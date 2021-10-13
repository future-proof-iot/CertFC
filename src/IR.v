(**************************************************************************)
(*  This file is part of dx, a tool to derive C from monadic Gallina.     *)
(*                                                                        *)
(*  Copyright (C) 2021 Université de Lille & CNRS                         *)
(*                                                                        *)
(*  This program is free software; you can redistribute it and/or modify  *)
(*  it under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation; either version 2 of the License, or     *)
(*  (at your option) any later version.                                   *)
(*                                                                        *)
(*  This program is distributed in the hope that it will be useful,       *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License for more details.                          *)
(**************************************************************************)

From Coq Require Import BinNums List String Nat.
From compcert.cfrontend Require Csyntax Ctypes.

From dx Require Import ResultMonad.

Open Scope string.
Close Scope nat_scope.

Definition Monad := Type -> Type.

(* Types for identifiers *)
(* These are chosen to match the choice in CompCert. *)
(* GlobalId must be chosen to be globally unique. *)
(* LocalId must be chosen to be locally (inside a function, corresponding to a
   [Definition]) unique. *)
(* These will be mapped into one big set of identifiers when converting to C,
   they don't need to be globally unique at the IR stage *)
Definition Id := positive.
Definition LocalId  := Id.
Definition GlobalId := Id.

(* Types that can be encoded *)
(* Note that unit is to be treated as a special case: since we do not want to
   manipulate values of unit type at runtime in C, the intermediate language
   handles them explicitly; this stems from the fact that no CompCert value
   could correspond to () *)
Record CompilableType := MkCompilableType
  { coqType: Type
  ; cType:   Ctypes.type
  (* TODO: Add properties that should be verified for this encoding to be
     valid, such as injectivity *)
  }.

Definition TypedLocalId := (LocalId * CompilableType).
Definition OptTypedLocalId := option TypedLocalId.
(* To describe bindings in a [match]: we want a LocalId and a CompilableType
   even when the bound name is not used in the branch body *)
Definition UsedBinding := bool.
Definition MatchedLocalId := (TypedLocalId * UsedBinding).

Record CompilableSymbolType := MkCompilableSymbolType
  { compilableSymbolArgTypes: list CompilableType
  ; compilableSymbolResType:  option CompilableType
  }.

Definition coqType' (optTyp : option CompilableType) :=
  match optTyp with
  | None     => unit
  | Some typ => coqType typ
  end.

Fixpoint encodeCompilableSymbolType' (m: option Monad) (argTypes: list CompilableType) (resType: option CompilableType): Type :=
  match argTypes with
  | nil               => match m with
                         | None    => coqType' resType
                         | Some m' => m' (coqType' resType)
                         end
  | cons a0 argTypes' => coqType a0 -> encodeCompilableSymbolType' m argTypes' resType
  end.

Definition encodeCompilableSymbolType (m: option Monad) (funType: CompilableSymbolType): Type :=
  encodeCompilableSymbolType' m (compilableSymbolArgTypes funType) (compilableSymbolResType funType).

Record MatchableType := MkMatchableType
  { compilableType :> CompilableType
  ; encodeMatch:      Csyntax.expr -> list Csyntax.statement -> Result Csyntax.statement
  (* [encodeMatch x' bodys'] must be the encoding of [match x with ... end]
     where [x'] is the encoding of [x] with one [body] per constructor;
     for [nat], this could be
     [fun x bs => match bs with [caseO; caseN] => |if (x == 0) caseO else caseN|]
     where [|expr|] stands for the Csyntax.statement for the C expression
     [expr] *)
  ; matchProjectors:  list (list (Csyntax.expr -> Csyntax.expr))
  (* for each constructor and for each argument [matchProjectors];
     for [nat], this could be [[]; [fun n => |n - 1|]] *)
  ; matchInterpTypes : list (list CompilableType)
  ; matchInterp : forall (m : Monad) (A : Type), coqType compilableType ->
    fold_right (fun X Y => X -> Y) (m A)
      (map (fold_right (fun X Y => X -> Y) (m A)) (map (map coqType) matchInterpTypes))
  }.

(* Primitives *)
(* We call _primitives_ the Coq functions that have a specific translation into
   C. This is specifically suited for C operators, so that the boolean equality
   in Coq can be translated into the actual [==] when applicable (for types where
   [==] is indeed the proper equality test, obviously). *)
(* It would obviously not make sense to use this to compile to stateful
   operators, such as ++ *)
(* Primitives are also designed to cover use cases such as constants. *)
Record Primitive := MkPrimitive
  { primType:      CompilableSymbolType
  ; primCoqImplem: encodeCompilableSymbolType None primType
  ; primCImplem:   list Csyntax.expr -> Result Csyntax.expr
  (* TODO: Add properties here? Or they should appear only for instances and
     the definition of semantics for each of the primitives? *)
  }.

Notation constant TY CoqI CI :=
  (MkPrimitive TY CoqI (fun es => match es with
                                  | nil => Ok CI
                                  | _   => Err PrimitiveEncodingFailed
                                  end))
  (only parsing).

(* **Pure** expressions *)
(* A local identifier can only be of "base" type, which means it cannot be a
   function *)
(* A global identifier can reference either a constant or a function; if it is
   a function, it is applied to a list of arguments; if the list is empty, it
   must be a function.
   Note that, in C, we could have a function with no argument and we have no
   way to represent here a function with no argument. But since our source is
   Gallina, we know that we will not deal with a pure function with no
   argument. Also note that this does not include stateful action (of monadic
   type) which are not expressions. *)
(* TODO: Is it too redundant to explicitly give the CompilableType on eLocal
   (it should be associated to that LocalId in the local environment) and
   eGlobal? (it should be the return type associated to that GlobalId in the
   global environment);
   in any case it is always explicitly given in Primitive *)
Inductive Expression : Type :=
| eLocal:  CompilableType -> LocalId -> Expression
| eGlobal: CompilableSymbolType -> GlobalId -> list Expression -> Expression
| ePrim:   Primitive -> list Expression -> Expression
.
(* Add constructors if ePrim does not cover the case *)
(* Define a specialised Expressions for list of expressions as a mutual
   inductive? This gets a smarter induction principle *)

(* Stateful actions *)
Inductive Statement : Type :=
| sPure:  option Expression -> Statement
  (* option Expression: None encodes a "pure tt" *)
| sBind:  OptTypedLocalId -> Statement -> Statement -> Statement
| sApply: CompilableSymbolType -> GlobalId -> list Expression -> Statement
| sMatch: MatchableType -> Expression -> list (list MatchedLocalId * Statement) -> Statement
.

Definition MatchBranchT := list MatchedLocalId * Statement.

(* TODO: should we add a LocalId in sMatch, in which to store the value of the
   Expression? should this be done rather in further transformation? *)
(* TODO: We might define some well-formedness property to check a [Statement] or
   [Expression] makes sense. For instance in [sMatch typ exp cases], [exp] must
   indeed have type [typ], the number of [cases] must match the number of
   constructors of [typ], etc.*)

(* TODO: is it possible to convert to C every [Statement]? In particular, can
   we convert the [Statement] corresponding to:

   <<
     x <- if someCondition
             then do ... ; sPure something
             else do ... ; sPure someother
     ...
   >>

   into (ideally):

   <<
     if (someCondition') {
       ...
       x = something';
     } else {
       ...
       x = someother';
     }
   >>
*)

(* This way to represent derivable symbols has only one way to represent
   non-monadic values with no argument while this could either be a variable or
   a (pure) function with no argument in C world *)
Record DerivableSymbol (m: Monad) := MkDerivableSymbol
  { derivableSymbolName:    string
  ; derivableSymbolMonadic: bool
  ; derivableSymbolType:    CompilableSymbolType
  ; derivableSymbolContent: encodeCompilableSymbolType (if derivableSymbolMonadic then Some m else None) derivableSymbolType
  ; derivableSymbolExtern:  bool
    (* ^ whether the DerivableSymbol should be used only to define an
         "extern", that is its content should not be converted
         Note that this could have been stated also using an option for
         Content: an extra bool is used so that Elpi code has access to the
         actual source symbol and can use it to identify it in the code that
         uses it *)
  }.

Inductive FixOrNofix : Type :=
| Fix: nat -> FixOrNofix
| Nofix: FixOrNofix
.

Record IRSymbol := MkIRSymbol
  { irSymbolName:    string
  ; irSymbolId:      GlobalId
  ; irSymbolLocals:  list string
  ; irSymbolMonadic: bool
  ; irSymbolType:    CompilableSymbolType
  ; irSymbolContent: option (if irSymbolMonadic then Statement else Expression)
  ; irSymbolFix:     FixOrNofix
  }.
