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

From Coq Require Import List ZArith.
From Coq Require String.

From compcert.cfrontend Require Csyntax Ctypes.
From compcert.common Require AST.

From dx Require Import ResultMonad ResultOps IR DXModule.

Definition CSymbol := AST.globdef (Ctypes.fundef Csyntax.function) Ctypes.type.

(* Conversion should fail when we try, for instance, to store tt in a variable
   (since it is supposed to be converted into void) *)

Inductive WhatNext : Type :=
| Store:  LocalId -> Ctypes.type -> WhatNext
| Drop:   WhatNext
| Return: WhatNext
.

Open Scope result_monad_scope.

Definition offsetVar (offset: Id) (x: Id) : Id := Pos.pred (Pos.add offset x).

Definition var (offset: Id) (x: Id) (t: Ctypes.type) : Csyntax.expr :=
  Csyntax.Evar (offsetVar offset x) t.

Definition offsetGlobals : GlobalId := 1%positive.

Definition assign (offsetLocals: LocalId) (x: LocalId) (t: Ctypes.type) (e: Csyntax.expr) :=
  Csyntax.Sdo (Csyntax.Eassign (var offsetLocals x t) e t).

Fixpoint convertExpression (offsetLocals: LocalId) (expr: Expression) : Result Csyntax.expr :=
  match expr with
  | eLocal t x => Ok (var offsetLocals x (cType t))
  | eGlobal (MkCompilableSymbolType nil (Some t)) x nil => Ok (var offsetGlobals x (cType t))
  | eGlobal _ _ _ => Err GlobalFunctionsNotImplemented
  | ePrim p args =>
      do args' <- sequence (map (convertExpression offsetLocals) args) ;
      primCImplem p args'
  end.

Definition returnCType (ty: CompilableSymbolType) : Ctypes.type :=
  match compilableSymbolResType ty with
  | None   => Ctypes.Tvoid
  | Some t => cType t
  end.

Definition callingConventionSymbol (ty: CompilableSymbolType) : AST.calling_convention :=
  AST.mkcallconv None false (match returnCType ty with
                             | (Ctypes.Tstruct _ _)
                             | (Ctypes.Tunion _ _) => true
                             | _                        => false
                             end).

Definition functionType (ty: CompilableSymbolType) : Ctypes.type :=
  let argTyps := map cType (compilableSymbolArgTypes ty) in
  let argTyps' := fold_right Ctypes.Tcons Ctypes.Tnil argTyps in
  Ctypes.Tfunction argTyps' (returnCType ty) (callingConventionSymbol ty).

Fixpoint zipWith3 {A B C D: Type} (f: A -> B -> C -> D) (xs: list A) (ys: list B) (zs: list C) : Result (list D) :=
  match (xs, ys, zs) with
  | (nil, nil, nil) => Ok nil
  | (x::xs', y::ys', z::zs') =>
     let u := f x y z in
     do us <- zipWith3 f xs' ys' zs' ;
     Ok (u::us)
  | _ => Err ZipMismatchedSizes
  end.

Fixpoint convertStatement (offsetLocals: LocalId) (wn: WhatNext) (stmt: Statement) : Result Csyntax.statement :=
  match stmt with
  | sPure None =>
      match wn with
      | Drop      => Ok Csyntax.Sskip
      | Return    => Ok (Csyntax.Sreturn None)
      | Store _ _ => Err StoreVoid
      end

  | sPure (Some e) =>
      do e' <- convertExpression offsetLocals e ;
      match wn with
      | Drop      => Ok (Csyntax.Sdo e')
      | Return    => Ok (Csyntax.Sreturn (Some e'))
      | Store x t => Ok (assign offsetLocals x t e')
      end

  | sBind tgt st1 st2 =>
      let wn' := match tgt with
                 | None        => Drop
                 | Some (x, t) => Store x (cType t)
                 end in
      do st1' <- convertStatement offsetLocals wn' st1 ;
      do st2' <- convertStatement offsetLocals wn  st2 ;
      Ok (Csyntax.Ssequence st1' st2')

  | sApply ty f args =>
      do args' <- mapM (convertExpression offsetLocals) args ;
      let args' := fold_right Csyntax.Econs Csyntax.Enil args' in
      let e := Csyntax.Ecall (Csyntax.Evar f (functionType ty)) args' (returnCType ty) in
      match wn with
      | Drop   => Ok (Csyntax.Sdo e)
      | Return => match compilableSymbolResType ty with
                  | None => Ok (Csyntax.Ssequence (Csyntax.Sdo e)
                                                  (Csyntax.Sreturn None))
                  | Some _ => Ok (Csyntax.Sreturn (Some e))
                  end
      | Store x t => Ok (assign offsetLocals x t e)
      end

  | sMatch ty e branches =>
      do e' <- convertExpression offsetLocals e ;
      do stmts' <- sequence (map (fun x => convertStatement offsetLocals wn (snd x)) branches) ;
      let convertBranch projs (brch: MatchBranchT) body :=
          let assignOne pbv s :=
            match pbv with
            | (_, (_, _, false)) => s
            | (p, (x, t, true))  => Csyntax.Ssequence (assign offsetLocals x (cType t) (p e')) s
            end in
          do xs <- combineM projs (fst brch) ;
          Ok (fold_right assignOne body xs)
      in
      do branches' <- zipWith3M convertBranch (matchProjectors ty) branches stmts' ;
      encodeMatch ty e' branches'
  end.

Fixpoint catOptions {A: Type} (xs: list (option A)) : list A :=
  match xs with
  | nil           =>      nil
  | None   :: xs' =>      catOptions xs'
  | Some x :: xs' => x :: catOptions xs'
  end.

Fixpoint extractLocals (offsetLocals: LocalId) (stmt: Statement) : list (Id * Ctypes.type) :=
  let go (xt : TypedLocalId) :=
    let (x, t) := xt in
    (offsetVar offsetLocals x, cType t)
  in
  let usedOrNot (xtu : MatchedLocalId) :=
    let (xt, u) := xtu in
    if u then Some xt else None
  in
  match stmt with
  | sPure _
  | sApply _ _ _ => nil
  | sBind None s1 s2 =>
      extractLocals offsetLocals s1 ++ extractLocals offsetLocals s2
  | sBind (Some xt) s1 s2 =>
      go xt :: extractLocals offsetLocals s1 ++ extractLocals offsetLocals s2
  | sMatch _ _ branches =>
      let subs := concat (map (fun b => extractLocals offsetLocals (snd b)) branches) in
      let vars := map go (catOptions (map usedOrNot (concat (map fst branches)))) in
      vars ++ subs
  end.

Fixpoint arguments (offsetLocals: LocalId) (current: Id) (args: list CompilableType) : list (Id * Ctypes.type) :=
  match args with
  | nil => nil
  | a :: args' => (offsetVar offsetLocals current, cType a) :: arguments offsetLocals (Pos.succ current) args'
  end.

Definition convertSymbol (offsetLocals: LocalId) (sym: IRSymbol) : Result (GlobalId * CSymbol) :=
  let id      := irSymbolId sym in
  let ty      := irSymbolType sym in
  let argTys  := compilableSymbolArgTypes ty in
  let argCTys := map cType argTys in
  let retCTy  := returnCType ty in
  let cc      := callingConventionSymbol ty in
  match sym with
  | MkIRSymbol _ _ _ true _ (Some body) _ =>
      do body' <- convertStatement offsetLocals Return body ;
      let args  := arguments offsetLocals 1%positive (compilableSymbolArgTypes ty) in
      let vars  := extractLocals offsetLocals body in
      let funct := Csyntax.mkfunction retCTy cc args vars body' in
      Ok (id, AST.Gfun (Ctypes.Internal funct))
  | MkIRSymbol _ _ _ true _ None _ =>
      let argSigTys := map Ctypes.typ_of_type argCTys in
      let retSigTy := Ctypes.rettype_of_type retCTy in
      let sig := AST.mksignature argSigTys retSigTy cc in

      (* TODO: Is it really an External we should build in that case? *)
      Ok (id,
          AST.Gfun (Ctypes.External
                      (AST.EF_external (irSymbolName sym) sig)
                      (fold_right Ctypes.Tcons Ctypes.Tnil argCTys)
                      retCTy
                      cc))
  | MkIRSymbol _ _ _ false _ (Some _) _ =>
      Err InitialisedGlobalConstantCannotBeConverted
  | MkIRSymbol _ _ _ false _ None _ =>
      Ok (id, AST.Gvar (AST.mkglobvar (returnCType ty) nil true false))
  end.

Fixpoint internConvertSymbols (offsetLocals: LocalId) (syms: list IRSymbol) : Result (list (GlobalId * CSymbol)) :=
  match syms with
  | nil => Ok nil
  | (sym :: syms') =>
    do cSym <- convertSymbol offsetLocals sym ;
    let offsetLocals' :=
      match length (irSymbolLocals sym) with
      | O => offsetLocals
      | l => Pos.add (Pos.of_nat l) offsetLocals
      end in
    do cSyms <- internConvertSymbols offsetLocals' syms' ;
    Ok (cSym :: cSyms)
  end.

Definition convertSymbols (syms: list IRSymbol) : Result (list (GlobalId * CSymbol)) :=
  let offsetLocals := Pos.of_succ_nat (length syms) in
  internConvertSymbols offsetLocals syms.

Fixpoint zipWithCount {A: Type} (count: Id) (xs: list A) : list (Id * A) :=
  match xs with
  | nil => nil
  | (x :: xs') => (count, x) :: zipWithCount (Pos.succ count) xs'
  end.

Definition makeDXModule (syms: list IRSymbol) (computeMain: list Id -> GlobalId) : Result dxModule :=
  do cSyms <- convertSymbols syms ;
  let globs := map (fun s => (irSymbolId s, irSymbolName s)) syms in
  let initLocs := Pos.of_succ_nat (length syms) in
  let locs := zipWithCount initLocs (flat_map irSymbolLocals syms) in
  let pubs := map irSymbolId syms in
  let names := app globs locs in
  let ids := map fst names in
  do prog <- fromCompCertRes (Ctypes.make_program nil cSyms pubs (computeMain ids)) ;
  Ok (MkDXModule prog names).

Definition makeDXModuleWithMain (syms: list IRSymbol) (main: GlobalId) : Result dxModule :=
  makeDXModule syms (fun _ => main).

Definition makeDXModuleWithoutMain (syms: list IRSymbol) : Result dxModule :=
  let max_all xs := Pos.succ (List.fold_left Pos.max xs 1%positive) in
  makeDXModule syms max_all.
