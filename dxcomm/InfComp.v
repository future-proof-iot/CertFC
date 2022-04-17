From dx Require Import ResultMonad IR CoqIR IRtoC DXModule DumpAsC.

Class CType (coqType: Type) := mkCType {cType_i : Ctypes.type}.

Class CTypeL (coqType:Type) := mkCTypeL {
                                   symtyp : CompilableSymbolType
                                 }.

Definition mkCmpType (T: Type) (I : CType T) : CompilableType :=
  {|coqType := T ; cType := @cType_i T I|}.

Instance mkCP (T: Type) {CTA : CType T} : CTypeL T :=
  mkCTypeL T (MkCompilableSymbolType  nil (Some (mkCmpType T CTA))).

Instance mkArr (A : Type) {CTA : CType A} (R : Type) {CTL : CTypeL R} : CTypeL (A -> R) :=
  mkCTypeL (A -> R)
           (MkCompilableSymbolType
              ((mkCmpType A CTA) :: (compilableSymbolArgTypes (@symtyp _ CTL)))
              (compilableSymbolResType (@symtyp _ CTL))).

(* infer symbol type *)
Definition iST (T : Type) {CTL : CTypeL T} : CompilableSymbolType :=
  @symtyp _ CTL.


Ltac mkprimitive Op E :=
  let t := type of Op in
  let v := eval compute in (@iST t _) in
      exact (MkPrimitive v Op E).
