(** Structure of soundness proofs for dx generated programs *)
Require Import List.
Require Import Coq.Program.Equality.
From dx Require Import IR.
From compcert Require Import Values.
From compcert Require Import SimplExpr.
From compcert Require Import Clight.

(** dx requires primitives.
    For each primitive,
    we have soundness theorem relating the Coq function and the primitive expres    sion. The primitive declaration is untyped.*)

Fixpoint arrow_type (l : list Type) (r : Type) :=
  match l with
  |  nil => r
  | cons e l => e -> (arrow_type l r)
  end.

Lemma nil_not_cons : forall {A: Type} (e:A) (l:list A),
    nil = e :: l -> False.
Proof.
  intros. discriminate.
Defined.

Lemma car_eq : forall {A: Type} (e1 e2: A) l1 l2,
                      e1 :: l1 = e2 :: l2 -> e1 = e2.
Proof.
  intros. congruence.
Defined.

Lemma cdr_eq : forall {A: Type} (e1 e2: A) l1 l2,
                      e1 :: l1 = e2 :: l2 -> l1 = l2.
Proof.
  intros. congruence.
Defined.


Module DList.
  Section A.
    Context {A: Type}.
    Variable F:  A -> Type.

    Inductive t : list A -> Type :=
    | DNil : t nil
    | DCons : forall {e:A} (v: F e) {l:list A} (dl:t l),
        t (e::l).

    Definition car {e: A} {l: list A} (dl : t  (e::l)) : F e.
      refine(
      match dl in (t l0) return match l0 with nil => nil = e::l  -> False | e :: l => F e end with
      | DNil => _
      | DCons e0 v l0 _ => _
      end).
      apply nil_not_cons.
      apply v.
    Defined.

    Definition cdr {e: A} {l: list A} (dl : t  (e::l)) : t l.
      refine (match dl in (t l0) return match l0 with nil => (nil = e :: l -> False) | e :: l => t l end with
      | DNil => _
      | DCons e0 _ l0 dl0 => dl0
      end).
      apply nil_not_cons.
    Defined.

    Fixpoint map_id (l: list A) (dl : t l) : t l.
      destruct l.
      - apply DNil.
      - destruct dl.
        exact DNil.
        apply (DCons v dl).
    Defined.


    Lemma Dnil_nil  : forall (dl: t nil), dl = DNil.
    Proof.
      intro.
      dependent destruction dl.
      reflexivity.
    Qed.


    Lemma map_id_id : forall l (dl:t l),
        dl = map_id l dl.
    Proof.
      induction l.
      simpl. apply Dnil_nil.
      simpl. intros. destruct dl; reflexivity.
    Qed.

    Lemma car_cdr : forall e l (dl : t (e::l)),
        dl = DCons (car dl) (cdr dl).
    Proof.
      dependent destruction dl.
      reflexivity.
    Qed.

  End A.

  Section FORALL2.
    Context {A: Type}.
    Context {F : A -> Type}.
    Context {G : A -> Type}.
    Variable R : forall (a:A), F a -> G a -> Prop.

    Fixpoint Forall2 {l:list A} (dl1 : t F l) :  forall (dl2 : t G l) , Prop:=
        match dl1 in (t _ l0) return (t G l0 -> Prop) with
        | @DNil _ _ => fun _  => True
        | @DCons _ _ e v l0 dl2 =>
          fun dl3  =>
            R e v (car G dl3) /\ Forall2  dl2 (cdr G dl3)
        end.

  End FORALL2.

  Section MAP.
    Context {A: Type}.
    Context {F : A -> Type}.
    Context {G : A -> Type}.
    Variable M : forall (a:A), F a -> G a.

    Fixpoint Map {l:list A} (dl1 : t F l) : t G l :=
      match dl1 in (t _ l0) return t G l0 with
      | @DNil _ _ => DNil G
      | @DCons _ _ e v l0 dl2 =>
        DCons G  (M e v )  (Map dl2)
      end.
  End MAP.

  Section MAPT.
    Context {A B: Type}.
    Context {F : A -> Type}.
    Context {G : B -> Type}.
    Context (Ml : A -> B).
    Variable M : forall (a:A), F a -> G (Ml a).

    Fixpoint MapT {l:list A} (dl1 : t F l) : t G (map Ml l):=
      match dl1 in (t _ l0) return (t G (map Ml l0)) with
      | @DNil _ _ => DNil G
      | @DCons _ _ e v l0 dl2 =>
        DCons G  (M e v)
               (MapT  dl2)
      end.
  End MAPT.



  Section MAP2.
    Context {A: Type}.
    Variable F : A -> Type.
    Variable G : A -> Type.
    Variable H : A -> Type.
    Variable M : forall (a:A), F a -> G a -> H a.

    Fixpoint Map2 (l:list A) (dl1 : t F l) : t G l -> t H l:=
      match dl1 in (t _ l0) return (t G l0 -> t H l0) with
      | @DNil _ _ => fun _  => DNil H
      | @DCons _ _ e v l0 dl2 =>
      fun dl3  =>
        DCons H  (M e v (car G dl3))  (Map2 l0 dl2 (cdr G dl3))
      end.

  End MAP2.

  Section LIST.

    Context {A B: Type}.
    Context {F : A -> Type}.
    Variable G : forall (x:A), F x -> B.

    Fixpoint list {l:list A} (dl: t F l) : list B :=
      match dl with
      | DNil => nil
      | DCons e v l dl' => G e v :: (list  dl')
      end.

  End LIST.

  End DList.

Arguments  DList.DCons {A} {F} {e} v {l} dl.


Module MatchCType.
  Section S.
    Variables T : CompilableType.

    Record t  : Type := mk
      {
      rel : coqType T -> val -> Prop
      }.

  End S.


  Definition from_option (T : option CompilableType) :=
    match T with
    | None => unit
    | Some C => t C
    end.
End MatchCType.

Definition args (P: Primitive) :=
  (compilableSymbolArgTypes (primType P)).

Definition ret (P : Primitive) :=  coqType' (compilableSymbolResType (primType P)).

Fixpoint app {l : list Type} {r: Type} (f : arrow_type l r) (a : DList.t (fun x => x) l) : r:=
  match a in (DList.t _ l0) return (arrow_type l0 r -> r) with
  | @DList.DNil _ _ => fun f0 : arrow_type nil r => f0
  | @DList.DCons _ _ e v _ a' =>
      fun f => app  (f v) a'
  end f.

Lemma arrow_type_encode : forall P,
    (arrow_type (List.map coqType (args P)) (ret P)) = (encodeCompilableSymbolType None (primType P)).
Proof.
  unfold args,ret.
  destruct P. simpl.
  unfold encodeCompilableSymbolType.
  destruct primType.
  simpl. clear.
  induction compilableSymbolArgTypes.
  - simpl. reflexivity.
  - simpl.
    rewrite IHcompilableSymbolArgTypes.
    reflexivity.
Defined.

Definition uniq {A: Type} (R : A -> Prop) (a : A)  :=
  R a /\ forall a', R a' -> a = a'.

Definition is_transl_expr (e: Csyntax.expr) (e': Clight.expr) :=
  forall g LE, transl_expr For_val e g = Res (nil,e') g LE.

Inductive one_eval_expr (e:Clight.expr) (v:val) : Prop :=
| EvalExpr_Intro  :
    forall ge ev te m,
        eval_expr ge ev te m e v -> one_eval_expr e v.

Definition eval_Csem  (e: Csyntax.expr) (v: val) : Prop:=
  exists e', uniq (is_transl_expr e) e'  /\
             uniq (one_eval_expr e') v.

Definition get_typed_args (l: list CompilableType) (la : DList.t (fun x => coqType x * val) l) : list Csyntax.expr :=
  DList.list
    (fun (x : CompilableType)
         (tval : coqType x * val) =>
       Csyntax.Eval (snd tval) (cType x)) la.

Definition correctPrimitive (P: Primitive)
           (a : DList.t (fun x => coqType x -> val -> Prop) (args P))
           (r : ret P -> val -> Prop) : Prop :=
      forall (la: DList.t (fun x => coqType x * val) (args P)),
        DList.Forall2 (fun (x : CompilableType) (R : coqType x -> val -> Prop) v => R (fst v) (snd v)) a la ->
        let a  := (DList.MapT (fun x => coqType x) (fun (x:CompilableType) v => fst v) la) in
        match primCImplem P (get_typed_args (args P) la) with
        | ResultMonad.Err _ => True
        | ResultMonad.Ok  e => forall v, eval_Csem  e v ->
                                         r (app (r:=ret P) (eq_rect_r (fun T : Type => T) (primCoqImplem P) (arrow_type_encode P)) a) v
  end
  .

Require Import DxIntegers.
From compcert Require Import Integers.

Definition int64_correct (x : int64) (v:val) := Vlong x = v.

Definition args_binary_int64_correct : DList.t (fun x => coqType x -> val -> Prop) (compilableSymbolArgTypes int64Toint64Toint64SymbolType) :=
  @DList.DCons _ _ int64CompilableType int64_correct _
               (@DList.DCons _  _
                             int64CompilableType int64_correct _
                             (@DList.DNil CompilableType _)).

Ltac car_cdr :=
  repeat match goal with
  | DL : DList.t _ (?E :: ?L) |- _ =>
    rewrite (@DList.car_cdr _ _ E L DL) in *;
    let c := fresh "c" in
    let d := fresh "d" in
    set (c:= @DList.car _ _ _ _ DL) in *;
    set (d:= @DList.cdr _ _ _ _ DL)  in *;
    clearbody c; clearbody d ; clear DL
  | DL : DList.t _ nil |- _ =>
    rewrite (DList.Dnil_nil _ DL) in *; clear DL
         end.


Lemma genv_ex : genv.
Proof.
  apply Build_genv.
  Print Globalenvs.Genv.mkgenv.
  eapply (@Globalenvs.Genv.mkgenv _ _ nil (Maps.PTree.empty block)
                                 (Maps.PTree.empty _)
                                 BinPos.xH
         ).
  - intros.
    rewrite Maps.PTree.gempty in H. discriminate.
  - intros.
    rewrite Maps.PTree.gempty in H. discriminate.
  - intros.
    rewrite Maps.PTree.gempty in H. discriminate.
  - apply Maps.PTree.empty.
Qed.





Ltac correctPrimitive_Op OP :=
  unfold correctPrimitive;
  cbn;
  intros;
  car_cdr;
  simpl in *;
  (* Explain that the translation of the Csyntax espression
     is a Clight expression *)
  intros v EVAL;
  unfold eval_Csem in EVAL;
  destruct EVAL as [e' [Htr Heval]];
  match goal with
  | H : _ (fst ?A1) _ /\
        _ (fst ?A2) (snd _) /\ True |- _ =>
    let HA1 := fresh "HA1" in
    let HA2 := fresh "HA2" in
    destruct H as [HA1 [HA2 _]];
    assert (e' =
            (Ebinop OP (Econst_long (fst A1) CoqIntegers.C_U64)
                    (Econst_long (fst A2) CoqIntegers.C_U64) CoqIntegers.C_U64))
           by (
    unfold uniq in Htr;
    destruct Htr as [Htr1  Htr2];
    apply Htr2;
    unfold is_transl_expr;
    intros;
    rewrite <- HA1;
    rewrite <- HA2;
    simpl;
    unfold bind2,bind, SimplExpr.ret;
    simpl; f_equal;
    apply Axioms.proof_irr
             );
    subst; clear Htr;
  unfold uniq in Heval;
  destruct Heval as [Heval1 Heval2];
  symmetry;
  apply Heval2;
  apply (EvalExpr_Intro _ _ genv_ex (Maps.PTree.empty _) (Maps.PTree.empty _)
                        Memory.Mem.empty);
  repeat econstructor
  end.


Lemma  Const_int64_add_correct : correctPrimitive
                                   Const_int64_add args_binary_int64_correct int64_correct.
Proof.
  correctPrimitive_Op Cop.Oadd.
Qed.

Lemma  Const_int64_sub_correct : correctPrimitive
                                   Const_int64_sub args_binary_int64_correct int64_correct.
Proof.
  correctPrimitive_Op Cop.Osub.
Qed.

(*

Lemma  Const_int64_mul_correct : correctPrimitive
                                   Const_int64_mul args_binary_int64_correct int64_correct.
Proof.
  correctPrimitive_Op Cop.Omul.
Qed.*)

Require Import DxMonad.
From compcert Require Import Smallstep.





Section S.
  (** The program contains our function of interest [fn] *)
  Variables p : Clight.program.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Variable Args : list CompilableType.
  Variable Res : CompilableType.

  (* [f] is a Coq Monadic function with the right type *)
  Variable f : encodeCompilableSymbolType (Some M) (MkCompilableSymbolType Args (Some Res)).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn: Clight.function.

  (* [match_mem] related the Coq monadic state and the C memory *)
  Variable match_mem : stateM -> genv -> Memory.Mem.mem -> Prop.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Variable match_arg_list : DList.t (fun x => coqType x -> val -> Prop) Args.

  (* [match_res] relates the Coq result and the C result *)
  Variable match_res : coqType Res -> val -> Prop.

  Lemma arrow_type_encode' : (arrow_type (List.map coqType Args) (M (coqType Res)) = encodeCompilableSymbolType (Some M) (MkCompilableSymbolType Args (Some Res))).
  Proof.
    unfold encodeCompilableSymbolType.
    simpl. clear.
    induction Args.
    - simpl. reflexivity.
    - simpl.
      rewrite IHl.
      reflexivity.
  Defined.

  Record correct_function  :=
    mk_correct_function
      {
        (** syntactic checks *)
        fn_return_ok : fn_return fn = cType Res;
        fn_callconv_ok : fn_callconv fn = AST.mkcallconv None false false;
        fn_params_ok   : List.map snd (fn_params fn) =
                         List.map cType Args;
        fn_temps_ok       : fn_temps fn = nil;
        (** semantic check *)
        fn_eval_ok : forall
            (* la is a list of pairs of arguments both Coq and C *)
            (la: DList.t (fun x => coqType x * val) Args),
            (* they satisfy the invariants *)
            DList.Forall2 (fun (x : CompilableType) (R : coqType x -> val -> Prop) v => R (fst v) (snd v)) match_arg_list la ->
            (* The C arguments are the second elements of the list la *)
            let lval :=   DList.list  (fun (x : CompilableType) (tval : coqType x * val) => snd tval) la in
            (* The Coq arguments are the first elements of the list *)
            let a  := DList.MapT (fun x => coqType x) (fun (x:CompilableType) v => fst v) la in
            forall k st m,
              (* The input state are in relation *)
              match_mem st (globalenv (semantics1 p)) m ->
              (* let fa be the Coq result *)
              let fa := app (r:=M (coqType Res)) (eq_rect_r (fun T : Type => T) f (arrow_type_encode')) a st in
              match fa with
              | None => False (* This is not possible because of the invariant *)
              | Some (v',st') =>
                (* We prove that we can reach a return state *)
                exists v m' t,
                Star (Clight.semantics1 p) (Callstate  (Ctypes.Internal fn)
                                                 lval  k m) t
                     (Returnstate v k m') /\
                (* The return memory matches the return state *)
                match_mem st' (globalenv (semantics1 p)) m'
                /\ (* The return value matches *)
                match_res v' v
              end
      }.

End S.
