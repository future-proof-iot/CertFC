(** Structure of soundness proofs for dx generated programs *)
Require Import List.
Require Import Coq.Program.Equality.
From dx Require Import IR.
From compcert Require Import Coqlib Values.
From compcert Require Import SimplExpr.
From compcert Require Import Clight.

From dx.tests Require Import DxIntegers DxMonad.
From compcert Require Import Integers.
From compcert Require Import Smallstep.
Require Import clight_exec.
Open Scope type_scope.


Definition without_mem {A B : Type} (P : A -> B -> Prop)
           (a : A) (b: B) (m: Memory.Mem.mem) :=
  P a b.


Definition match_bool (b:bool) (v:val) :=
  v = Vint (if b then Integers.Int.one else Integers.Int.zero).


(** dx requires primitives.
    For each primitive,
    we have soundness theorem relating the Coq function and the primitive expres    sion. The primitive declaration is untyped.*)

Fixpoint arrow_type (l : list Type) (r : Type) :=
  match l with
  |  nil => r
  | cons e l => e -> (arrow_type l r)
  end.

Fixpoint arrow_n (n:nat) (e : Type) (r: Type) :=
  match n with
  |  O => r
  | S n => e -> (arrow_n n e r)
  end.

Fixpoint rep {A: Type} (n:nat) (e: A) :=
  match n with
  | O => nil
  | S n => e :: (rep n e)
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


  Section FORALL.
    Context {A: Type}.
    Context {F : A -> Type}.
    Variable R : forall (a:A), F a -> Prop.

    Fixpoint Forall {l:list A} (dl1 : t F l) : Prop:=
        match dl1  with
        | @DNil _ _ => True
        | @DCons _ _ e v l0 dl2 =>
            R e v  /\ Forall  dl2
        end.
  End FORALL.

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

    Lemma Forall2_rew : forall (e:A) (e1:F e) (e2 : G e)
                               l (dl1 : t F l) (dl2 : t G l),
        @Forall2 (e::l) (@DCons _ _ e e1 l dl1) (@DCons _ _ e e2 l dl2) =
          (R e e1 e2 /\ @Forall2 l dl1 dl2).
    Proof.
      reflexivity.
    Qed.

    
  End FORALL2.


  Section ZIP.
    Context {A : Type}.
    Context {F : A -> Type}.
    Context {G : A -> Type}.

    Fixpoint zip {l:list A} (dl1 : t F l): forall (dl2 : t G l) , t (fun x => F x * G x)%type l:=
  match dl1 in (t _ l0) return (t G l0 -> t (fun x : A => F x * G x)%type l0) with
  | @DNil _ _ => fun _  => DNil (fun x : A => F x * G x)%type
  | @DCons _ _ e v l0 dl2 =>
      fun dl3 : t G (e :: l0) =>
        DCons (fun x : A => F x * G x)%type (v, car G dl3) (zip dl2 (cdr G dl3))
  end.

    End ZIP.


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
    Context {F : A -> Type}.
    Context {G : A -> Type}.
    Context {H : A -> Type}.
    Variable M : forall (a:A), F a -> G a -> H a.

    Fixpoint map2 {l:list A} (dl1 : t F l) : t G l -> t H l:=
      match dl1 in (t _ l0) return (t G l0 -> t H l0) with
      | @DNil _ _ => fun _  => DNil H
      | @DCons _ _ e v l0 dl2 =>
      fun dl3  =>
        DCons H  (M e v (car G dl3))  (map2  dl2 (cdr G dl3))
      end.

  End MAP2.

  Section LIST.

    Context {A B: Type}.
    Context {F : A -> Type}.
    Variable G : forall (x:A), F x -> B.

    Fixpoint to_list {l:list A} (dl: t F l) : list B :=
      match dl with
      | DNil => nil
      | DCons e v l dl' => G e v :: (to_list  dl')
      end.

    Lemma length_to_list : forall l (dl: t F l),
        length (to_list dl) = length l.
    Proof.
      induction dl;simpl;auto.
    Qed.

  End LIST.

  Section OFLIST.

    Context {A B: Type}.

    Fixpoint of_list (l:list A) : t (fun (x:A) => A) l:=
      match l with
      | nil => DNil _
      | e::l => DCons _ e  (of_list l)
      end.

    Lemma length_nil_cons : forall {E: Type} (e: E) (l:list E) (r:Type),
        List.length (A:= E) nil = List.length (e :: l) -> r.
    Proof.
      discriminate.
    Qed.

    Lemma length_cons_cons : forall [E1 E2: Type] [e1:E1] [e2: E2] [l1:list E1] [l2: list E2],
        List.length (e1 :: l1) = List.length (e2 :: l2) ->
        Datatypes.length l1 = Datatypes.length l2.
    Proof.
      simpl. congruence.
    Qed.

    Fixpoint of_list_sl (l: list A)  (l' : list B) : forall (LEN : List.length l = List.length l'), t (fun (x:B) => A) l':=
      match l as l0 return (Datatypes.length l0 = Datatypes.length l' -> t (fun _ : B => A) l') with
      | nil =>
          match l'  with
          | nil => fun _  => DNil (fun _ : B => A)
          | b :: l'0 => @length_nil_cons B _ _ _
          end
      | a :: l0 =>
          match l'  with
          | nil => fun _ => DNil (fun _ : B => A)
          | b :: l'0 =>
              fun LEN1  => DCons (fun _ : B => A) a (of_list_sl l0 l'0 (length_cons_cons LEN1))
          end
      end.

    Lemma to_list_of_list_sl  : forall (l: list A) (l': list B) (LEN : List.length l = List.length l'),
        l = to_list (fun (_:B) (x:A) => x) (of_list_sl l l' LEN).
    Proof.
      induction l.
      - simpl. destruct l'.
        + simpl. reflexivity.
        + simpl. discriminate.
      - simpl.
        destruct l'.
        discriminate.
        simpl. intros.
        f_equal. apply IHl.
    Qed.

  End OFLIST.

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

Fixpoint app {l : list Type} {r: Type} (f : arrow_type l r) (a : DList.t (fun x => x) l) : r:=
  match a in (DList.t _ l0) return (arrow_type l0 r -> r) with
  | @DList.DNil _ _ => fun f0 : arrow_type nil r => f0
  | @DList.DCons _ _ e v _ a' =>
      fun f => app  (f v) a'
  end f.

Fixpoint app_n {e: Type} {r:Type} (d:e) (n: nat) (f: arrow_n n e r) (l:list e) {struct n} : r:=
  match n as n0 return (arrow_n n0 e r -> r) with
  | O => fun f0  => f0
  | S n0 =>
      fun f0  =>
      match l return r with
      | nil => @app_n e r d n0 (f0 d) (@nil e)
      | cons e0 l0 => @app_n e r d n0 (f0 e0) l0
      end
  end f.


Ltac car_cdr :=
  repeat match goal with
  | DL : @DList.t ?T _ (?E :: ?L) |- _ =>
    rewrite (@DList.car_cdr T _ E L DL) in *;
    let c := fresh "c" in
    let d := fresh "d" in
    set (c:= @DList.car _ _ _ _ DL) in *;
    set (d:= @DList.cdr _ _ _ _ DL)  in *;
    clearbody c; clearbody d ; clear DL
  | DL : DList.t _ nil |- _ =>
    rewrite (DList.Dnil_nil _ DL) in *; clear DL
         end.


Definition unmodifies_effect (l : list block) (m m' : Memory.Mem.mem) : Prop :=
  forall b, ~ In b l -> forall chk o,
      Memory.Mem.load chk m b o =
        Memory.Mem.load chk m' b o.

Lemma unmodifies_effect_trans : forall l m1 m2 m3,
    unmodifies_effect l m1 m2 ->
    unmodifies_effect l m2 m3 ->
    unmodifies_effect l m1 m3.
Proof.
  unfold unmodifies_effect.
  intros.
  rewrite H by auto.
  rewrite H0 by auto.
  reflexivity.
Qed.

Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Variable args : list Type.
  Variable res : Type.

  (* [f] is a Coq Monadic function with the right type *)
  Variable f : arrow_type args (M res).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn: Clight.function.

  Variable modifies : list block. (* of the C code *)

(*  Variable match_mem : stateM -> val -> Memory.Mem.mem -> Prop.*)

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Variable match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) (stateM ::args).

  (* [match_res] relates the Coq result and the C result *)
  Variable match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop.

  Record correct_function3  :=
    mk_correct_function3
      {
        fn_eval_ok3 : forall
            (a: DList.t (fun x => x) args) (st:stateM),
          match app (r:=M res) f  a st with
          | None => True
          | Some (v',st') =>
              (* We prove that we can reach a return state *)
              forall (lval: DList.t (fun _ => val) (stateM ::args))
                     k m,
                is_call_cont k ->
                (* they satisfy the invariants *)
                DList.Forall2 (fun (a:Type) (R: a -> val -> stateM -> Memory.Mem.mem ->Prop) (X:a * val) => R (fst X) (snd X) st m)
                              match_arg_list (DList.zip  (DList.DCons st a) lval) ->
                (* We prove that we can reach a return state *)
                Forall2 (fun v t => Cop.val_casted v (snd t)) (DList.to_list (fun _ v => v) lval) (fn_params fn) ->

                exists v m' t,
                Star (Clight.semantics2 p) (Callstate  (Ctypes.Internal fn)
                                                       (DList.to_list (fun x v => v) lval)  k m) t
                     (Returnstate v (call_cont k) m') /\
                  (* The return memory matches the return state *)
                  match_res  v' v st' m' /\ Cop.val_casted v (fn_return fn) /\
                  unmodifies_effect modifies m m'
              end
      }.

End S.





Definition apply_cont (k:cont) : option (statement * cont) :=
  match k with
  | Kstop => None
  | Kseq s k => Some(s,k)
  | Kloop1 s1 s2 k => Some (s2, Kloop2 s1 s2 k)
  | Kloop2 s1 s2 k => Some (Sloop s1 s2, k)
  | Kswitch k      => Some (Sskip,k)
  | Kcall _ _ _  _ _ => None
  end.


Section S.
  Variable p : Clight.program.

  Variable res : Type.
  Variable f : M res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.
  Variable stm: Clight.statement.

  Variable modifies : list block.

  Variable match_arg : stateM -> temp_env -> Memory.Mem.mem -> Prop.

  Variable match_res : res -> stateM  -> temp_env -> Memory.Mem.mem -> Prop.

  Definition correct_statement (st : stateM) (le:temp_env) (m:Memory.Mem.mem) :=
    match_arg st le m ->
    match f  st with
    | None => True
    | Some (v',st') =>
        forall s' k k',
          apply_cont k = Some (s',k') ->
          exists le' m' t,
                  Star (Clight.semantics2 p) (State fn stm k empty_env le m) t
                       (State  fn s' k' empty_env le' m') /\
                    (* The return memory matches the return state *)
                    match_res v' st' le' m' /\ unmodifies_effect modifies m m'
    end.

End S.


Definition match_elt (st: stateM) (m : Memory.Mem.mem) (le : temp_env)
           (r : (AST.ident * Ctypes.type) * (val -> stateM -> Memory.Mem.mem -> Prop)) :=
  match Maps.PTree.get (fst (fst r)) le with
  | None => False
  | Some v => (snd r) v st m /\ Cop.val_casted v (snd (fst r))
  end.

Definition match_temp_env (dl : list ((AST.ident * Ctypes.type) * (val -> stateM -> Memory.Mem.mem -> Prop)))
           (le:temp_env) (st: stateM) (m : Memory.Mem.mem)
            : Prop :=
  Forall (match_elt st m le) dl.

Definition pre
           (var_inv : list (positive * Ctypes.type * (val -> stateM -> Memory.Mem.mem -> Prop)))
            (le: temp_env) (st: stateM) (m: Memory.Mem.mem) :=
  match_temp_env var_inv le st m.

(*
Definition post {r: Type} (state_inv : stateM -> Memory.Mem.mem -> Prop)
           (match_res : r -> val -> Memory.Mem.mem -> Prop)
           (var_inv : list (positive * Ctypes.type * (val -> stateM -> Memory.Mem.mem -> Prop)))
           (vr : positive * Ctypes.type) (res : r)  (st:stateM) (le: temp_env) (m: Memory.Mem.mem) :=
  state_inv st m /\ match_temp_env ((vr, match_res res) :: var_inv) le m.
*)

Section S.
  Variable p : Clight.program.

  Variable res : Type.
  Variable f :  M res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.
  Variable stm: Clight.statement.

  Variable modifies : list block.

  Variable match_arg : list ((AST.ident * Ctypes.type) * (val -> stateM -> Memory.Mem.mem -> Prop)).

  Variable match_res : res -> val  -> stateM -> Memory.Mem.mem -> Prop.

  Definition correct_body (st : stateM)   (le:temp_env) (m:Memory.Mem.mem) :=
    match_temp_env match_arg le st m ->
    match f st with
          | None => True
          | Some (v',st') =>
              (* We prove that we can reach a return state *)
              forall k,
                is_call_cont k ->
                (* We prove that we can reach a return state *)
                exists v m' t,
                Star (Clight.semantics2 p) (State fn stm k empty_env le m)
                     t
                     (Returnstate v (call_cont k) m') /\
                  (* The return memory matches the return state *)
                  match_res v' v st' m' /\ Cop.val_casted v (fn_return fn) /\
                  unmodifies_effect modifies m m'
          end.

End S.


Definition list_rel (args : list Type)
           (rargs : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args)
           (a     : DList.t (fun x => x) args) :        list (val -> stateM -> Memory.Mem.mem -> Prop) :=
  DList.to_list (fun (x : Type) H  => H)
             (DList.map2 (fun (a0 : Type) (F : a0 -> val -> stateM -> Memory.Mem.mem -> Prop) x   => F x) rargs a).

Definition list_rel_arg (p : list (AST.ident * Ctypes.type)) (args : list Type) (rargs : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) args)
           (a     : DList.t (fun x => x) args) :
         list  (AST.ident * Ctypes.type * (val -> stateM -> Memory.Mem.mem -> Prop))
  :=  List.combine p (list_rel args rargs a).


Lemma get_bind_parameter_temps_s :
  forall lp lv (i:AST.ident)  te,
    ~ In i (var_names lp) ->
    Maps.PTree.get i (bind_parameter_temps_s lp lv te) = Maps.PTree.get i te.
Proof.
  induction lp.
  - simpl. intros. reflexivity.
  - simpl.
    destruct a;simpl.
    intros. destruct lv. auto.
    destruct (Pos.eq_dec i i0).
    subst. tauto.
    rewrite IHlp.
    apply Maps.PTree.gso.
    congruence.
    tauto.
Qed.



Lemma match_arg_list_match_init_env :
  forall (targs: list Type)
         (lval: DList.t (fun _ => val) targs)
         (a   : DList.t (fun x => x) targs)
         (ma : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) targs)
         m p te st
         (HLEN : length p = length targs)
         (NOREP1: Coqlib.list_norepet (var_names p))
         (MA : DList.Forall2 (fun (a : Type) (R : a -> val -> stateM -> Memory.Mem.mem -> Prop) (X : a * val) => R (fst X) (snd X) st m
                             ) ma (DList.zip a lval))
         (MA' : Forall2
                  (fun (v : val) (t : AST.ident * Ctypes.type) =>
                     Cop.val_casted v (snd t))
                  (DList.to_list (fun (_ : Type) (v : val) => v) lval) p)
  ,
      match_temp_env (list_rel_arg p targs ma a)
        (bind_parameter_temps_s p (DList.to_list (fun (_ : Type) (v0 : val) => v0) lval) te) st m .
Proof.
  unfold match_temp_env.
  induction targs.
  - intros. car_cdr.
    simpl.
    destruct p ; try discriminate.
    simpl. unfold list_rel_arg. simpl.
    constructor.
  - intros. car_cdr.
    destruct p ; try discriminate.
    simpl. destruct p.
    assert (NOTIN :~ In i (var_names p0)).
    {
      simpl in NOREP1.
      inv NOREP1. tauto.
    }
    unfold list_rel_arg.
    simpl.
    constructor.
    + unfold match_elt.
      simpl.
      rewrite get_bind_parameter_temps_s by assumption.
      rewrite Maps.PTree.gss.
      simpl in MA.
      inv MA'. simpl in H2.
      tauto.
    +
      eapply IHtargs.
      simpl in HLEN.
      congruence.
      inv NOREP1. auto.
      simpl in MA.
      tauto.
      inv MA';auto.
Qed.




Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  (* [Args,Res] provides the mapping between the Coq and the C types *)
  Variable args : list Type.
  Variable res : Type.

  (* [f] is a Coq Monadic function with the right type *)
  Variable f : arrow_type args (M res).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn: Clight.function.

  Variable modifies : list block.

  (* Usually, only the first arguments is using stateM.
     Most of the arguments do not use Memory.Mem.mem either *)
  Variable match_arg_list : DList.t (fun x => x -> val -> stateM -> Memory.Mem.mem -> Prop) (stateM :: args).

  Variable match_res : res -> val -> stateM -> Memory.Mem.mem -> Prop.

  Lemma correct_function_from_body : forall
      (DIS : Coqlib.list_disjoint (var_names (fn_params fn)) (var_names (fn_temps fn)))
      (NOREP1: Coqlib.list_norepet (var_names (fn_params fn)))
      (NOREP :  Coqlib.list_norepet (var_names (fn_vars fn)))
      (NOVAR : fn_vars fn = nil)
      (HLEN : Datatypes.length (fn_params fn) = S (Datatypes.length args))
      (C : forall st le m a, correct_body p  res (app f a) fn (fn_body fn) modifies
                                          (list_rel_arg (fn_params fn) (stateM::args) match_arg_list (DList.DCons st  a))
                                          match_res st le m)

    ,
    correct_function3 p args res f fn modifies match_arg_list match_res.
  Proof.
    econstructor.
    intros.
    destruct (app f a st) eqn: EQ; auto.
    destruct p0 as (v',st').
    intros lval k m K MM MA.
    specialize (C st (bind_parameter_temps_s (fn_params fn) ((DList.to_list (fun (_ : Type) (v0 : val) => v0) lval))
          (create_undef_temps (fn_temps fn))) m a).
    unfold correct_body in C.
    rewrite EQ in C.
    exploit C;eauto.
    {
      apply match_arg_list_match_init_env;auto.
    }
    intros (v2& m'& t'& EX & RES).
    do 3 eexists.
    split ; eauto.
    eapply star_step.
    econstructor ; eauto.
    econstructor ; eauto.
    - rewrite NOVAR.
      econstructor ; eauto.
    - rewrite bind_parameter_temps_eq.
      reflexivity.
      simpl.
      rewrite DList.length_to_list.
      auto.
    - eapply star_trans.
      eauto.
      apply star_refl.
      reflexivity.
    - reflexivity.
  Qed.


End S.




Lemma apply_cont_cont : forall p fn m k s' k' le,
    apply_cont k = Some (s', k') ->
    Step (semantics2 p)
         (State fn Sskip k empty_env le m) Events.E0
         (State fn s' k' empty_env le m).
Proof.
  intros.
  destruct k ; inversion H;subst.
  - econstructor ;eauto.
  - econstructor;eauto.
  - econstructor;eauto.
  - econstructor;eauto.
Qed.

Definition is_tmp_expr (e : expr) : option (AST.ident * Ctypes.type) :=
  match e with
  | Etempvar v t => Some(v,t)
  | _           => None
  end.

Fixpoint map_opt {A B : Type} (F : A -> option B) (l : list A) : option (list B) :=
  match l with
  | nil => Some nil
  | e::l => match F e , map_opt F l with
            | Some v, Some l => Some (v::l)
            | _ , _ => None
            end
  end.

Lemma length_map_opt : forall {A B: Type} (F : A -> option B) (l : list A) l',
    map_opt F l = Some l' ->
    List.length l = List.length l'.
Proof.
  induction l; simpl.
  - intros. inv H. reflexivity.
  - intros. destruct (F a); try discriminate.
    destruct (map_opt F l) eqn:M; try discriminate.
    inv H.
    simpl. f_equal. apply IHl;auto.
Qed.



Lemma map_fst_combine : forall {A B: Type} (l1: list A) (l2: list B),
    List.length l1 = List.length l2 ->
    map fst (combine l1 l2) = l1.
Proof.
  induction l1; simpl.
  - reflexivity.
  - destruct l2; simpl.
    discriminate.
    intros.
    f_equal.
    auto.
Qed.

(*
Lemma match_temp_env_set : forall x v te m l
    (NOTIN: ~ In x (List.map (fun x => fst (fst x)) l)),
    match_temp_env l te m ->
    match_temp_env l (Maps.PTree.set x v  te) m.
Proof.
  unfold match_temp_env.
  induction l.
  - simpl. intros. constructor.
  - simpl. intros.
    inv H.
    constructor ; auto.
    unfold match_elt in H2.
    unfold match_elt.
    destruct (Pos.eq_dec (fst (fst a)) x).
   + subst.
     exfalso.
     apply NOTIN.
     left ; reflexivity.
   + rewrite Maps.PTree.gso by auto.
     auto.
Qed.

Lemma match_temp_env_up :
  forall te m m'  (l:list (AST.ident * Ctypes.type * (val -> Memory.Mem.mem -> Prop)))
         (MOD :
                forall x t r v,
                  In ((x,t),r) l ->
                  Maps.PTree.get x te = Some v ->
                  r v m -> r v m')
  ,
    match_temp_env l te m ->
    match_temp_env l te m'.
Proof.
  unfold match_temp_env.
  induction l.
  - constructor.
  - intros.
    inv H ; constructor ; auto.
    unfold match_elt in *.
    destruct (Maps.PTree.get (fst (fst a)) te) eqn:G;auto.
    destruct H2 ; split ; auto.
    destruct a as ((x,t),r).
    simpl in *.
    eapply MOD;eauto.
    eapply IHl;eauto.
    intros.
    eapply MOD ;eauto.
    simpl. right;eauto.
Qed.



Definition var_inv_preserve (var_inv : list (positive * Ctypes.type * (val ->Memory.Mem.mem -> Prop)))
           (modifies : list block) (te: temp_env)
  :=
  forall  m m',
    unmodifies_effect modifies m m' ->
    forall (x : AST.ident) (t : Ctypes.type) (r : val -> Memory.Mem.mem -> Prop)
           (v : val),
      In (x, t, r) var_inv -> Maps.PTree.get x te = Some v -> r v m -> r v m'.

(*
Section S.
  Variable p : program.
  Variable fn: Clight.function.

  Lemma correct_statement_call :
    forall  (has_cast : bool) args res (f : arrow_type args (M res)) a loc
           vres fvar targs ti eargs tres  fct modifies
           (state_inv : stateM -> val -> Memory.Mem.mem -> Prop)
           (FS : Globalenvs.Genv.find_symbol (globalenv (semantics2 p)) fvar = Some loc)
           (FF : Globalenvs.Genv.find_funct (globalenv (semantics2 p))
                                            (Vptr loc Ptrofs.zero) = Some (Ctypes.Internal fct))
           (TF : type_of_fundef (Ctypes.Internal fct) =
                   Ctypes.Tfunction targs ti AST.cc_default)

           (match_arg : DList.t (fun x : Type => x -> val -> Memory.Mem.mem -> Prop) args)
           (match_res : res -> val  -> Memory.Mem.mem -> Prop)
           (C : correct_function3 p args res f fct modifies state_inv match_arg match_res)
           (var_inv : list (positive * Ctypes.type * (val ->Memory.Mem.mem -> Prop)))
           (le : temp_env) (m : Memory.Mem.mem) (st : stateM)
           (VARINV: var_inv_preserve var_inv modifies le)
(*           (PRE1: state_inv st m)
           (PRE2: match_temp_env var_inv le m)*)
           (lvar : list (positive * Ctypes.type))
           (EARGS : map_opt is_tmp_expr eargs = Some lvar)
           (TI    : ti = fn_return fct)
           (TARGS : targs = Ctypes.type_of_params lvar)
           (TARGSF: List.map snd lvar = List.map snd (fn_params fct))
           (VAR : incl (List.combine lvar (list_rel args match_arg a)) var_inv)
           (NOTIN1 : ~In vres   (map  (fun x  => fst (fst x)) var_inv))
           (NOTIN2 : ~In tres   (map  (fun x  => fst (fst x)) var_inv))
           (LVAL  : match_temp_env var_inv le m ->
                    exists lval, map_opt (fun x => Maps.PTree.get (fst x) le) lvar = Some lval
                                 /\ List.length lval = List.length args)
    ,
      correct_statement p res (app f a) fn
    (Ssequence
       (Scall (Some tres)
          (Evar fvar
             (Ctypes.Tfunction targs ti AST.cc_default))
          eargs)
       (Sset vres (if has_cast then
          (Ecast (Etempvar tres ti) ti) else Etempvar tres ti)))
    modifies (pre state_inv var_inv) (post state_inv match_res var_inv (vres,ti)) st le m.
  Proof.
    repeat intro.
    rename H into PRE.
    destruct C.
    specialize (fn_eval_ok4 a st).
    destruct (app f a st); try congruence.
    destruct p0 as (v',st').
    intros s' k k' K.
    destruct PRE as (PRE1 & PRE2).
    specialize (LVAL PRE2). destruct LVAL as (lval& LVAL & LEN).
    specialize (fn_eval_ok4 (DList.of_list_sl lval args0 LEN)
                            (Kcall (Some tres) fn empty_env le
                                   (Kseq (Sset vres (if has_cast
                then Ecast (Etempvar tres ti) ti
                else Etempvar tres ti)) k)) m I PRE1).
    assert (MA : DList.Forall2 (fun (a : Type) (R : a -> val -> Memory.Mem.mem -> Prop) (X : a * val) => R (fst X) (snd X) m) match_arg
                  (DList.zip a (DList.of_list_sl lval args0 LEN))).
    {
      unfold match_temp_env in PRE2.
      rewrite Forall_forall in PRE2.
      revert PRE2.
      revert LVAL VAR.
      clear.
      revert lval LEN.
      revert  lvar var_inv.
      induction a.
      - intros. car_cdr.
        simpl. auto.
      - intros. car_cdr.
        simpl.
        destruct lval. discriminate.
        simpl.
        destruct lvar. discriminate.
        simpl in LVAL.
        assert (In (p, c v) var_inv).
        { apply VAR. simpl. tauto. }
        generalize (PRE2 _ H).
        unfold match_elt.
        change AST.ident with positive in *.
        simpl.
        destruct (Maps.PTree.get (fst p) le) eqn:G;try discriminate.
        destruct (map_opt
             (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le)
             lvar) eqn:M ; try discriminate.
        inv LVAL.
        split. tauto.
        eapply IHa; eauto.
        repeat intro.
        apply VAR.
        right. auto.
    }
    assert (MA' : Forall2
                  (fun (v : val) (t : AST.ident * Ctypes.type) =>
                   Cop.val_casted v (snd t))
                  lval
                  lvar).
    {
      revert PRE2.
      assert (P: incl lvar  (map fst var_inv)).
      {
        revert VAR.
        rewrite <- (map_fst_combine lvar (list_rel args0 match_arg a)) at 2.
        apply incl_map.
        unfold list_rel.
        rewrite DList.length_to_list.
        clear - LEN LVAL.
        apply length_map_opt in LVAL.
        rewrite LEN in *.
        auto.
      }
      revert LVAL.
      revert P.
      clear.
      revert lval.
      unfold match_temp_env.
      induction lvar.
      - simpl. intros.
        inv LVAL. constructor.
      - simpl.
        intros.
        change AST.ident with positive in *.
        destruct (Maps.PTree.get (fst a) le) eqn: G; try discriminate.
        destruct (           map_opt (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le)) eqn:M ; try discriminate.
        inv LVAL.
        constructor.
        assert (INM : In a (map fst var_inv)).
        { apply P.
          simpl. tauto. }
        rewrite in_map_iff in INM.
        destruct INM as (x & FST & IN).
        rewrite Forall_forall in PRE2.
        apply PRE2 in IN.
        unfold match_elt in IN.
        change AST.ident with positive in *.
        rewrite FST in *.
        rewrite G in IN.
        tauto.
        apply IHlvar; auto.
        eapply incl_cons_inv; eauto.
    }
    assert (EQ: lval = (DList.to_list (fun (_ : Type) (v : val) => v)
                                   (DList.of_list_sl lval args0 LEN))).
    { apply (DList.to_list_of_list_sl ). }
    assert (MA2:= MA').
    rewrite EQ in MA'.
    assert (MA'' : Forall2
          (fun (v : val) (t : AST.ident * Ctypes.type) =>
             Cop.val_casted v (snd t)) lval (fn_params fct)).
    {
      revert MA2.
      revert TARGSF.
      clear.
      revert lvar lval.
      induction (fn_params fct).
      - destruct lvar ; simpl; try discriminate.
        auto.
      - destruct lvar; try discriminate.
        simpl. intros. inv TARGSF.
        inv MA2;auto.
        constructor ;auto.
        unfold AST.ident in *.
        rewrite H0 in H4;auto.
        eapply IHl;eauto.
    }
    rewrite EQ in MA''.
    destruct (fn_eval_ok4 MA MA'') as (v1 & m1 & t1 & STAR & RES' &CAST & INV &MOD).
    do 3 eexists.
    split.
    eapply star_step.
    econstructor ;eauto.
    eapply star_step.
    econstructor ;eauto.
    simpl. reflexivity.
    econstructor ;eauto.
    eapply eval_Evar_global.
    apply Maps.PTree.gempty.
    eauto.
    eapply deref_loc_reference.
    simpl; reflexivity.
    { instantiate (1:= lval).
      revert MA2 TARGS EARGS LVAL.
      clear.
      revert lval targs lvar.
      induction eargs.
      - simpl. intros. inv EARGS.
        simpl in LVAL. inv LVAL.
        constructor.
      - simpl.
        intros.
        destruct (is_tmp_expr a) eqn:TMP; try congruence.
        destruct a ; simpl in TMP ; try congruence.
        inv TMP.
        destruct (map_opt is_tmp_expr eargs) eqn:M; try discriminate.
        inv EARGS.
        simpl in LVAL.
        destruct (Maps.PTree.get i le) eqn:G ; try discriminate.
        destruct (map_opt (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le) l) eqn:M2; try discriminate.
        inv LVAL.
        simpl. econstructor ; eauto.
        econstructor ; eauto.
        simpl.
        inv MA2.
        apply Cop.cast_val_casted. auto.
        inv MA2.
        eapply IHeargs; eauto.
    }
    eapply star_trans.
    rewrite <- EQ in STAR.
    eauto.
    unfold call_cont.
    eapply star_step.
    econstructor ; eauto.
    eapply star_step.
    econstructor ; eauto.
    eapply star_step; eauto.
    econstructor ; eauto.
    {
      instantiate (1:=v1).
      destruct has_cast.
      econstructor;eauto.
      econstructor;eauto.
      unfold set_opttemp.
      rewrite Maps.PTree.gss. reflexivity.
      simpl.
      apply Cop.cast_val_casted; auto.
      subst. auto.
      econstructor; eauto.
      unfold set_opttemp.
      rewrite Maps.PTree.gss. reflexivity.
    }
    eapply star_step.
    eapply apply_cont_cont; eauto.
    apply star_refl.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    unfold post.
    repeat split; auto.
    unfold match_temp_env.
    apply Forall_cons.
    - unfold match_elt.
      simpl.
      rewrite Maps.PTree.gss.
      subst. tauto.
    - apply match_temp_env_set; auto.
      apply match_temp_env_set; auto.
      revert PRE2.
      eapply match_temp_env_up; eauto.
      apply VARINV.
      auto.
  Qed.
End S.

Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res1 : Type.

  Variable f1 : M res1.

  Variable res2 : Type.

  Variable f2 : res1 -> (M res2).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable mem_inv   : stateM -> Memory.Mem.mem -> Prop.

  Variable match_res1 : res1 -> val -> Memory.Mem.mem -> Prop.

  Variable match_res2 : res2  -> val -> Memory.Mem.mem -> Prop.

  Lemma correct_statement_seq_body :
    forall (s1 s2:Clight.statement) vret ti
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> Memory.Mem.mem -> Prop)))
      st le m
      (C1 : correct_statement p res1 f1 fn s1 modifies (pre mem_inv var_inv) (post mem_inv match_res1 var_inv (vret,ti)) st le m)
      (C2 : forall le m st x, correct_body p res2 (f2 x) fn s2 modifies mem_inv ((vret,ti,match_res1 x):: var_inv) match_res2 st le m)
    ,
             correct_body p  res2 (bindM f1 f2) fn
             (Ssequence s1 s2) modifies mem_inv var_inv match_res2 st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold bindM.
    unfold runM at 1.
    unfold correct_statement in C1.
    destruct (f1 st) eqn:F1 ; try congruence.
    destruct p0 as (v1,st1).
    unfold runM.
    destruct (f2 v1 st1) eqn:F2; try congruence.
    destruct p0 as (v2,st2).
    intros.
    destruct (C1 PRE s2 (Kseq s2 k) k  eq_refl) as
      (le'& m' & t & ST & MR & MOD).
    specialize (C2 le' m' st1 v1).
    unfold correct_body in C2.
    rewrite F2 in C2.
    assert (PRE2 : pre mem_inv ((vret, ti, match_res1 v1) :: var_inv) st1 le' m').
    {
      unfold pre. unfold post in MR.
      tauto.
    }
    destruct (C2  PRE2  _ H) as
      (le2& m2 & t2 & ST2 & MR2).
    exists le2. exists m2. exists (t ++ t2).
    split;auto.
    eapply star_step.
    econstructor ; eauto.
    eapply star_trans.
    eauto.
    eauto.
    reflexivity.
    reflexivity.
    repeat split ; try tauto.
    eapply unmodifies_effect_trans; eauto.
    tauto.
    auto.
    auto.
  Qed.

End S.

Definition set_bool (vr: positive) (b:bool) (le: temp_env) :=
  Maps.PTree.set vr (if b then Vint Int.one else Vint Int.zero) le.

Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f1 f2 : M res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable mem_inv   : stateM -> Memory.Mem.mem -> Prop.

  Variable match_res : res -> val -> Memory.Mem.mem -> Prop.

  Lemma correct_statement_if_body :
    forall (s1 s2:Clight.statement) (x:bool) vr
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> Memory.Mem.mem -> Prop)))
      st le m
      (IN : In ((vr, Clightdefs.tbool, (without_mem match_bool x))) var_inv)
      (C1 : correct_body p res (if x then f1 else f2) fn (if x then s1 else s2)
                         modifies mem_inv var_inv match_res st
                         le m)
    ,

      correct_body p res (if x then f1 else f2) fn
                          (Sifthenelse (Etempvar vr Clightdefs.tbool)
                                       s1 s2) modifies mem_inv var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold correct_body in C1.
    specialize(C1 PRE).
    assert (GET : Maps.PTree.get vr le = Some (Vint (if x then Int.one else Int.zero))).
    {
      destruct PRE as (P1 & P2).
      unfold match_temp_env in P2.
      rewrite Forall_forall in P2.
      apply P2 in IN.
      unfold match_elt in IN.
      simpl in IN.
      destruct (Maps.PTree.get vr le).
      destruct IN.
      unfold without_mem,match_bool in H.
      subst. reflexivity.
      tauto.
    }
    destruct x;auto.
    - destruct (f1 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k H) as (v1 & m1 & t1 & STAR & I1 & I2 & I3 & I4).
      exists v1,m1,t1.
      repeat split.
      eapply star_step.
      econstructor ;eauto.
      econstructor ;eauto.
      reflexivity.
      change (negb (Int.eq Int.one Int.zero)) with true.
      simpl.
      eauto.
      reflexivity.
      auto. auto.
      auto.
      auto.
    - destruct (f2 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k H) as (v1 & m1 & t1 & STAR & I1 & I2 & I3 & I4).
      exists v1,m1,t1.
      repeat split.
      eapply star_step.
      econstructor ;eauto.
      econstructor ;eauto.
      reflexivity.
      change (negb (Int.eq Int.one Int.zero)) with true.
      simpl.
      eauto.
      reflexivity.
      auto. auto.
      auto.
      auto.
  Qed.

End S.






Lemma match_temp_ex :
  forall l l' le m,
         match_temp_env l le m ->
         incl l' (List.map fst l)  ->
  exists lval : list val,
    map_opt (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le)
      l' = Some lval.
Proof.
  induction l'.
  -
    simpl. exists nil.
    reflexivity.
  - intros.
    apply List.incl_cons_inv in H0.
    destruct H0 as (IN & INCL).
    destruct (IHl' _ _ H INCL) as (lval1 & MAP).
    unfold match_temp_env in H.
    rewrite Forall_forall in H.
    rewrite in_map_iff in IN.
    destruct IN as (v & FST & IN).
    apply H in IN.
    unfold match_elt in IN.
    destruct (Maps.PTree.get (fst (fst v)) le) eqn:E; try tauto.
    exists (v0 ::lval1).
    simpl.
    subst.
    unfold AST.ident in *.
    rewrite E in *.
    rewrite MAP.
    reflexivity.
Qed.
*)
*)
