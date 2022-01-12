(** Structure of soundness proofs for dx generated programs *)
From Coq Require Import List.
From Coq Require Import Program.Equality.
From dx Require Import IR.
From compcert Require Import Coqlib Values.
From compcert Require Import SimplExpr.
From compcert Require Import Clight.

From bpf.comm Require Import State Monad. (*
From bpf.src Require Import DxIntegers.*)
From compcert Require Import Integers.
From compcert Require Import Smallstep.
From compcert Require Import Clightdefs.
Import Clightdefs.ClightNotations.

From bpf.proof Require Import clight_exec.
Open Scope type_scope.


Definition without_mem {A B : Type} (P : A -> B -> Prop)
           (a : A) (b: B) (m: Memory.Mem.mem) :=  P a b.

Definition stateless {A B : Type} (P : A -> B -> Prop)
           (a : A) (b: B) (st: State.state) (m: Memory.Mem.mem) :=  P a b.


Definition match_bool (b:bool) (v:val) :=
  v = Vint (if b then Integers.Int.one else Integers.Int.zero).

(** dx requires primitives.
    For each primitive,
    we have soundness theorem relating the Coq function and the primitive expression.
    The primitive declaration is untyped.
*)

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


Inductive dpair : Type :=
  mk {
      typ : Type;
      elt: typ
    }.

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

  Section FROMDP.

    Fixpoint of_list_dp (l : list dpair) : DList.t (fun x => x) (List.map typ l) :=
      match l as l' return DList.t (fun x => x) (List.map typ l') with
      | nil => DNil _
      |  (mk t v) :: l => DList.DCons (fun x => x) v (of_list_dp l)
      end.
  End FROMDP.

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
    Variable T : CompilableType.

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

(**r ysh: adding st st' *)
Definition unmodifies_effect (l : list block) (m m' : Memory.Mem.mem) (st st' : State.state) : Prop :=
  match l with
  | nil => m = m' /\ st = st'
  | _ =>
  forall b, ~ In b l -> forall chk o,
      Memory.Mem.load chk m b o =
        Memory.Mem.load chk m' b o
  end.

Lemma unmodifies_effect_trans : forall l m1 m2 m3 st1 st2 st3,
    unmodifies_effect l m1 m2 st1 st2 ->
    unmodifies_effect l m2 m3 st2 st3 ->
    unmodifies_effect l m1 m3 st1 st3.
Proof.
  unfold unmodifies_effect.
  intros.
  destruct l.
  firstorder; subst; reflexivity.
  intros.
  rewrite H by auto.
  rewrite H0 by auto.
  reflexivity.
Qed.


Definition all_args (l : list Type) (is_pure: bool) :=
  if is_pure then l else (unit:Type) :: l.

Definition all_args_list (l : list Type) (is_pure : bool) (dl :DList.t (fun x => x) l) : DList.t (fun x => x) (all_args l is_pure) :=
  if is_pure as b return (DList.t (fun x : Type => x) (all_args l b))
  then dl
  else DList.DCons tt dl.



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

(*  Variable match_mem : State.state -> val -> Memory.Mem.mem -> Prop.*)

  Variable is_pure : bool.

  (* [match_arg] relates the Coq arguments and the C arguments *)
  Variable match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) (all_args args is_pure).

  (* [match_res] relates the Coq result and the C result *)
  Variable match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop.

  Class correct_function3 (a: DList.t (fun x => x) args) :=
    mk_correct_function3
      {
        fn_eval_ok3 : forall (st:State.state),
          match app (r:=M res) f  a st with
          | None => True
          | Some (v',st') =>
              (* We prove that we can reach a return state *)
              forall (lval: DList.t (fun _ => val) (all_args  args is_pure))
                     k m,
                (* they satisfy the invariants *)
                DList.Forall2 (fun (a:Type) (R: a -> val -> State.state -> Memory.Mem.mem ->Prop) (X:a * val) => R (fst X) (snd X) st m)
                              match_arg_list (DList.zip  (all_args_list args is_pure a ) lval) ->
                (* We prove that we can reach a return state *)
                Forall2 (fun v t => Cop.val_casted v (snd t)) (DList.to_list (fun _ v => v) lval) (fn_params fn) ->

                exists v m' t,
                Star (Clight.semantics2 p) (Callstate  (Ctypes.Internal fn)
                                                       (DList.to_list (fun x v => v) lval)  k m) t
                     (Returnstate v (call_cont k) m') /\
                  (* The return memory matches the return state *)
                  match_res  v' v st' m' /\ Cop.val_casted v (fn_return fn) /\
                  unmodifies_effect modifies m m' st st'
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

  Variable match_arg : State.state -> temp_env -> Memory.Mem.mem -> Prop.

  Variable match_res : res -> State.state  -> temp_env -> Memory.Mem.mem -> Prop.

  Definition correct_statement (st : State.state) (le:temp_env) (m:Memory.Mem.mem) :=
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
                    match_res v' st' le' m' /\ unmodifies_effect modifies m m' st st'
    end.

End S.


Definition match_elt (st: State.state) (m : Memory.Mem.mem) (le : temp_env)
           (r : (AST.ident * Ctypes.type) * (val -> State.state -> Memory.Mem.mem -> Prop)) :=
  match Maps.PTree.get (fst (fst r)) le with
  | None => False
  | Some v => (snd r) v st m /\ Cop.val_casted v (snd (fst r))
  end.

Definition match_temp_env (dl : list ((AST.ident * Ctypes.type) * (val -> State.state -> Memory.Mem.mem -> Prop)))
           (le:temp_env) (st: State.state) (m : Memory.Mem.mem)
            : Prop :=
  Forall (match_elt st m le) dl.

Definition pre
           (var_inv : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
            (st: State.state) (le: temp_env)  (m: Memory.Mem.mem) :=
  match_temp_env var_inv le st m.

Definition post {r: Type}
           (match_res : r -> val -> State.state -> Memory.Mem.mem -> Prop)
           (var_inv : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
           (vr : positive * Ctypes.type) (res : r)  (st:State.state) (le: temp_env) (m: Memory.Mem.mem) :=
  match_temp_env ((vr, match_res res) :: var_inv) le st m.

Definition post_unit (match_res : unit -> val -> State.state -> Memory.Mem.mem -> Prop)
           (var_inv : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
           (r : unit) (st:State.state) (le: temp_env) (m: Memory.Mem.mem) :=
  match_temp_env var_inv le st m /\ match_res r Vundef st m.



Section S.
  Variable p : Clight.program.

  Variable res : Type.
  Variable f :  M res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.
  Variable stm: Clight.statement.

  Variable modifies : list block.

  Variable match_arg : list ((AST.ident * Ctypes.type) * (val -> State.state -> Memory.Mem.mem -> Prop)).

  Variable match_res : res -> val  -> State.state -> Memory.Mem.mem -> Prop.

  Definition correct_body (st : State.state)   (le:temp_env) (m:Memory.Mem.mem) :=
    match_temp_env match_arg le st m ->
    match f st with
          | None => True
          | Some (v',st') =>
              (* We prove that we can reach a return state *)
              forall k,
                (* We prove that we can reach a return state *)
                exists v m' t,
                Star (Clight.semantics2 p) (State fn stm k empty_env le m)
                     t
                     (Returnstate v (call_cont k) m') /\
                  (* The return memory matches the return state *)
                  match_res v' v st' m' /\ Cop.val_casted v (fn_return fn) /\
                  unmodifies_effect modifies m m' st st'
          end.

End S.


Definition list_rel (args : list Type)
           (rargs : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args)
           (a     : DList.t (fun x => x) args) :        list (val -> State.state -> Memory.Mem.mem -> Prop) :=
  DList.to_list (fun (x : Type) H  => H)
             (DList.map2 (fun (a0 : Type) (F : a0 -> val -> State.state -> Memory.Mem.mem -> Prop) x   => F x) rargs a).

Definition list_rel_arg (p : list (AST.ident * Ctypes.type)) (args : list Type) (rargs : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) args)
           (a     : DList.t (fun x => x) args) :
         list  (AST.ident * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop))
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
         (ma : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) targs)
         m p te st
         (HLEN : length p = length targs)
         (NOREP1: Coqlib.list_norepet (var_names p))
         (MA : DList.Forall2 (fun (a : Type) (R : a -> val -> State.state -> Memory.Mem.mem -> Prop) (X : a * val) => R (fst X) (snd X) st m
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

  (* If [is_pure] is true, the C code has no handler to the monadic state *)
  Variable is_pure : bool.

  (* Usually, only the first arguments is using State.state.
     Most of the arguments do not use Memory.Mem.mem either *)

  Variable match_arg_list : DList.t (fun x => x -> val -> State.state -> Memory.Mem.mem -> Prop) (all_args args is_pure).

  Variable match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop.


  Lemma correct_function_from_body : forall
      (DIS : Coqlib.list_disjoint (var_names (fn_params fn)) (var_names (fn_temps fn)))
      (NOREP1: Coqlib.list_norepet (var_names (fn_params fn)))
      (NOREP :  Coqlib.list_norepet (var_names (fn_vars fn)))
      (NOVAR : fn_vars fn = nil)
      (HLEN : Datatypes.length (fn_params fn) = Datatypes.length (all_args args is_pure))
      a
      (C : forall st le m, correct_body p  res (app f a) fn (fn_body fn) modifies
                                          (list_rel_arg (fn_params fn) (all_args args is_pure) match_arg_list (all_args_list args is_pure  a))
                                          match_res st le m)

    ,
        correct_function3 p args res f fn modifies is_pure match_arg_list match_res a.
  Proof.
    econstructor.
    intros.
    destruct (app f a st) eqn: EQ; auto.
    destruct p0 as (v',st').
    intros lval k m MM MA.
    specialize (C st (bind_parameter_temps_s (fn_params fn) ((DList.to_list (fun (_ : Type) (v0 : val) => v0) lval))
          (create_undef_temps (fn_temps fn))) m).
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

Definition var_expr (e : expr) : option (AST.ident * Ctypes.type) :=
  match e with
  | Etempvar v t => Some(v,t)
  | Ecast (Etempvar v t) _ => Some (v, t)
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

Lemma match_temp_env_cons :
  forall x te st m l,
         (match_elt st m te x) ->
         match_temp_env l te st m  ->
    match_temp_env (x::l) te st m.
Proof.
  unfold match_temp_env.
  constructor;auto.
Qed.


Lemma match_temp_env_set : forall x v te st m l
    (NOTIN: ~ In x (List.map (fun x => fst (fst x)) l)),
    match_temp_env l te st m ->
    match_temp_env l (Maps.PTree.set x v  te) st m.
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
  forall te st m st' m'  (l:list (AST.ident * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
         (MOD :
                forall x t r v,
                  In ((x,t),r) l ->
                  Maps.PTree.get x te = Some v ->
                  r v st m -> r v st' m')
  ,
    match_temp_env l te st m ->
    match_temp_env l te st' m'.
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


Definition var_inv_preserve {res: Type} (var_inv : list (positive * Ctypes.type * (val ->State.state -> Memory.Mem.mem -> Prop))) (match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop)
           (modifies : list block) (te: temp_env)
  :=
  forall  r rv m m' st st',
    unmodifies_effect modifies m m' st st' ->
    match_res r rv st' m' ->
    match_temp_env var_inv te st m  ->
    match_temp_env var_inv te st' m'.

Definition  exec_deref_loc (ty : Ctypes.type) (m : Memory.Mem.mem) (b : block) (ofs : ptrofs) : option val :=
  match Ctypes.access_mode ty with
  | Ctypes.By_value chk => Memory.Mem.loadv chk m (Vptr b ofs)
  | Ctypes.By_reference => Some (Vptr b ofs)
  | Ctypes.By_copy => Some (Vptr b ofs)
  | Ctypes.By_nothing => None
  end.

(**r ysh: executing clight expressions, return the result of the expression (Q: Clight has `eval_expr`, is a relation ), this definition should be equivalent to clight's `eval_expr` *)
Fixpoint exec_expr (ge:genv) (ev:env) (le: temp_env) (m:Memory.Mem.mem) (e: expr) {struct e} : option val :=
  match e with
  | Econst_int i t    => Some (Vint  i)
  | Econst_float f _  => Some (Vfloat f)
  | Econst_single f _ => Some (Vsingle f)
  | Econst_long  l _  => Some (Vlong l)
  | Evar v  t         => match Maps.PTree.get v ev with
                         | Some (b,t') => (**r ysh: local variable *)
                            if Ctypes.type_eq t t' then
                              exec_deref_loc t m b  Ptrofs.zero
                            else None
                         | None   => (**r ysh: global variable *)
                            match (Globalenvs.Genv.find_symbol ge v) with
                            | None => None
                            | Some b => exec_deref_loc t m b  Ptrofs.zero
                            end
                         end
  | Etempvar id t     => Maps.PTree.get id le
  | Ederef e t        => match exec_expr ge ev le m e with  (**r ysh: None -> *)
                         | None => None
                         | Some v => 
                            match v with
                            | Vptr b ofs => exec_deref_loc t m b ofs
                            | _ => None
                            end
                         end
  | Eaddrof _ _       => None
  | Eunop o e t       => match exec_expr ge ev le m e with
                         | None => None
                         | Some v => Cop.sem_unary_operation o v (typeof e) m
                         end
  | Ebinop o e1 e2 t    => match exec_expr ge ev le m e1 , exec_expr ge ev le m e2 with
                           | Some v1 , Some v2 => Cop.sem_binary_operation ge o v1 (typeof e1) v2 (typeof e2) m
                           | _ , _ => None
                           end
  | Ecast e ty        => match exec_expr ge ev le m e with
                         | None => None
                         | Some v => Cop.sem_cast v (typeof e) ty m
                         end
  | Efield _ _ _      => None (**r ysh: None -> *)
  | Esizeof _ _       => None
  | Ealignof _ _      => None
  end.

Lemma deref_loc_var : forall t m b v ofs,
    exec_deref_loc t m b ofs = Some v -> (**r ysh: zero -> ofs *)
    deref_loc t m b ofs v.
Proof.
  intros.
  unfold exec_deref_loc in H.
  destruct (Ctypes.access_mode t) eqn:AM.
  eapply deref_loc_value; eauto.
  inv H. eapply deref_loc_reference; eauto.
  inv H. eapply deref_loc_copy; eauto.
  discriminate.
Qed.

(**r ysh: The Lemma tells the relation between `exec_expr` and Clight's `eval_expr` *)
Lemma eval_expr_eval : forall ge ev te m e v,
    exec_expr ge ev te m e = Some v ->
    eval_expr ge ev te m e v.
Proof.
  induction e.
  - simpl. intros. inv H.
    econstructor.
  - simpl. intros. inv H.
    econstructor.
  - simpl. intros. inv H.
    econstructor.
  - simpl. intros. inv H.
    econstructor.
  - simpl. intros.
    destruct (Maps.PTree.get i ev) eqn:G.
    + destruct p.
      destruct (Ctypes.type_eq t t0).
      * subst.
        econstructor. eauto.
        econstructor.
        eauto.
        apply deref_loc_var. auto.
      * discriminate.
    +
      destruct (Globalenvs.Genv.find_symbol ge i) eqn:FS; try discriminate.
      simpl in H. inv H.
      econstructor.
      eapply eval_Evar_global;eauto.
      apply deref_loc_var. auto.
  - simpl. intros.
    econstructor ; eauto.
  - (**r ysh: `intros ; discriminate.` -> *)
    intros.
    simpl in H.
    destruct (exec_expr ge ev te m e) eqn: He; try discriminate.
    destruct v0 eqn: Hv0; try discriminate.
    subst.
    econstructor.
    econstructor.
    apply IHe.
    reflexivity.
    apply deref_loc_var. auto.
  - intros ; discriminate.
  - simpl.
    intros.
    destruct (exec_expr ge ev te m e) eqn:EE.
    econstructor.
    eauto. auto.
    discriminate.
  - intros.
    simpl in H.
    destruct (exec_expr ge ev te m e1) eqn:E1; try discriminate.
    destruct (exec_expr ge ev te m e2) eqn:E2; try discriminate.
    econstructor ; eauto.
  - intros.
    simpl in H.
    destruct (exec_expr ge ev te m e) eqn:E; try discriminate.
    inv H. econstructor.
    eauto. auto.
  - intros.
    discriminate.
  - discriminate.
  - discriminate.
Qed.

Definition is_Vint (t: Ctypes.type) : bool :=
  match t with
  | Ctypes.Tint Ctypes.I32 si attr => true
  | Ctypes.Tpointer ty attr    => negb Archi.ptr64
  | Ctypes.Tvoid
  |   _  => false
  end.


Definition is_VBool (t: Ctypes.type) : bool :=
  match t with
  | Ctypes.Tint Ctypes.IBool si attr => true
  |   _  => false
  end.

Lemma val_casted_is_VBool : forall b t,
    is_VBool t = true ->
    Cop.val_casted (Val.of_bool b) t.
Proof.
  destruct t ; try discriminate.
  simpl. destruct i; try discriminate.
  destruct b; constructor.
  reflexivity. reflexivity.
Qed.

Definition is_Vfloat (t: Ctypes.type) : bool :=
  match t with
  | Ctypes.Tfloat Ctypes.F64 attr => true
  | Ctypes.Tvoid
  | _  => false
  end.

Definition is_Vsingle (t: Ctypes.type) : bool :=
  match t with
  |Ctypes.Tfloat Ctypes.F32 attr => true
  | Ctypes.Tvoid
  | _  => false
  end.

Definition is_Vlong (t: Ctypes.type) : bool :=
  match t with
  | Ctypes.Tlong si attr  => true
  | Ctypes.Tpointer ty attr    => Archi.ptr64
  | Ctypes.Tvoid
  | _ => false
  end.

Definition is_Vptr (t : Ctypes.type) : bool :=
  match t with
  | Ctypes.Tpointer ty attr => true
  | Ctypes.Tlong si attr    => Archi.ptr64
  | Ctypes.Tint Ctypes.I32 si attr => negb Archi.ptr64
  | Ctypes.Tvoid => true
  | _    => false
  end.

Definition is_Vundef (t : Ctypes.type) : bool :=
  match t with
  | Ctypes.Tvoid => true
  | _    => false
  end.


Ltac discr_bool := match goal with
                   | H : false = true |- _ => discriminate H
                   end.


Lemma is_Vint_casted : forall i t,
    is_Vint t = true ->
    Cop.val_casted (Vint i) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  destruct i0; try discr_bool.
  constructor. reflexivity.
  constructor.
  rewrite negb_true_iff in H.
  auto.
Qed.

Lemma is_Vfloat_casted : forall i t,
    is_Vfloat t = true ->
    Cop.val_casted (Vfloat i) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  destruct f; try discr_bool.
  constructor.
Qed.


Lemma is_Vsingle_casted : forall i t,
    is_Vsingle t = true ->
    Cop.val_casted (Vsingle i) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  destruct f; try discr_bool.
  constructor.
Qed.

Lemma is_Vlong_casted : forall i t,
    is_Vlong t = true ->
    Cop.val_casted (Vlong i) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  constructor.
  constructor. auto.
Qed.

Lemma is_Vptr_casted : forall b o t,
    is_Vptr t = true ->
    Cop.val_casted (Vptr b o) t.
Proof.
  destruct t; simpl ; intros; try discr_bool.
  constructor.
  destruct i; try discr_bool.
  constructor.   rewrite negb_true_iff in H.   auto.
  constructor;auto. constructor.
Qed.

Import Cop.



Definition vc_binary_operation_casted (o: Cop.binary_operation) (t1 t2: Ctypes.type) (r :Ctypes.type): bool :=
  match o with
  | Oadd => match classify_add t1 t2 with
            | add_default => Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) r

            |  _          => false
            end
  | Osub => match classify_sub t1 t2 with
            | sub_default => Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) r

            |  _          => false
            end
  | Omul   | Odiv | Omod   | Oand
  | Oor | Oxor  => Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2 &&
                               Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) r

  | Oshl | Oshr => match classify_shift t1 t2 with
                   | shift_case_ii _ => Ctypes.type_eq t1 r && Ctypes.type_eq t2 r && is_Vint r
                   | shift_case_ll _ => Ctypes.type_eq t1 r && Ctypes.type_eq t2 r   && is_Vlong r
                   | shift_case_il  _ => is_Vint t1 && is_Vlong t2 && is_Vint r
                   | shift_case_li _  => is_Vlong t1 && is_Vint t2 && is_Vlong r
                   | shift_default     => false
                   end
  | Oeq | One | Olt | Ogt | Ole | Oge  => is_VBool r
  end.


Definition var_casted_list (l: list (positive * Ctypes.type)) (le: temp_env) : Prop:=
  forall i t v,  In (i, t) l ->
               Maps.PTree.get i le = Some v ->
               Cop.val_casted v t.

Lemma val_casted_sem_binarith :
  forall f1 f2 f3 f4 v1 v2 t m v
         (BC : binarith_type (classify_binarith t t) = t)
         (SB : sem_binarith f1 f2 f3 f4 v1 t v2 t m = Some v)
         (WC1: forall s x y r,
             Ctypes.Tint Ctypes.I32 s Ctypes.noattr = t ->
             val_casted (Vint x) t ->
             val_casted (Vint y) t -> f1 s x y = Some r ->
             val_casted r t)
         (WC2: forall s x y r,
             Ctypes.Tlong s Ctypes.noattr = t ->
             val_casted (Vlong x) t ->
             val_casted (Vlong y) t -> f2 s x y = Some r ->
             val_casted r t)
         (WC3: forall x y r,
             Ctypes.Tfloat Ctypes.F64 Ctypes.noattr = t ->
             val_casted (Vfloat x) t ->
             val_casted (Vfloat y) t -> f3 x y = Some r ->
             val_casted r t)
         (WC4: forall x y r,
             Ctypes.Tfloat Ctypes.F32 Ctypes.noattr = t ->
             val_casted (Vsingle x) t ->
             val_casted (Vsingle y) t -> f4 x y = Some r ->
             val_casted r t),
    val_casted v1 t ->
    val_casted v2 t ->
    val_casted v t.
Proof.
  unfold sem_binarith.
  intros.
  rewrite BC in SB.
  rewrite! cast_val_casted in SB by auto.
  destruct (classify_binarith t t).
  - destruct v1,v2; try congruence.
    simpl in BC.
    apply WC1 in SB; auto.
  - destruct v1,v2; try congruence.
    simpl in BC.
    apply WC2 in SB;auto.
  - destruct v1,v2; try congruence.
    simpl in BC.
    apply WC3 in SB; auto.
  - destruct v1,v2; try congruence.
    simpl in BC.
    apply WC4 in SB; auto.
  - discriminate.
Qed.

Lemma val_casted_cmp_ptr : forall m c v1 v2 v t,
    is_VBool t = true ->
    cmp_ptr m c v1 v2 = Some v ->
  val_casted v t.
Proof.
  unfold cmp_ptr.
  intros.
  destruct Archi.ptr64.
  destruct (Val.cmplu_bool (Memory.Mem.valid_pointer m) c v1 v2); try discriminate.
  inv H0. apply val_casted_is_VBool; auto.
  destruct (Val.cmpu_bool (Memory.Mem.valid_pointer m) c v1 v2); try discriminate.
  inv H0. apply val_casted_is_VBool; auto.
Qed.

Lemma val_casted_sem_cmp :
  forall o (v1 : val) (t1 : Ctypes.type) (v2 : val) (t2 t : Ctypes.type) (v : val) (m : Memory.Mem.mem),
    val_casted v1 t1 -> val_casted v2 t2 -> is_VBool t = true -> sem_cmp o v1 t1 v2 t2 m = Some v -> val_casted v t.
Proof.
  unfold sem_cmp. intros.
  destruct Archi.ptr64.
  destruct (classify_cmp t1 t2);
    try (eapply val_casted_cmp_ptr;eauto;fail).
  destruct v2 ; try discriminate ; eapply val_casted_cmp_ptr;eauto.
  destruct v1 ; try discriminate ; eapply val_casted_cmp_ptr;eauto.
  destruct v2 ; try discriminate ; eapply val_casted_cmp_ptr;eauto.
  destruct v1 ; try discriminate ; eapply val_casted_cmp_ptr;eauto.
  unfold sem_binarith in H2.
  destruct (sem_cast v1 t1 (binarith_type (classify_binarith t1 t2)) m);
    destruct (sem_cast v2 t2 (binarith_type (classify_binarith t1 t2)) m);
    destruct (classify_binarith t1 t2); try discriminate.
  - destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  - destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  - destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  - destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  - destruct (classify_cmp t1 t2).
    eapply val_casted_cmp_ptr;eauto.
    destruct v2 ; try discriminate;
      eapply val_casted_cmp_ptr;eauto.
    destruct v1 ; try discriminate;
      eapply val_casted_cmp_ptr;eauto.
    destruct v2 ; try discriminate;
      eapply val_casted_cmp_ptr;eauto.
    destruct v1 ; try discriminate;
      eapply val_casted_cmp_ptr;eauto.
  unfold sem_binarith in H2.
  destruct (sem_cast v1 t1 (binarith_type (classify_binarith t1 t2)) m);
    destruct (sem_cast v2 t2 (binarith_type (classify_binarith t1 t2)) m);
    destruct (classify_binarith t1 t2); try discriminate.
  + destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  + destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  + destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
  + destruct v0,v3 ; try discriminate. inv H2.
  eapply val_casted_is_VBool;eauto.
Qed.

Lemma vc_casted_binary_operation_correct : forall ge o v1 t1 v2 t2 t v m,
    Cop.val_casted v1 t1 ->
    Cop.val_casted v2 t2 ->
    vc_binary_operation_casted o t1 t2 t = true ->
    Cop.sem_binary_operation ge o v1 t1 v2 t2 m = Some v ->
  Cop.val_casted v t.
Proof.
  destruct o; simpl.
  - intros.
    unfold sem_add in H2.
    destruct (classify_add t1 t2) eqn:CL; try congruence.
    rewrite andb_true_iff in H1.
    destruct H1 as (T1 & T2).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H1 in *.
    assert (t2 = t) by congruence.
    rewrite H3 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor. reflexivity.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
  - intros.
    unfold sem_sub in H2.
    destruct (classify_sub t1 t2) eqn:CL; try congruence.
    rewrite andb_true_iff in H1.
    destruct H1 as (T1 & T2).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H1 in *.
    assert (t2 = t) by congruence.
    rewrite H3 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor. reflexivity.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
  - intros.
    unfold sem_mul in H2.
    rewrite andb_true_iff in H1.
    destruct H1 as (T1 & T2).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H1 in *.
    assert (t2 = t) by congruence.
    rewrite H3 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor. reflexivity.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
  - intros.
    unfold sem_div in H2.
    rewrite andb_true_iff in H1.
    destruct H1 as (T1 & T2).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H1 in *.
    assert (t2 = t) by congruence.
    rewrite H3 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros. simpl in H7. rewrite <- H4 in *.
      destruct s.
      destruct (Int.eq y Int.zero || Int.eq x (Int.repr Int.min_signed) && Int.eq y Int.mone); try congruence.
      inv H7. constructor. reflexivity.
      destruct (Int.eq y Int.zero) ; try congruence.
      inv H7. constructor. reflexivity.
    + intros. simpl in H7. rewrite <- H4 in *.
      destruct s.
      destruct (Int64.eq y Int64.zero || Int64.eq x (Int64.repr Int64.min_signed) && Int64.eq y Int64.mone); try congruence.
      inv H7. constructor.
      destruct (Int64.eq y Int64.zero) ; try congruence.
      inv H7. constructor.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7.
      constructor.
  - intros.
    unfold sem_mod in H2.
    rewrite andb_true_iff in H1.
    destruct H1 as (T1 & T2).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H1 in *.
    assert (t2 = t) by congruence.
    rewrite H3 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros. simpl in H7. rewrite <- H4 in *.
      destruct s.
      destruct (Int.eq y Int.zero || Int.eq x (Int.repr Int.min_signed) && Int.eq y Int.mone); try congruence.
      inv H7. constructor. reflexivity.
      destruct (Int.eq y Int.zero) ; try congruence.
      inv H7. constructor. reflexivity.
    + intros. simpl in H7. rewrite <- H4 in *.
      destruct s.
      destruct (Int64.eq y Int64.zero || Int64.eq x (Int64.repr Int64.min_signed) && Int64.eq y Int64.mone); try congruence.
      inv H7. constructor.
      destruct (Int64.eq y Int64.zero) ; try congruence.
      inv H7. constructor.
    + intros. simpl in H7. discriminate.
    + intros. simpl in H7. discriminate.
  - intros.
    unfold sem_and in H2.
    rewrite andb_true_iff in H1.
    destruct H1 as (T1 & T2).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H1 in *.
    assert (t2 = t) by congruence.
    rewrite H3 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7. constructor. reflexivity.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7. constructor.
    + intros. simpl in H7. discriminate.
    + intros. simpl in H7. discriminate.
  - intros.
    unfold sem_or in H2.
    rewrite andb_true_iff in H1.
    destruct H1 as (T1 & T2).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H1 in *.
    assert (t2 = t) by congruence.
    rewrite H3 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7. constructor. reflexivity.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7. constructor.
    + intros. simpl in H7. discriminate.
    + intros. simpl in H7. discriminate.
  - intros.
    unfold sem_xor in H2.
    rewrite andb_true_iff in H1.
    destruct H1 as (T1 & T2).
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t1); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t2); try discriminate;
    destruct (Ctypes.type_eq (binarith_type (classify_binarith t1 t2)) t); try discriminate.
    assert (t1 = t2) by congruence.
    rewrite H1 in *.
    assert (t2 = t) by congruence.
    rewrite H3 in *.
    eapply val_casted_sem_binarith ;eauto.
    congruence.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7. constructor. reflexivity.
    + intros. simpl in H7. rewrite <- H4 in *.
      inv H7. constructor.
    + intros. simpl in H7. discriminate.
    + intros. simpl in H7. discriminate.
  - unfold sem_shl.
    unfold sem_shift. intros.
    destruct (classify_shift t1 t2) eqn:CS.
    + rewrite! andb_true_iff in H1;
    destruct H1 as ((C1 & C2) & C3).
    destruct (Ctypes.type_eq t1 t); try discriminate;
    destruct (Ctypes.type_eq t2 t); try discriminate.
    destruct v1,v2 ; try discriminate.
    destruct (Int.ltu i0 Int.iwordsize); try discriminate.
    inv H2. apply is_Vint_casted; auto.
    + rewrite! andb_true_iff in H1;
        destruct H1 as ((C1 & C2) & C3).
      destruct v1,v2 ; try discriminate.
      destruct (Int64.ltu i0 Int64.iwordsize); try discriminate.
      inv H2. apply is_Vlong_casted; auto.
    + rewrite! andb_true_iff in H1;
        destruct H1 as ((C1 & C2) & C3).
      destruct v1,v2 ; try discriminate.
      destruct (Int64.ltu i0 (Int64.repr 32)); try discriminate.
      inv H2. apply is_Vint_casted; auto.
    + rewrite! andb_true_iff in H1;
        destruct H1 as ((C1 & C2) & C3).
      destruct v1,v2 ; try discriminate.
      destruct (Int.ltu i0 (Int64.iwordsize')); try discriminate.
      inv H2. apply is_Vlong_casted; auto.
    +  discriminate.
  - unfold sem_shr.
    unfold sem_shift. intros.
    destruct (classify_shift t1 t2) eqn:CS.
    + rewrite! andb_true_iff in H1;
    destruct H1 as ((C1 & C2) & C3).
    destruct (Ctypes.type_eq t1 t); try discriminate;
    destruct (Ctypes.type_eq t2 t); try discriminate.
    destruct v1,v2 ; try discriminate.
    destruct (Int.ltu i0 Int.iwordsize); try discriminate.
      destruct s ; inv H2; apply is_Vint_casted; auto.
    + rewrite! andb_true_iff in H1;
        destruct H1 as ((C1 & C2) & C3).
      destruct v1,v2 ; try discriminate.
      destruct (Int64.ltu i0 Int64.iwordsize); try discriminate.
      inv H2. apply is_Vlong_casted; auto.
    + rewrite! andb_true_iff in H1;
        destruct H1 as ((C1 & C2) & C3).
      destruct v1,v2 ; try discriminate.
      destruct (Int64.ltu i0 (Int64.repr 32)); try discriminate.
      inv H2. apply is_Vint_casted; auto.
    + rewrite! andb_true_iff in H1;
        destruct H1 as ((C1 & C2) & C3).
      destruct v1,v2 ; try discriminate.
      destruct (Int.ltu i0 (Int64.iwordsize')); try discriminate.
      inv H2. apply is_Vlong_casted; auto.
    +  discriminate.
  - intros.
    eapply val_casted_sem_cmp in H2; eauto.
  - intros.
    eapply val_casted_sem_cmp in H2; eauto.
  - intros.
    eapply val_casted_sem_cmp in H2; eauto.
  - intros.
    eapply val_casted_sem_cmp in H2; eauto.
  - intros.
    eapply val_casted_sem_cmp in H2; eauto.
  - intros.
    eapply val_casted_sem_cmp in H2; eauto.
Qed.

Definition vc_cast_casted (o:Ctypes.type) (d:Ctypes.type) :=
  match classify_cast o d with
  | cast_case_pointer => is_Vptr d
  | cast_case_i2l si  => true
  | _                 => false
  end.

Lemma val_casted_sem_cast : forall t1 t v v' m,
    vc_cast_casted t1 t = true ->
    sem_cast v t1 t m = Some v' ->
  val_casted v' t.
Proof.
  intros.
  unfold vc_cast_casted in H.
  unfold sem_cast in H0.
  destruct (classify_cast t1 t) eqn:CC; try discriminate.
  - destruct v ; try congruence.
    destruct Archi.ptr64 eqn:A; try congruence.
    inv H0.
    destruct t ; simpl in H ; try congruence.
    constructor. rewrite A in H.
    destruct i0; try congruence. constructor.
    reflexivity.
    constructor. auto.
    destruct Archi.ptr64 eqn:A; try congruence.
    inv H0.
    destruct t ; simpl in H ; try congruence.
    constructor. rewrite A in H.
    destruct i0; try congruence. discriminate H.
    constructor. constructor;auto.
    inv H0.
    eapply is_Vptr_casted; eauto.
  - destruct v; try congruence.
    inv H0.
    unfold classify_cast in CC.
    destruct t1; try discriminate.
    + destruct t; try discriminate.
      destruct i0; discriminate.
      destruct f; discriminate.
    + destruct t; try congruence.
      destruct i1;try congruence.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      constructor.
      destruct f; discriminate.
      destruct Archi.ptr64 eqn:A;
        try discriminate CC.
      econstructor; assumption.
    + destruct t ;
        try discriminate CC.
      destruct i0;
        try discriminate CC.
      destruct f; try discriminate.
    + destruct t ;
        try discriminate CC.
      destruct i0;
        try discriminate CC.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
      destruct f0; try discriminate.
      destruct f; try discriminate.
      destruct f; try discriminate.
    + destruct t ;
        try congruence.
      destruct i0;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct (Ctypes.intsize_eq
                  Ctypes.I8 Ctypes.I32);
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct (Ctypes.intsize_eq
           Ctypes.I16
           Ctypes.I32)
      ;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct (Ctypes.intsize_eq
           Ctypes.I32
           Ctypes.I32); try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      destruct Archi.ptr64 eqn:A;
        try congruence.
      constructor.
      destruct f. discriminate.
      discriminate.
    +  destruct t ; try congruence.
       destruct i0 ; try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq
           Ctypes.I8 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq Ctypes.I16 Ctypes.I32) ; try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq Ctypes.I32 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ;congruence.
       constructor.
       destruct f; congruence.
    + destruct t ; try congruence.
       destruct i0 ; try congruence.
       destruct Archi.ptr64 ; try congruence.
      destruct (Ctypes.intsize_eq Ctypes.I8 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq Ctypes.I16 Ctypes.I32) ; try congruence.
       destruct Archi.ptr64 ; try congruence.
       destruct (Ctypes.intsize_eq Ctypes.I32 Ctypes.I32); try congruence.
       destruct Archi.ptr64 ;congruence.
       constructor.
       destruct f; congruence.
    + destruct t ; try congruence.
       destruct i1 ; try congruence.
      destruct f; try congruence.
    +        destruct t ; try congruence.
             destruct i1 ; try congruence.
             destruct f ; try congruence.
Qed.

(**r this one should be another version of `Cop.val_casted` *)
Fixpoint vc_casted (inv: list (positive * Ctypes.type)) (e:expr) :=
  match e with
  | Econst_int _ t    => is_Vint t
  | Econst_float _ t  => is_Vfloat t
  | Econst_single _ t => is_Vsingle t
  | Econst_long _ t  => is_Vlong t
  | Evar _ _         => false
  | Etempvar v t     => existsb (fun x => if Ctypes.type_eq t (snd x) then Pos.eqb v (fst x) else false) inv
  | Ederef e _       => false (**r ysh: `false` -> `vc_casted inv e` *)
  | Eaddrof _ _       => false
  | Eunop o e t       => false
  | Ebinop o e1 e2 t    => vc_casted inv e1 && vc_casted inv e2 &&
                             vc_binary_operation_casted o (typeof e1) (typeof e2) t
  | Ecast e ty        => vc_casted inv e &&
                           vc_cast_casted (typeof e) ty
  | Efield e _ _      => false (**r ysh: `false` -> `vc_casted inv e` *)
  | Esizeof _ _       => false
  | Ealignof _ _      => false
  end.

(**r this Lemma tells the relation among vc_casted, exec_expr and `Cop.val_casted` *)
Lemma vc_casted_correct :
  forall inv ge le m a v
         (INV : var_casted_list inv le),
    vc_casted inv a = true ->
    exec_expr ge empty_env le m a = Some v ->
    Cop.val_casted v (typeof a).
Proof.
  induction a; simpl in *; try discriminate.
  - intros. inv H0.
    apply is_Vint_casted; auto.
  - intros. inv H0.
    apply is_Vfloat_casted; auto.
  - intros. inv H0.
    apply is_Vsingle_casted; auto.
  - intros. inv H0.
    apply is_Vlong_casted; auto.
  - intros.
    rewrite existsb_exists in H.
    destruct H as ((i',t'),(IN,P)).
    simpl in P.
    destruct (Ctypes.type_eq t t'); try congruence.
    apply Peqb_true_eq in P. subst.
    eapply INV;eauto.
  (*- (**r Ederef *)
    intros. (**r ysh: `old` -> `new` *)
    destruct (exec_expr ge empty_env le m a) eqn:E1; try discriminate.
    destruct v0 eqn: Hv0; try discriminate.
    specialize IHa with (Vptr b i).
    apply IHa in INV;[ idtac | assumption | reflexivity]. admit. *)
  - (**r Ebinop *)
    intros.
    destruct (exec_expr ge empty_env le m a1) eqn:E1; try discriminate.

    destruct (exec_expr ge empty_env le m a2) eqn:E2; try discriminate.
    repeat rewrite andb_true_iff in H.
    destruct H as ((H1 , H2), H3).
    eapply vc_casted_binary_operation_correct in H0; eauto.
  - intros.
    destruct (exec_expr ge empty_env le m a) eqn:E1; try discriminate.
    repeat rewrite andb_true_iff in H.
    destruct H as (H1 , H2).
    specialize (IHa _ INV H1 eq_refl).
    eapply val_casted_sem_cast in H0; eauto.
Qed.

Lemma check_cast : forall ge le inv m eargs lval targs
                          (INV   : var_casted_list inv le)
                          (LVAL : map_opt (exec_expr ge empty_env le m) eargs = Some lval)
                          (TARGS : List.map typeof eargs = List.map snd targs)
                          (CAST  : List.forallb (vc_casted inv) eargs = true)
  ,
    Forall2 (fun (v : val) (t : AST.ident * Ctypes.type) => Cop.val_casted v (snd t)) lval targs.
Proof.
  induction eargs.
  - simpl. intros. inv TARGS.
    inv LVAL. destruct targs. constructor.
    discriminate.
  - intros.
    simpl in TARGS. simpl in LVAL.
    destruct (exec_expr ge empty_env le m a) eqn:E ; try discriminate.
    destruct (map_opt (exec_expr ge empty_env le m) eargs) eqn:M ; try discriminate.
    inv LVAL. destruct targs. discriminate.
    inv TARGS.
    simpl in CAST.
    rewrite andb_true_iff in CAST.
    destruct CAST as (C1 & C2).
    econstructor ; eauto.
    rewrite <- H0.
    eapply vc_casted_correct;eauto.
Qed.

Lemma var_casted_list_map_fst : forall st m le var_inv,
    Forall (match_elt st m le) var_inv ->
  var_casted_list (map fst var_inv) le.
Proof.
 unfold var_casted_list.
 intros.
 rewrite Forall_forall in H.
 rewrite in_map_iff in H0.
 destruct H0 as (((i1,t1),r1), (EQ , IN)).
 simpl in EQ. inv EQ.
 apply H in IN.
 unfold match_elt in IN.
 simpl in IN.
 rewrite H1 in IN.
 tauto.
Qed.

Fixpoint type_of_list (l : list Ctypes.type) : Ctypes.typelist :=
  match l with
  | nil => Ctypes.Tnil
  | cons e l => Ctypes.Tcons e (type_of_list l)
  end.

Section S.
  Variable p : program.
  Variable fn: Clight.function.

  Lemma correct_statement_call :
    forall  (has_cast : bool) args res (f : arrow_type args (M res)) is_pure a loc
           vres fvar targs ti eargs tres  fct modifies
           (FS : Globalenvs.Genv.find_symbol (globalenv (semantics2 p)) fvar = Some loc)
           (FF : Globalenvs.Genv.find_funct (globalenv (semantics2 p))
                                            (Vptr loc Ptrofs.zero) = Some (Ctypes.Internal fct))
           (TF : type_of_fundef (Ctypes.Internal fct) =
                   Ctypes.Tfunction targs ti AST.cc_default)

           (match_arg : DList.t (fun x : Type => x -> val -> State.state -> Memory.Mem.mem -> Prop) (all_args args is_pure))
           (match_res : res -> val  -> State.state -> Memory.Mem.mem -> Prop)
           (C : forall a, correct_function3 p args res f fct modifies is_pure match_arg match_res a)
           (var_inv : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
           (le : temp_env) (m : Memory.Mem.mem) (st : State.state)
           (VARINV: var_inv_preserve var_inv match_res modifies  le)
           (TI    : ti = fn_return fct)
           (TARGS : targs = type_of_list (map typeof eargs))
           (TARGS1 : map typeof eargs = map snd (fn_params fct))
           (NOTIN1 : ~In vres   (map  (fun x  => fst (fst x)) var_inv))
           (NOTIN2 : ~In tres   (map  (fun x  => fst (fst x)) var_inv))
           (CASTED  : List.forallb (vc_casted (List.map fst var_inv)) eargs = true)
           (LENEARGS : List.length eargs = (List.length (all_args args is_pure)))
           (LVAL  :
             Forall (match_elt st m le) var_inv ->
             exists lval,
               map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs = Some lval
            /\ forall (LEN :List.length lval = (List.length (all_args args is_pure))),
      DList.Forall2 (fun (a : Type) (R : a -> val -> State.state -> Memory.Mem.mem -> Prop) (X : a * val) => R (fst X) (snd X) st m) match_arg
                    (DList.zip (all_args_list args is_pure a) (DList.of_list_sl lval (all_args args is_pure) LEN)))
    ,
      correct_statement p res (app f a) fn
    (Ssequence
       (Scall (Some tres)
          (Evar fvar
             (Ctypes.Tfunction targs ti AST.cc_default))
          eargs)
       (Sset vres (if has_cast then
          (Ecast (Etempvar tres ti) ti) else Etempvar tres ti)))
    modifies (pre  var_inv) (post  match_res var_inv (vres,ti)) st le m.
  Proof.
    repeat intro.
    rename H into PRE.
    destruct (C a).
    specialize (fn_eval_ok4  st).
    destruct (app f a st); try congruence.
    destruct p0 as (v',st').
    intros s' k k' K.
    unfold pre in PRE. unfold match_temp_env in PRE.
    destruct (LVAL PRE) as (lval & MAP & ALL).
    clear LVAL.
    assert (LEN : Datatypes.length lval = Datatypes.length (all_args args is_pure)).
    {
      apply length_map_opt in MAP.
      rewrite <- MAP.
      rewrite LENEARGS.
      reflexivity.
      }
      specialize (ALL LEN).
      specialize (fn_eval_ok4 (DList.of_list_sl lval (all_args args is_pure) LEN)
                            (Kcall (Some tres) fn empty_env le
                                   (Kseq (Sset vres (if has_cast
                then Ecast (Etempvar tres ti) ti
                                                     else Etempvar tres ti)) k)) m).
(*
    assert (MA : DList.Forall2 (fun (a : Type) (R : a -> val -> State.state -> Memory.Mem.mem -> Prop) (X : a * val) => R (fst X) (snd X) st m) match_arg
                  (DList.zip (all_args_list args is_pure a) (DList.of_list_sl lval (all_args args is_pure) LEN))).
    {
      unfold match_temp_env in PRE.
      rewrite Forall_forall in PRE.
      revert PRE.
      revert LVAL VAR.
      clear.
      revert lval LEN.
      revert  lvar var_inv.
      revert match_arg.
      generalize ((all_args_list args is_pure a)) as a'.
      generalize (all_args args is_pure) as args'.
      induction a'.
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
        generalize (PRE _ H).
        unfold match_elt.
        change AST.ident with positive in *.
        simpl.
        destruct (Maps.PTree.get (fst p) le) eqn:G;try discriminate.
        destruct (map_opt
             (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le)
             lvar) eqn:M ; try discriminate.
        inv LVAL.
        split. tauto.
        eapply IHa'; eauto.
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
      revert PRE.
      assert (P: incl lvar  (map fst var_inv)).
      {
        revert VAR.
        rewrite <- (map_fst_combine lvar (list_rel (all_args args is_pure)
                                                   match_arg (all_args_list args is_pure a))) at 2.
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
        rewrite Forall_forall in PRE.
        apply PRE in IN.
        unfold match_elt in IN.
        change AST.ident with positive in *.
        rewrite FST in *.
        rewrite G in IN.
        tauto.
        apply IHlvar; auto.
        eapply incl_cons_inv; eauto.
    } *)
    assert (EQ: lval = (DList.to_list (fun (_ : Type) (v : val) => v)
                                   (DList.of_list_sl lval (all_args args is_pure) LEN))).
    { apply (DList.to_list_of_list_sl ). }
(*    assert (MA2:= MA').
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
    } *)
    (*rewrite EQ in MA''.*)
    assert (ALLCASTED : Forall2 (fun (v : val) (t : AST.ident * Ctypes.type) => val_casted v (snd t))
    lval (fn_params fct)).
    {
      eapply check_cast; eauto.
      eapply var_casted_list_map_fst; eauto.
    }
    destruct (fn_eval_ok4 ALL) as (v1 & m1 & t1 & STAR & RES' & CAST  &MOD).
    rewrite <- EQ. assumption.
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
      revert PRE CASTED TARGS MAP.
      clear. intro. revert lval targs.
      induction eargs.
      - simpl. intros. inv MAP.
        constructor.
      - simpl.
        intros. subst.
        destruct (exec_expr (Clight.globalenv p) empty_env le m a) eqn:E; try congruence.
        destruct (map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs) eqn:MO; try discriminate.
        inv MAP.
        rewrite andb_true_iff in CASTED.
        destruct CASTED as (C1 & C2).
        econstructor; eauto.
        apply eval_expr_eval in E.
        eauto.
        apply Cop.cast_val_casted.
        eapply vc_casted_correct; eauto.
        eapply var_casted_list_map_fst; eauto.
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
      revert PRE.
      eapply VARINV. auto.
      eauto.
  Qed.

End S.

Section S.
  Variable p : program.
  Variable fn: Clight.function.

  Lemma correct_statement_call_none :
    forall args  (f : arrow_type args (M unit)) is_pure a loc
           fvar targs ti eargs fct modifies
           (FS : Globalenvs.Genv.find_symbol (globalenv (semantics2 p)) fvar = Some loc)
           (FF : Globalenvs.Genv.find_funct (globalenv (semantics2 p))
                                            (Vptr loc Ptrofs.zero) = Some (Ctypes.Internal fct))
           (TF : type_of_fundef (Ctypes.Internal fct) =
                   Ctypes.Tfunction targs ti AST.cc_default)

           (match_arg : DList.t (fun x : Type => x -> val -> State.state -> Memory.Mem.mem -> Prop) (all_args args is_pure))
           (match_res : unit -> val  -> State.state -> Memory.Mem.mem -> Prop)
           (C : forall a, correct_function3 p args unit f fct modifies is_pure match_arg match_res a)
           (match_res_Vundef : forall x v st m, match_res x v st m -> v = Vundef)

           (var_inv : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
           (le : temp_env) (m : Memory.Mem.mem) (st : State.state)
           (VARINV: var_inv_preserve var_inv match_res modifies  le)
           (TI    : ti = fn_return fct)
           (TARGS : targs = type_of_list (map typeof eargs))
           (TARGS1 : map typeof eargs = map snd (fn_params fct))
           (CASTED  : List.forallb (vc_casted (List.map fst var_inv)) eargs = true)
           (LENEARGS : List.length eargs = (List.length (all_args args is_pure)))
           (LVAL  :
             Forall (match_elt st m le) var_inv ->
             exists lval,
               map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs = Some lval
            /\ forall (LEN :List.length lval = (List.length (all_args args is_pure))),
      DList.Forall2 (fun (a : Type) (R : a -> val -> State.state -> Memory.Mem.mem -> Prop) (X : a * val) => R (fst X) (snd X) st m) match_arg
                    (DList.zip (all_args_list args is_pure a) (DList.of_list_sl lval (all_args args is_pure) LEN)))
    ,
      correct_statement p unit (app f a) fn
       (Scall None
          (Evar fvar
             (Ctypes.Tfunction targs ti AST.cc_default))
          eargs)
    modifies (pre  var_inv) (post_unit match_res  var_inv) st le m.
  Proof.
    repeat intro.
    rename H into PRE.
    destruct (C a).
    specialize (fn_eval_ok4  st).
    destruct (app f a st); try congruence.
    destruct p0 as (v',st').
    intros s' k k' K.
    unfold pre in PRE. unfold match_temp_env in PRE.
    destruct (LVAL PRE) as (lval & MAP & ALL).
    clear LVAL.
    assert (LEN : Datatypes.length lval = Datatypes.length (all_args args is_pure)).
    {
      apply length_map_opt in MAP.
      rewrite <- MAP.
      rewrite LENEARGS.
      reflexivity.
      }
      specialize (ALL LEN).
      specialize (fn_eval_ok4 (DList.of_list_sl lval (all_args args is_pure) LEN)
                            (Kcall None fn empty_env le
                                    k) m).
    assert (EQ: lval = (DList.to_list (fun (_ : Type) (v : val) => v)
                                   (DList.of_list_sl lval (all_args args is_pure) LEN))).
    { apply (DList.to_list_of_list_sl ). }
    assert (ALLCASTED : Forall2 (fun (v : val) (t : AST.ident * Ctypes.type) => val_casted v (snd t))
    lval (fn_params fct)).
    {
      eapply check_cast; eauto.
      eapply var_casted_list_map_fst; eauto.
    }
    destruct (fn_eval_ok4 ALL) as (v1 & m1 & t1 & STAR & RES' & CAST  &MOD).
    rewrite <- EQ. assumption.
    assert (v1 = Vundef). eapply match_res_Vundef; eauto.
    subst.
    do 3 eexists.
    split.
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
      revert PRE CASTED  MAP.
      clear. intro. revert lval.
      induction eargs.
      - simpl. intros. inv MAP.
        constructor.
      - simpl.
        intros. subst.
        destruct (exec_expr (Clight.globalenv p) empty_env le m a) eqn:E; try congruence.
        destruct (map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs) eqn:MO; try discriminate.
        inv MAP.
        rewrite andb_true_iff in CASTED.
        destruct CASTED as (C1 & C2).
        econstructor; eauto.
        apply eval_expr_eval in E.
        eauto.
        apply Cop.cast_val_casted.
        eapply vc_casted_correct; eauto.
        eapply var_casted_list_map_fst; eauto.
    }
    eapply star_trans.
    rewrite <- EQ in STAR.
    eauto.
    unfold call_cont.
    eapply star_step.
    econstructor ; eauto.
    unfold set_opttemp.
    eapply star_step.
    eapply apply_cont_cont; eauto.
    apply star_refl.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    unfold post_unit.
    repeat split; auto.
    unfold match_temp_env.
    revert PRE.
    eapply VARINV. auto.
    eauto.
  Qed.

End S.



Section S.
  Variable p : program.
  Variable fn: Clight.function.

  Lemma correct_body_call_ret :
    forall  (has_cast : bool) args res (f : arrow_type args (M res)) is_pure a loc
           (*vres*) fvar targs ti eargs tres  fct modifies
           (FS : Globalenvs.Genv.find_symbol (globalenv (semantics2 p)) fvar = Some loc)
           (FF : Globalenvs.Genv.find_funct (globalenv (semantics2 p))
                                            (Vptr loc Ptrofs.zero) = Some (Ctypes.Internal fct))
           (TF : type_of_fundef (Ctypes.Internal fct) =
                   Ctypes.Tfunction targs ti AST.cc_default)

           (match_arg : DList.t (fun x : Type => x -> val -> State.state -> Memory.Mem.mem -> Prop) (all_args args is_pure))
           (match_res : res -> val  -> State.state -> Memory.Mem.mem -> Prop)
           (C : correct_function3 p args res f fct modifies is_pure match_arg match_res a)
           (var_inv : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
           (le : temp_env) (m : Memory.Mem.mem) (st : State.state)
           (VARINV: var_inv_preserve var_inv match_res modifies  le)
           (TI    : ti = fn_return fct)
           (TIN    : ti = fn_return fn)
           (TARGS : targs = type_of_list (map typeof eargs))
           (TARGS1 : map typeof eargs = map snd (fn_params fct))
(*           (NOTIN1 : ~In vres   (map  (fun x  => fst (fst x)) var_inv))
           (NOTIN2 : ~In tres   (map  (fun x  => fst (fst x)) var_inv)) *)
           (CASTED  : List.forallb (vc_casted (List.map fst var_inv)) eargs = true)
           (LENEARGS : List.length eargs = (List.length (all_args args is_pure)))
           (LVAL  :
             Forall (match_elt st m le) var_inv ->
             exists lval,
               map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs = Some lval
            /\ forall (LEN :List.length lval = (List.length (all_args args is_pure))),
      DList.Forall2 (fun (a : Type) (R : a -> val -> State.state -> Memory.Mem.mem -> Prop) (X : a * val) => R (fst X) (snd X) st m) match_arg
                    (DList.zip (all_args_list args is_pure a) (DList.of_list_sl lval (all_args args is_pure) LEN)))
    ,
      correct_body p res (app f a) fn
    (Ssequence
       (Scall (Some tres)
          (Evar fvar
             (Ctypes.Tfunction targs ti AST.cc_default))
          eargs)
       (Sreturn (Some (if has_cast then
                   (Ecast (Etempvar tres ti) ti) else Etempvar tres ti))))
    modifies var_inv match_res  st le m.
  Proof.
    repeat intro.
    rename H into PRE.
    destruct C.
    specialize (fn_eval_ok4  st).
    destruct (app f a st); try congruence.
    destruct p0 as (v',st').
    intros k.
    destruct (LVAL PRE) as (lval & MAP & ALL).
    clear LVAL.
    assert (LEN : Datatypes.length lval = Datatypes.length (all_args args is_pure)).
    {
      apply length_map_opt in MAP.
      rewrite <- MAP.
      rewrite LENEARGS.
      reflexivity.
      }
      specialize (ALL LEN).
      specialize (fn_eval_ok4 (DList.of_list_sl lval (all_args args is_pure) LEN)
                            (Kcall (Some tres) fn empty_env le
                                   (Kseq (Sreturn
                (Some
                   (if has_cast
                    then Ecast (Etempvar tres ti) ti
                    else Etempvar tres ti))) k)) m).
(*
    assert (MA : DList.Forall2 (fun (a : Type) (R : a -> val -> State.state -> Memory.Mem.mem -> Prop) (X : a * val) => R (fst X) (snd X) st m) match_arg
                  (DList.zip (all_args_list args is_pure a) (DList.of_list_sl lval (all_args args is_pure) LEN))).
    {
      unfold match_temp_env in PRE.
      rewrite Forall_forall in PRE.
      revert PRE.
      revert LVAL VAR.
      clear.
      revert lval LEN.
      revert  lvar var_inv.
      revert match_arg.
      generalize ((all_args_list args is_pure a)) as a'.
      generalize (all_args args is_pure) as args'.
      induction a'.
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
        generalize (PRE _ H).
        unfold match_elt.
        change AST.ident with positive in *.
        simpl.
        destruct (Maps.PTree.get (fst p) le) eqn:G;try discriminate.
        destruct (map_opt
             (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le)
             lvar) eqn:M ; try discriminate.
        inv LVAL.
        split. tauto.
        eapply IHa'; eauto.
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
      revert PRE.
      assert (P: incl lvar  (map fst var_inv)).
      {
        revert VAR.
        rewrite <- (map_fst_combine lvar (list_rel (all_args args is_pure)
                                                   match_arg (all_args_list args is_pure a))) at 2.
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
        rewrite Forall_forall in PRE.
        apply PRE in IN.
        unfold match_elt in IN.
        change AST.ident with positive in *.
        rewrite FST in *.
        rewrite G in IN.
        tauto.
        apply IHlvar; auto.
        eapply incl_cons_inv; eauto.
    } *)
    assert (EQ: lval = (DList.to_list (fun (_ : Type) (v : val) => v)
                                   (DList.of_list_sl lval (all_args args is_pure) LEN))).
    { apply (DList.to_list_of_list_sl ). }
(*    assert (MA2:= MA').
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
    } *)
    (*rewrite EQ in MA''.*)
    assert (ALLCASTED : Forall2 (fun (v : val) (t : AST.ident * Ctypes.type) => val_casted v (snd t))
    lval (fn_params fct)).
    {
      eapply check_cast; eauto.
      eapply var_casted_list_map_fst; eauto.
    }
    destruct (fn_eval_ok4 ALL) as (v1 & m1 & t1 & STAR & RES' & CAST  &MOD).
    rewrite <- EQ. assumption.
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
      revert PRE CASTED TARGS MAP.
      clear. intro. revert lval targs.
      induction eargs.
      - simpl. intros. inv MAP.
        constructor.
      - simpl.
        intros. subst.
        destruct (exec_expr (Clight.globalenv p) empty_env le m a) eqn:E; try congruence.
        destruct (map_opt (exec_expr (Clight.globalenv p) empty_env le m) eargs) eqn:MO; try discriminate.
        inv MAP.
        rewrite andb_true_iff in CASTED.
        destruct CASTED as (C1 & C2).
        econstructor; eauto.
        apply eval_expr_eval in E.
        eauto.
        apply Cop.cast_val_casted.
        eapply vc_casted_correct; eauto.
        eapply var_casted_list_map_fst; eauto.
    }
    eapply star_trans.
    rewrite <- EQ in STAR.
    eauto.
    unfold call_cont.
    eapply star_step.
    econstructor ; eauto.
    econstructor ; eauto.
    econstructor; eauto.
    econstructor ; eauto.
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
    rewrite TI in *.
    rewrite TIN in *.
    unfold typeof.
    destruct has_cast.
    eapply cast_val_casted; eauto.
    eapply cast_val_casted; eauto.
    reflexivity.
    econstructor;eauto.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    repeat split; auto.
    congruence.
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

  Variable match_res1 : res1 -> val -> State.state -> Memory.Mem.mem -> Prop.

  Variable match_res2 : res2  -> val -> State.state -> Memory.Mem.mem -> Prop.

  Lemma correct_statement_seq_body :
    forall (s1 s2:Clight.statement) vret ti
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m
      (C1 : correct_statement p res1 f1 fn s1 modifies (pre  var_inv) (post  match_res1 var_inv (vret,ti)) st le m)
      (C2 : forall le m st x, correct_body p res2 (f2 x) fn s2 modifies  ((vret,ti,match_res1 x):: var_inv) match_res2 st le m)
    ,
             correct_body p  res2 (bindM f1 f2) fn
             (Ssequence s1 s2) modifies  var_inv match_res2 st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold bindM.
    unfold correct_statement in C1.
    destruct (f1 st) eqn:F1 ; try congruence.
    destruct p0 as (v1,st1).
    destruct (f2 v1 st1) eqn:F2; try congruence.
    destruct p0 as (v2,st2).
    intros.
    destruct (C1 PRE s2 (Kseq s2 k) k  eq_refl) as
      (le'& m' & t & ST & MR & MOD).
    specialize (C2 le' m' st1 v1).
    unfold correct_body in C2.
    rewrite F2 in C2.
    assert (PRE2 : pre  ((vret, ti, match_res1 v1) :: var_inv) st1 le' m').
    {
      unfold pre. unfold post in MR.
      tauto.
    }
    destruct (C2  PRE2  k) as
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

  Lemma correct_statement_seq_body_nil :
    forall (s1 s2:Clight.statement) vret ti
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m
      (C1 : correct_statement p res1 f1 fn s1 nil (pre  var_inv) (post  match_res1 var_inv (vret,ti)) st le m)
      (C2 : forall le m st x, correct_body p res2 (f2 x) fn s2 modifies  ((vret,ti,match_res1 x):: var_inv) match_res2 st le m)
    ,
             correct_body p  res2 (bindM f1 f2) fn
             (Ssequence s1 s2) modifies  var_inv match_res2 st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold bindM.
    unfold correct_statement in C1.
    destruct (f1 st) eqn:F1 ; [| constructor].
    destruct p0 as (v1,st1).
    destruct (f2 v1 st1) eqn:F2; [| constructor].
    destruct p0 as (v2,st2).
    intros.
    destruct (C1 PRE s2 (Kseq s2 k) k  eq_refl) as
      (le'& m' & t & ST & MR & MOD).
    specialize (C2 le' m' st1 v1).
    unfold correct_body in C2.
    rewrite F2 in C2.
    assert (PRE2 : pre  ((vret, ti, match_res1 v1) :: var_inv) st1 le' m').
    {
      unfold pre. unfold post in MR.
      tauto.
    }
    destruct (C2  PRE2  k) as
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
    unfold unmodifies_effect in MOD.
    subst.
    destruct MR2 as (MR2_1 & MR2_2 & MR2_3).
    destruct MOD; subst.
    assumption.
  Qed.

  Lemma correct_statement_seq_body_pure :
    forall (s1 s2:Clight.statement) vret ti
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m
      (C1 : correct_statement p res1 f1 fn s1 nil (pre  var_inv) (post  match_res1 var_inv (vret,ti)) st le m)
      (C2 : forall le st x, correct_body p res2 (f2 x) fn s2 nil  ((vret,ti,match_res1 x):: var_inv) match_res2 st le m)
    ,
             correct_body p  res2 (bindM f1 f2) fn
             (Ssequence s1 s2) nil  var_inv match_res2 st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold bindM.
    unfold correct_statement in C1.
    destruct (f1 st) eqn:F1 ; try congruence.
    destruct p0 as (v1,st1).
    destruct (f2 v1 st1) eqn:F2; try congruence.
    destruct p0 as (v2,st2).
    intros.
    destruct (C1 PRE s2 (Kseq s2 k) k  eq_refl) as
      (le'& m' & t & ST & MR & MOD).
    unfold unmodifies_effect in MOD; simpl in MOD.
    destruct MOD.
    subst m'.
    specialize (C2 le' st1 v1).
    unfold correct_body in C2.
    rewrite F2 in C2.
    assert (PRE2 : pre  ((vret, ti, match_res1 v1) :: var_inv) st1 le' m).
    {
      unfold pre. unfold post in MR.
      tauto.
    }
    destruct (C2  PRE2  k) as
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
    destruct MR2 as (_ & _ & MR2); unfold unmodifies_effect in MR2; destruct MR2; subst; reflexivity.
    destruct MR2 as (_ & _ & MR2); unfold unmodifies_effect in MR2; destruct MR2; subst; reflexivity.
    all: constructor.
  Qed.



End S.

Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable f1 : M unit.

  Variable res2 : Type.

  Variable f2 : unit -> (M res2).

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable modifies : list block.

  Variable match_res1 : unit -> val -> State.state -> Memory.Mem.mem -> Prop.

  Variable match_res2 : res2  -> val -> State.state -> Memory.Mem.mem -> Prop.

  Lemma correct_statement_seq_body_unit :
    forall (s1 s2:Clight.statement)
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m
      (C1 : correct_statement p unit f1 fn s1 modifies (pre  var_inv) (post_unit  match_res1 var_inv) st le m)
      (C2 : forall le m st x, correct_body p res2 (f2 x) fn s2 modifies  var_inv match_res2 st le m)
    ,
             correct_body p  res2 (bindM f1 f2) fn
             (Ssequence s1 s2) modifies  var_inv match_res2 st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold bindM.
    unfold correct_statement in C1.
    destruct (f1 st) eqn:F1 ; try congruence.
    destruct p0 as (v1,st1).
    destruct (f2 v1 st1) eqn:F2; try congruence.
    destruct p0 as (v2,st2).
    intros.
    destruct (C1 PRE s2 (Kseq s2 k) k  eq_refl) as
      (le'& m' & t & ST & MR & MOD).
    specialize (C2 le' m' st1 v1).
    unfold correct_body in C2.
    rewrite F2 in C2.
    assert (PRE2 : pre  var_inv st1 le' m').
    {
      unfold pre. unfold post_unit in MR.
      tauto.
    }
    destruct (C2  PRE2  k) as
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

Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f : M res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop.


  Lemma correct_statement_seq_body_drop :
    forall (s1 s2:Clight.statement)
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m
      (C2 : forall le m st, correct_body p res f fn s1 modifies  var_inv match_res st le m)
    ,
             correct_body p  res f fn
             (Ssequence s1 s2) modifies  var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold correct_body in C2.
    specialize (C2 le m st PRE).
    destruct (f st) eqn:F1 ; try congruence.
    destruct p0 as (v1,st1).
    intros.
    destruct (C2 (Kseq s2 k)) as (vr & mr & tr & STAR & MR & VC & UNM).
    exists vr, mr,tr.
    repeat split; auto.
    eapply star_step.
    econstructor;eauto.
    eauto. reflexivity.
  Qed.



End S.



Lemma bind_id_left : forall {A: Type} (f: M A) x  , f x = bindM (returnM tt) (fun _ => f) x.
Proof.
  intros.
  unfold bindM.
  unfold returnM.
  reflexivity.
Qed.

Lemma correct_body_id : forall p (res:Type) (f: M res) fn (s:statement) md pr pst st le m,
    correct_body p res (bindM (returnM tt) (fun _ => f)) fn s md pr pst st le m ->
    correct_body p res f fn s md pr pst st le m.
Proof.
  repeat intro.
  unfold correct_body in H.
  rewrite <- bind_id_left in H.
  apply H.
  apply H0.
Qed.

Lemma bind_id_right : forall {A: Type} (f: M A) x  , f x = bindM f returnM x.
Proof.
  intros.
  unfold bindM.
  unfold returnM.
  destruct (f x); auto. destruct p; auto.
Qed.

Lemma correct_body_id_right : forall p (res:Type) (f: M res) fn (s:statement) md pr pst st le m,
    correct_body p res (bindM f returnM) fn s md pr pst st le m ->
    correct_body p res f fn s md pr pst st le m.
Proof.
  repeat intro.
  unfold correct_body in H.
  rewrite <- bind_id_right in H.
  apply H; auto.
Qed.




Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f : M res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_res1 : unit -> val -> State.state -> Memory.Mem.mem -> Prop.

  Variable match_res2 : res  -> val -> State.state -> Memory.Mem.mem -> Prop.

  Lemma correct_statement_seq_set :
    forall (r:AST.ident) (e:expr) (s2:Clight.statement) (*vret ti*)
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m 
      (EVAL: match_temp_env var_inv le st m ->
             exists v, exec_expr (globalenv (semantics2 p)) empty_env le m e = Some v  /\
                         match_res1 tt v st m /\val_casted v (typeof e))
      (FR     :   ~ In r (map (fun x => fst (fst x)) var_inv))
     (C2 : forall le m st x, correct_body p res f fn s2 modifies  ((r,typeof e,match_res1 x):: var_inv) match_res2 st le m)
    ,
             correct_body p  res f fn
             (Ssequence (Sset r e) s2) modifies  var_inv match_res2 st le m.
  Proof.
    intros.
    apply correct_body_id.
    eapply correct_statement_seq_body.
    instantiate (1 := typeof e).
    instantiate (1 := r).
    instantiate (1:= match_res1).
    repeat intro.
    unfold pre in H.
    specialize (EVAL H).
    destruct EVAL as (v & EVAL & MR & CAST).
    apply eval_expr_eval in EVAL.
    repeat eexists.
    econstructor. econstructor.
    eauto.
    econstructor.
    eapply apply_cont_cont. eauto.
    econstructor ; eauto.
    reflexivity.
    reflexivity.
    unfold post.
    apply match_temp_env_cons.
    unfold match_elt.
    simpl.
    rewrite Maps.PTree.gss.
    split ; auto.
    eapply match_temp_env_set; auto.
    destruct modifies.
    unfold unmodifies_effect; split; reflexivity.
    unfold unmodifies_effect.
    intros; reflexivity.
    intros.
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

  Variable match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop.


  Lemma correct_statement_if_body :
    forall (s1 s2:Clight.statement) (x:bool) vr
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m
      (IN : In ((vr, Clightdefs.tbool, (stateless match_bool x))) var_inv)
      (C1 : correct_body p res (if x then f1 else f2) fn (if x then s1 else s2)
                         modifies  var_inv match_res st
                         le m)
    ,

      correct_body p res (if x then f1 else f2) fn
                          (Sifthenelse (Etempvar vr Clightdefs.tbool)
                                       s1 s2) modifies  var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold correct_body in C1.
    specialize(C1 PRE).
    assert (GET : Maps.PTree.get vr le = Some (Vint (if x then Int.one else Int.zero))).
    {
      unfold match_temp_env in PRE.
      rewrite Forall_forall in PRE.
      apply PRE in IN.
      unfold match_elt in IN.
      simpl in IN.
      destruct (Maps.PTree.get vr le).
      destruct IN.
      unfold stateless,match_bool in H.
      subst. reflexivity.
      tauto.
    }
    destruct x;auto.
    - destruct (f1 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k) as (v1 & m1 & t1 & STAR & I1 & I2 & I3).
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
    - destruct (f2 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k) as (v1 & m1 & t1 & STAR & I1 & I2 & I3).
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
  Qed.

End S.

Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f1 f2 : M res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop.

  Lemma correct_statement_if_body_expr :
    forall (s1 s2:Clight.statement) (x:bool) e
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m
      (C1 : correct_body p res (if x then f1 else f2) fn (if x then s1 else s2)
                         modifies  var_inv match_res st
                         le m)
      (TY : classify_bool (typeof e) = bool_case_i)
      (EVAL: match_temp_env var_inv le st m -> exec_expr (globalenv (semantics2 p)) empty_env le m e = Some (Val.of_bool x))
    ,

      correct_body p res (if x then f1 else f2) fn
                          (Sifthenelse e
                                       s1 s2) modifies  var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold correct_body in C1.
    specialize(C1 PRE).
    destruct x;auto.
    - destruct (f1 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k) as (v1 & m1 & t1 & STAR & I1 & I2 & I3).
      specialize (EVAL PRE).
      apply eval_expr_eval in EVAL.
      exists v1,m1,t1.
      repeat split.
      eapply star_step.
      econstructor ;eauto.
      unfold bool_val.
      simpl.
      rewrite TY.
      reflexivity.
      change (negb (Int.eq Int.one Int.zero)) with true.
      simpl.
      eauto.
      reflexivity.
      auto. auto.
      auto.
    - destruct (f2 st) eqn:F1; try auto.
      destruct p0 as (v',st').
      intros.
      destruct (C1 k) as (v1 & m1 & t1 & STAR & I1 & I2 & I3).
      specialize (EVAL PRE).
      apply eval_expr_eval in EVAL.
      exists v1,m1,t1.
      repeat split.
      eapply star_step.
      econstructor ;eauto.
      unfold bool_val.
      rewrite TY.
      reflexivity.
      change (negb (Int.eq Int.one Int.zero)) with true.
      simpl.
      eauto.
      reflexivity.
      auto. auto.
      auto.
  Qed.

End S.

Section S.
  (** The program contains our function of interest [fn] *)
  Variable p : Clight.program.

  Variable res : Type.

  Variable f : M res.

  (* [fn] is the Cligth function which has the same behaviour as [f] *)
  Variable fn : Clight.function.

  Variable match_res : res -> val -> State.state -> Memory.Mem.mem -> Prop.


  Lemma correct_statement_switch :
    forall (n:Z) e l
           (modifies : list block)
           (var_inv  : list (positive * Ctypes.type * (val -> State.state -> Memory.Mem.mem -> Prop)))
      st le m

      (C1 : correct_body p res f fn (seq_of_labeled_statement (select_switch n l))
                         modifies  var_inv match_res st
                         le m)
      (TY : classify_switch (typeof e) = switch_case_i)
      (EVAL: match_temp_env var_inv le st m ->
               exec_expr (globalenv (semantics2 p)) empty_env le m e = Some (Vint (Int.repr n)))
      (SMALL : 0 <= n < Int.modulus)
    ,

      correct_body p res f fn
                          (Sswitch e l) modifies  var_inv match_res st le m.
  Proof.
    intros.
    unfold correct_body.
    intros PRE.
    unfold correct_body in C1.
    specialize(C1 PRE).
    specialize (EVAL PRE).
    destruct (f st) eqn:F1; try auto.
    destruct p0 as (v',st').
    intros.
    destruct (C1 (Kswitch k)) as (v1 & m1 & t1 & STAR & I1 & I2 & I3).
    apply eval_expr_eval in EVAL.
    exists v1,m1,t1.
    repeat split.
    eapply star_step.
    econstructor ;eauto.
    unfold sem_switch_arg.
    rewrite TY. reflexivity.
    rewrite Int.unsigned_repr_eq.
    rewrite Zmod_small by auto.
    eauto.
    reflexivity.
    auto.
    auto.
    auto.
  Qed.

End S.

Lemma correct_body_Sreturn_None :
  forall p fn modifies inv
         (match_res : unit -> val -> State.state -> Memory.Mem.mem -> Prop)
         st le m,
    (match_temp_env inv le st m -> match_res tt Vundef st m) ->
    (fn_return fn = Ctypes.Tvoid) ->

    correct_body p unit (returnM tt) fn (Sreturn None) modifies
               inv match_res st le m.
Proof.
  repeat intro.
  eexists Vundef.
  exists m. exists Events.E0.
  repeat split.
  eapply star_step.
  econstructor ; eauto.
  reflexivity.
  eapply star_refl.
  reflexivity.
  auto.
  rewrite H0.
  constructor.
  unfold unmodifies_effect.
  destruct modifies. tauto.
  reflexivity.
Qed.

Lemma match_temp_env_ex : forall l' l le st m ,
    incl l' (List.map fst l) ->
    match_temp_env l le st m ->
  exists lval : list val,
    map_opt (fun x : positive * Ctypes.type => Maps.PTree.get (fst x) le)
      l' = Some lval.
Proof.
  induction l'.
  - simpl.
    intros. exists nil.
    reflexivity.
  - intros.
    simpl.
    assert (In a (List.map fst l)).
    apply H. simpl. tauto.
    apply List.incl_cons_inv in H.
    destruct H as (IN & INCL).
    assert (H0':= H0).
    eapply IHl' in H0'; eauto.
    destruct H0'.
    unfold match_temp_env in H0.
    rewrite Forall_forall in H0.
    rewrite in_map_iff in IN.
    destruct IN as (v' & FST & IN).
    subst. apply H0 in IN.
    unfold match_elt in IN.
    unfold AST.ident in *.
    destruct (Maps.PTree.get (fst (fst v')) le); try tauto.
    rewrite H.
    eexists. reflexivity.
Qed.
