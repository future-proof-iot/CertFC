Require Import DxIntegers DxValues DxRegs.

Definition state := regmap. (*This one must be int_64 defined in DxIntegers *)


Definition M (A: Type) := state -> option (A * state).

Definition runM {A: Type} (x: M A) (st: state) := x st.
Definition returnM {A: Type} (a: A) : M A := fun st => Some (a, st).
Definition emptyM {A: Type} : M A := fun st => None.
Definition bindM {A B: Type} (x: M A) (f: A -> M B) : M B :=
  fun st =>
    match runM x st with
    | None => None
    | Some (x', st') => runM (f x') st'
    end.

Definition eval_reg (r: reg) : M val64_t := fun st => Some (eval_regmap r st, st).
Definition upd_reg (r: reg) (v: val64_t) : M unit := fun st => Some (tt, upd_regmap r v st).

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.
