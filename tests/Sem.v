From compcert Require Import Coqlib Integers AST Values Memory Ctypes.
From dx.tests Require Import Asm Monad Int16.

Definition vlong_to_vint (v: val): val :=
  match v with
  | Vlong n    => Vint (Int.repr (Int64.unsigned n))
  | _          => Vundef
  end.

Open Scope monad_scope.

Definition step (ins:instruction) (next_ins: option int64) : MrBPF unit :=
  match ins with
  | BPF_NEG32 dst     =>
    do dst64 <- (eval_reg dst) ;
      upd_reg dst (Val.longofintu (Val.neg (vlong_to_vint (dst64))))
  | BPF_NEG64 dst     =>
    do dst64 <- (eval_reg dst) ;
      upd_reg dst (Val.negl (dst64))
  | BPF_ADD32r dst src =>
    do dst64 <- eval_reg dst;
    do src64 <- eval_reg src;
      upd_reg dst (Val.longofintu (Val.add (vlong_to_vint dst64) (vlong_to_vint src64)))
  | BPF_ADD32i dst i   => 
    do dst64 <- eval_reg dst;
      upd_reg dst (Val.longofintu (Val.add (vlong_to_vint dst64) (Vint i)))
  | BPF_ADD64r dst src => 
    do dst64 <- eval_reg dst;
    do src64 <- eval_reg src;
      upd_reg dst (Val.addl dst64 src64)
  | BPF_ADD64i dst i   => 
    do dst64 <- eval_reg dst;
      upd_reg dst (Val.addl dst64 (Val.longofint (Vint i)))
  | BPF_RET => default_MrBPF
  end.