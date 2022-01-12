From compcert Require Import Ctypes AST Integers.

From bpf.comm Require Import Int16 Regs.

(** For use to distinguish ALU32 and ALU64 *)
Inductive arch := A32 | A64.

(** For condition flags *)
(*Inductive signedness := Signed | Unsigned.*)

Inductive cond := 
  Eq 
| Gt: signedness -> cond 
| Ge: signedness -> cond
| Lt: signedness -> cond
| Le: signedness -> cond
| SEt 
| Ne
.

Definition off := int.
Definition imm := int.

Inductive binOp: Type :=
  BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND
| BPF_LSH | BPF_RSH | BPF_MOD | BPF_XOR | BPF_MOV| BPF_ARSH.

Inductive instruction: Type :=
  (**r ALU64/32*)
  | BPF_NEG    : arch -> reg -> instruction
  | BPF_BINARY : arch -> binOp -> reg -> reg+imm -> instruction  
  (**r Branch *)
  | BPF_JA  : off -> instruction
  | BPF_JUMP: cond -> reg -> reg+imm -> off -> instruction

  (**r Load *)
  | BPF_LDDW   : reg -> imm -> instruction
  (**r Load_x *)
  | BPF_LDX : memory_chunk -> reg -> reg -> off -> instruction
  (**r Store/ Store_x *)
  | BPF_ST  : memory_chunk -> reg -> reg+imm -> off -> instruction
  (**r exit *)
  | BPF_RET  : instruction
  | BPF_ERR  : instruction
.