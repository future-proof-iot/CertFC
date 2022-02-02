From compcert Require Import Ctypes AST Integers.

From bpf.comm Require Import Regs rBPFAST.

(** For use to distinguish ALU32 and ALU64 *)
Inductive arch := A32 | A64.

Lemma arch_eq: forall (x y: arch), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.

Definition arch_eqb (a0 a1: arch) : bool :=
  match a0, a1 with
  | A32, A32
  | A64, A64 => true
  | _, _ => false
  end.

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

Lemma signedness_eq32: forall (s1 s2: signedness), {s1=s2} + {s1<>s2}.
Proof.
  decide equality.
Defined.

Definition signedness_eqb (s1 s2: signedness) :=
  match s1, s2 with
  | Signed, Signed
  | Unsigned, Unsigned => true
  | _, _ => false
  end.

Lemma cond_eq: forall (x y: cond), {x=y} + {x<>y}.
Proof.
  decide equality. all: apply signedness_eq32.
Defined.

Definition cond_eqb (c0 c1: cond): bool :=
  match c0, c1 with
  | Eq, Eq
  | SEt, SEt
  | Ne, Ne => true
  | Gt s0, Gt s1
  | Ge s0, Ge s1
  | Lt s0, Lt s1
  | Le s0, Le s1 => signedness_eqb s0 s1
  | _, _ => false
  end.

Definition off := int.
Definition imm := int.

Inductive binOp: Type :=
  BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND
| BPF_LSH | BPF_RSH | BPF_MOD | BPF_XOR | BPF_MOV| BPF_ARSH.

Lemma binOp_eq: forall (b1 b2: binOp), {b1=b2} + {b1<>b2}.
Proof.
  decide equality.
Defined.

Definition binOp_eqb (b0 b1: binOp): bool :=
  match b0, b1 with
  | BPF_ADD, BPF_ADD
  | BPF_SUB, BPF_SUB
  | BPF_MUL, BPF_MUL
  | BPF_DIV, BPF_DIV
  | BPF_OR,  BPF_OR
  | BPF_AND, BPF_AND
  | BPF_LSH, BPF_LSH
  | BPF_RSH, BPF_RSH
  | BPF_MOD, BPF_MOD
  | BPF_XOR, BPF_XOR
  | BPF_MOV, BPF_MOV
  | BPF_ARSH, BPF_ARSH => true
  | _, _ => false
  end.

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

Definition bpf_instruction_eqb (a b: instruction) : bool :=
  match a, b with
  | BPF_NEG a0 r0, BPF_NEG a1 r1 => arch_eqb a0 a1 && reg_eqb r0 r1
  | BPF_BINARY a0 b0 r0 ri0, BPF_BINARY a1 b1 r1 ri1 => arch_eqb a0 a1 && binOp_eqb b0 b1 && reg_eqb r0 r1 &&
      match ri0, ri1 with
      | inl r0', inl r1' => reg_eqb r0' r1'
      | inr i0', inr i1' => Int.eq  i0' i1'
      | _, _ => false
      end
  | BPF_JA ofs0, BPF_JA ofs1 => Int.eq ofs0 ofs1
  | BPF_JUMP c0 r0 ri0 ofs0, BPF_JUMP c1 r1 ri1 ofs1 => cond_eqb c0 c1 && reg_eqb r0 r1 && (match ri0, ri1 with
      | inl r0', inl r1' => reg_eqb r0' r1'
      | inr i0', inr i1' => Int.eq  i0' i1'
      | _, _ => false
      end) && Int.eq ofs0 ofs1
  | BPF_LDDW r0 i0, BPF_LDDW r1 i1 => reg_eqb r0 r1 && Int.eq i0 i1
  | BPF_LDX mc0 d0 s0 ofs0, BPF_LDX mc1 d1 s1 ofs1 => chunk_eqb mc0 mc1 && reg_eqb d0 d1 && reg_eqb s0 s1 && Int.eq ofs0 ofs1
  | BPF_ST mc0 r0 ri0 ofs0, BPF_ST mc1 r1 ri1 ofs1 => chunk_eqb mc0 mc1 && reg_eqb r0 r1 && (match ri0, ri1 with
      | inl r0', inl r1' => reg_eqb r0' r1'
      | inr i0', inr i1' => Int.eq  i0' i1'
      | _, _ => false
      end) && Int.eq ofs0 ofs1
  | BPF_RET, BPF_RET
  | BPF_ERR, BPF_ERR => true
  | _, _ => false
  end.
