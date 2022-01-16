From compcert Require Import Integers AST Ctypes.
From Coq Require Import Arith ZArith Lia.

From bpf.comm Require Import Int16 Flag Regs rBPFValues.
From bpf.model Require Import Syntax Decode.

Open Scope nat_scope.

Definition get_instruction_if (opcode:nat) (rd rs:reg) (ofs: int) (i: int): instruction :=
  if opcode =? 0x07 then
    BPF_BINARY A64 BPF_ADD  rd (inr i)
  else if opcode =? 0x0f then
    BPF_BINARY A64 BPF_ADD  rd (inl rs)
  else if opcode =? 0x17 then
    BPF_BINARY A64 BPF_SUB  rd (inr i)
  else if opcode =? 0x1f then
    BPF_BINARY A64 BPF_SUB  rd (inl rs)
  else if opcode =? 0x27 then
    BPF_BINARY A64 BPF_MUL  rd (inr i)
  else if opcode =? 0x2f then
    BPF_BINARY A64 BPF_MUL  rd (inl rs)
  else if opcode =? 0x37 then
    BPF_BINARY A64 BPF_DIV  rd (inr i)
  else if opcode =? 0x3f then
    BPF_BINARY A64 BPF_DIV  rd (inl rs)
  else if opcode =? 0x47 then
    BPF_BINARY A64 BPF_OR   rd (inr i)
  else if opcode =? 0x4f then
    BPF_BINARY A64 BPF_OR   rd (inl rs)
  else if opcode =? 0x57 then
    BPF_BINARY A64 BPF_AND  rd (inr i)
  else if opcode =? 0x5f then
    BPF_BINARY A64 BPF_AND  rd (inl rs)
  else if opcode =? 0x67 then
    BPF_BINARY A64 BPF_LSH  rd (inr i)
  else if opcode =? 0x6f then
    BPF_BINARY A64 BPF_LSH  rd (inl rs)
  else if opcode =? 0x77 then
    BPF_BINARY A64 BPF_RSH  rd (inr i)
  else if opcode =? 0x7f then
    BPF_BINARY A64 BPF_RSH  rd (inl rs)
  else if opcode =? 0x87 then
    BPF_NEG A64 rd
  else if opcode =? 0x97 then
    BPF_BINARY A64 BPF_MOD  rd (inr i)
  else if opcode =? 0x9f then
    BPF_BINARY A64 BPF_MOD  rd (inl rs)
  else if opcode =? 0xa7 then
    BPF_BINARY A64 BPF_XOR  rd (inr i)
  else if opcode =? 0xaf then
    BPF_BINARY A64 BPF_XOR  rd (inl rs)
  else if opcode =? 0xb7 then
    BPF_BINARY A64 BPF_MOV  rd (inr i)
  else if opcode =? 0xbf then
    BPF_BINARY A64 BPF_MOV  rd (inl rs)
  else if opcode =? 0xc7 then
    BPF_BINARY A64 BPF_ARSH rd (inr i)
  else if opcode =? 0xcf then
    BPF_BINARY A64 BPF_ARSH rd (inl rs)
  (*ALU32*)
  else if opcode =? 0x04 then
    BPF_BINARY A32 BPF_ADD  rd (inr i)
  else if opcode =? 0x0c then
    BPF_BINARY A32 BPF_ADD  rd (inl rs)
  else if opcode =? 0x14 then
    BPF_BINARY A32 BPF_SUB  rd (inr i)
  else if opcode =? 0x1c then
    BPF_BINARY A32 BPF_SUB  rd (inl rs)
  else if opcode =? 0x24 then
    BPF_BINARY A32 BPF_MUL  rd (inr i)
  else if opcode =? 0x2c then
    BPF_BINARY A32 BPF_MUL  rd (inl rs)
  else if opcode =? 0x34 then
    BPF_BINARY A32 BPF_DIV  rd (inr i)
  else if opcode =? 0x3c then
    BPF_BINARY A32 BPF_DIV  rd (inl rs)
  else if opcode =? 0x44 then
    BPF_BINARY A32 BPF_OR   rd (inr i)
  else if opcode =? 0x4c then
    BPF_BINARY A32 BPF_OR   rd (inl rs)
  else if opcode =? 0x54 then
    BPF_BINARY A32 BPF_AND  rd (inr i)
  else if opcode =? 0x5c then
    BPF_BINARY A32 BPF_AND  rd (inl rs)
  else if opcode =? 0x64 then
    BPF_BINARY A32 BPF_LSH  rd (inr i)
  else if opcode =? 0x6c then
    BPF_BINARY A32 BPF_LSH  rd (inl rs)
  else if opcode =? 0x74 then
    BPF_BINARY A32 BPF_RSH  rd (inr i)
  else if opcode =? 0x7c then
    BPF_BINARY A32 BPF_RSH  rd (inl rs)
  else if opcode =? 0x84 then
    BPF_NEG A32 rd
  else if opcode =? 0x94 then
    BPF_BINARY A32 BPF_MOD  rd (inr i)
  else if opcode =? 0x9c then
    BPF_BINARY A32 BPF_MOD  rd (inl rs)
  else if opcode =? 0xa4 then
    BPF_BINARY A32 BPF_XOR  rd (inr i)
  else if opcode =? 0xac then
    BPF_BINARY A32 BPF_XOR  rd (inl rs)
  else if opcode =? 0xb4 then
    BPF_BINARY A32 BPF_MOV  rd (inr i)
  else if opcode =? 0xbc then
    BPF_BINARY A32 BPF_MOV  rd (inl rs)
  else if opcode =? 0xc4 then
    BPF_BINARY A32 BPF_ARSH rd (inr i)
  else if opcode =? 0xcc then
    BPF_BINARY A32 BPF_ARSH rd (inl rs)

  else if opcode =? 0x18 then
    BPF_LDDW rd i
  else if opcode =? 0x61 then
    BPF_LDX Mint32         rd rs ofs
  else if opcode =? 0x69 then
    BPF_LDX Mint16unsigned rd rs ofs
  else if opcode =? 0x71 then
    BPF_LDX Mint8unsigned  rd rs ofs
  else if opcode =? 0x79 then
    BPF_LDX Mint64         rd rs ofs
  else if opcode =? 0x62 then
    BPF_ST  Mint32         rd (inr i)  ofs
  else if opcode =? 0x6a then
    BPF_ST  Mint16unsigned rd (inr i)  ofs
  else if opcode =? 0x72 then
    BPF_ST  Mint8unsigned  rd (inr i)  ofs
  else if opcode =? 0x7a then
    BPF_ST  Mint64         rd (inr i)  ofs
  else if opcode =? 0x63 then
    BPF_ST  Mint32         rd (inl rs) ofs
  else if opcode =? 0x6b then
    BPF_ST  Mint16unsigned rd (inl rs) ofs
  else if opcode =? 0x73 then
    BPF_ST  Mint8unsigned  rd (inl rs) ofs
  else if opcode =? 0x7b then
    BPF_ST  Mint64         rd (inl rs) ofs

  else if opcode =? 0x05 then
    BPF_JA ofs
  else if opcode =? 0x15 then
    BPF_JUMP  Eq           rd (inr i)  ofs
  else if opcode =? 0x1d then
    BPF_JUMP  Eq           rd (inl rs) ofs
  else if opcode =? 0x25 then
    BPF_JUMP (Gt Unsigned) rd (inr i)  ofs
  else if opcode =? 0x2d then
    BPF_JUMP (Gt Unsigned) rd (inl rs) ofs
  else if opcode =? 0x35 then
    BPF_JUMP (Ge Unsigned) rd (inr i)  ofs
  else if opcode =? 0x3d then
    BPF_JUMP (Ge Unsigned) rd (inl rs) ofs
  else if opcode =? 0xa5 then
    BPF_JUMP (Lt Unsigned) rd (inr i)  ofs
  else if opcode =? 0xad then
    BPF_JUMP (Lt Unsigned) rd (inl rs) ofs
  else if opcode =? 0xb5 then
    BPF_JUMP (Le Unsigned) rd (inr i)  ofs
  else if opcode =? 0xbd then
    BPF_JUMP (Le Unsigned) rd (inl rs) ofs
  else if opcode =? 0x45 then
    BPF_JUMP  SEt          rd (inr i)  ofs
  else if opcode =? 0x4d then
    BPF_JUMP  SEt          rd (inl rs) ofs
  else if opcode =? 0x55 then
    BPF_JUMP  Ne           rd (inr i)  ofs
  else if opcode =? 0x5d then
    BPF_JUMP  Ne           rd (inl rs) ofs
  else if opcode =? 0x65 then
    BPF_JUMP (Gt Signed)   rd (inr i)  ofs
  else if opcode =? 0x6d then
    BPF_JUMP (Gt Signed)   rd (inl rs) ofs
  else if opcode =? 0x75 then
    BPF_JUMP (Ge Signed)   rd (inr i)  ofs
  else if opcode =? 0x7d then
    BPF_JUMP (Ge Signed)   rd (inl rs) ofs
  else if opcode =? 0xc5 then
    BPF_JUMP (Lt Signed)   rd (inr i)  ofs
  else if opcode =? 0xcd then
    BPF_JUMP (Lt Signed)   rd (inl rs) ofs
  else if opcode =? 0xd5 then
    BPF_JUMP (Le Signed)   rd (inr i)  ofs
  else if opcode =? 0xdd then
    BPF_JUMP (Le Signed)   rd (inl rs) ofs

  else if opcode =? 0x95 then
    BPF_RET

  else
    BPF_ERR
.
Close Scope nat_scope.

Lemma switch_if_same :
  forall (opcode:nat) (rd rs:reg) (ofs: int) (i: int),
    get_instruction opcode rd rs ofs i = get_instruction_if opcode rd rs ofs i.
Proof.
  intros.
  unfold get_instruction, get_instruction_if.
  do 100 (destruct opcode; [reflexivity | idtac]).
  do 121 (destruct opcode; [reflexivity | idtac]).
  destruct opcode; [reflexivity | reflexivity].
Qed.

Open Scope nat_scope.
Lemma switch_to_if :
  forall (rd rs:reg) (ofs: int) (i: int)
(Hopcode : nat)
(Hadd64i : Hopcode <> 7)
(Hadd64r : Hopcode <> 15)
(Hsub64i : Hopcode <> 23)
(Hsub64r : Hopcode <> 31)
(Hmul64i : Hopcode <> 39)
(Hmul64r : Hopcode <> 47)
(Hdiv64i : Hopcode <> 55)
(Hdiv64r : Hopcode <> 63)
(Hor64i : Hopcode <> 71)
(Hor64r : Hopcode <> 79)
(Hand64i : Hopcode <> 87)
(Hand64r : Hopcode <> 95)
(Hlsh64i : Hopcode <> 103)
(Hlsh64r : Hopcode <> 111)
(Hrsh64i : Hopcode <> 119)
(Hrsh64r : Hopcode <> 127)
(Hneg64 : Hopcode <> 135)
(Hmod64i : Hopcode <> 151)
(Hmod64r : Hopcode <> 159)
(Hxor64i : Hopcode <> 167)
(Hxor64r : Hopcode <> 175)
(Hmov64i : Hopcode <> 183)
(Hmov64r : Hopcode <> 191)
(Harsh64i : Hopcode <> 199)
(Harsh64r : Hopcode <> 207)
(Hadd32i : Hopcode <> 4)
(Hadd32r : Hopcode <> 12)
(Hsub32i : Hopcode <> 20)
(Hsub32r : Hopcode <> 28)
(Hmul32i : Hopcode <> 36)
(Hmul32r : Hopcode <> 44)
(Hdiv32i : Hopcode <> 52)
(Hdiv32r : Hopcode <> 60)
(Hor32i : Hopcode <> 68)
(Hor32r : Hopcode <> 76)
(Hand32i : Hopcode <> 84)
(Hand32r : Hopcode <> 92)
(Hlsh32i : Hopcode <> 100)
(Hlsh32r : Hopcode <> 108)
(Hrsh32i : Hopcode <> 116)
(Hrsh32r : Hopcode <> 124)
(Hneg32 : Hopcode <> 132)
(Hmod32i : Hopcode <> 148)
(Hmod32r : Hopcode <> 156)
(Hxor32i : Hopcode <> 164)
(Hxor32r : Hopcode <> 172)
(Hmov32i : Hopcode <> 180)
(Hmov32r : Hopcode <> 188)
(Harsh32i : Hopcode <> 196)
(Harsh32r : Hopcode <> 204)
(HLDDW : Hopcode <> 24)
(Hldx32 : Hopcode <> 97)
(Hldx16 : Hopcode <> 105)
(Hldx8 : Hopcode <> 113)
(Hldx64 : Hopcode <> 121)
(Hstx32 : Hopcode <> 98)
(Hstx16 : Hopcode <> 106)
(Hstx8 : Hopcode <> 114)
(Hstx64 : Hopcode <> 122)
(Hst32 : Hopcode <> 99)
(Hst16 : Hopcode <> 107)
(Hst8 : Hopcode <> 115)
(Hst64 : Hopcode <> 123)
(Hja : Hopcode <> 5)
(Heqi : Hopcode <> 21)
(Heqr : Hopcode <> 29)
(Hgti : Hopcode <> 37)
(Hgtr : Hopcode <> 45)
(Hgei : Hopcode <> 53)
(Hger : Hopcode <> 61)
(Hlti : Hopcode <> 165)
(Hltr : Hopcode <> 173)
(Hlei : Hopcode <> 181)
(Hler : Hopcode <> 189)
(Hseti : Hopcode <> 69)
(Hsetr : Hopcode <> 77)
(Hnei : Hopcode <> 85)
(Hner : Hopcode <> 93)
(Hsgti : Hopcode <> 101)
(Hsgtr : Hopcode <> 109)
(Hsgei : Hopcode <> 117)
(Hsger : Hopcode <> 125)
(Hslti : Hopcode <> 197)
(Hsltr : Hopcode <> 205)
(Hslei : Hopcode <> 213)
(Hsler : Hopcode <> 221)
(Hret : Hopcode <> 149),
  get_instruction Hopcode rd rs ofs i = BPF_ERR.
Proof.
  intros.
  rewrite switch_if_same.
  unfold get_instruction_if.
Ltac simpl_nat :=
  match goal with
  | H: ?X <> ?Y |- context [if (?X =? ?Y) then _ else _] =>
    destruct (X =? Y) eqn: Ht; [rewrite Nat.eqb_eq in Ht; intuition | try reflexivity]; clear Ht
  end.
  repeat simpl_nat.
Qed.
Close Scope nat_scope.