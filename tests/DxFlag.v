Inductive bpf_flag: Type := 
  | BPF_OK                  (**r =  0, *)
  | BPF_ILLEGAL_INSTRUCTION (**r = -1, *)
  | BPF_ILLEGAL_MEM         (**r = -2, *)
  | BPF_ILLEGAL_JUMP        (**r = -3, *)
  | BPF_ILLEGAL_CALL        (**r = -4, *)
  | BPF_ILLEGAL_LEN         (**r = -5, *)
  | BPF_ILLEGAL_REGISTER    (**r = -6  *)
  | BPF_NO_RETURN           (**r = -7, *)
  | BPF_OUT_OF_BRANCHES     (**r = -8, *)
  | BPF_ILLEGAL_DIV         (**r = -9, *)
  | BPF_ILLEGAL_SHIFT       (**r = -10,*)
  | BPF_ILLEGAL_ALU         (**r = -11,*)
.
Lemma bpf_flag_eq: forall (x y: bpf_flag), {x=y} + {x<>y}.
Proof.
decide equality. Defined.

Inductive ErrorUndef :=
  | ErrorL: bpf_flag -> ErrorUndef
  | UndefR: bpf_flag -> ErrorUndef.