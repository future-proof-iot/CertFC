From compcert.common Require AST.
From dx Require Import IRtoC.
From Coq Require Import ZArith String.
Import UserIdentNotations.
Open Scope string.

Definition state_id:      AST.ident := $"bpf_state".
Definition pc_id:         AST.ident := $"state_pc".
Definition regmaps_id:    AST.ident := $"regsmap".
Definition flag_id:       AST.ident := $"bpf_flag".
Definition mem_num_id:    AST.ident := $"mrs_num".
Definition mem_regs_id:   AST.ident := $"mrs".
Definition mem_region_id: AST.ident := $"memory_region".
Definition ins_len_id:    AST.ident := $"ins_len".
Definition ins_id:        AST.ident := $"ins".
Definition start_addr_id: AST.ident := $"start_addr".
Definition size_id:       AST.ident := $"block_size".
Definition perm_id:       AST.ident := $"block_perm".
Definition block_ptr_id:  AST.ident := $"block_ptr".
Definition mem_regions_id:AST.ident := $"memory_regions".
Definition bpf_ctx_id:    AST.ident := $"bpf_ctx".
Definition bpf_stk_id:    AST.ident := $"bpf_stk".
Definition content_id:    AST.ident := $"content".
Close Scope string.