From compcert.common Require AST.

From Coq Require Import ZArith.

Definition state_id:      AST.ident := 1001%positive.
Definition pc_id:         AST.ident := 1002%positive.
Definition regmaps_id:    AST.ident := 1003%positive.
Definition flag_id:       AST.ident := 1004%positive.
Definition mem_region_id: AST.ident := 1005%positive.
Definition start_addr_id: AST.ident := 1006%positive.
Definition size_id:       AST.ident := 1007%positive.
Definition mem_regions_id:AST.ident := 1008%positive.
Definition bpf_ctx_id:    AST.ident := 1009%positive.
Definition bpf_stk_id:    AST.ident := 1010%positive.
Definition content_id:    AST.ident := 1011%positive.