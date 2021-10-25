From compcert.common Require AST.

From Coq Require Import ZArith.

Definition state_id:      AST.ident := 101%positive.
Definition pc_id:         AST.ident := 102%positive.
Definition regmaps_id:    AST.ident := 103%positive.
Definition mem_region_id: AST.ident := 104%positive.
Definition start_addr_id: AST.ident := 105%positive.
Definition size_id:       AST.ident := 106%positive.
Definition mem_regions_id:AST.ident := 107%positive.
Definition bpf_ctx_id:    AST.ident := 108%positive.
Definition bpf_stk_id:    AST.ident := 109%positive.
Definition content_id:    AST.ident := 110%positive.