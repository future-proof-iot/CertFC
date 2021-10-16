From compcert.common Require AST.

From Coq Require Import ZArith.

Definition state_id:   AST.ident := 101%positive.
Definition pc_id:      AST.ident := 102%positive.
Definition regmaps_id: AST.ident := 103%positive.