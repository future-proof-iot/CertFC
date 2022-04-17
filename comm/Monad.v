Definition M (St: Type) (A: Type) := St -> option (A * St).

Definition returnM {A: Type} {St: Type} (a: A) : M St A := fun st => Some (a, st).
Definition errorM {A: Type} {St: Type} : M St A := fun st => None.
Definition bindM {A B: Type} {St: Type} (x: M St A) (f: A -> M St B) : M St B :=
  fun st =>
    match x st with
    | None => None
    | Some (x', st') => (f x') st'
    end.

Declare Scope monad_scope.
Notation "'do' x <- a ; b" :=
  (bindM a (fun x => b))
    (at level 200, x name, a at level 100, b at level 200)
  : monad_scope.