From Coq Require Import List.
Import ListNotations.

Fixpoint replace_nth_error {A:Type} (l:list A) (n:nat) (v:A) {struct n} : option (list A) :=
  match n, l with
  | O, x :: tl => Some (v :: tl)
  | S n', x :: l' => 
    let tl:option (list A) := replace_nth_error l' n' v in
    match tl with
    | None => None
    | Some tl' => Some (x :: tl')
    end
  | _, nil => None
  end.

Fixpoint replace_nl_error {A:Type} (l:list A) (nl:list A){struct nl}: option (list A) :=
  match nl, l with
  | nil, _ => Some l
  | nx::ntl, nil => None
  | nx::ntl, x::tl => 
    let l1 := replace_nl_error tl ntl in
    match l1 with
    | None => None
    | Some l2 => Some (nx::l2)
    end
  end.

Fixpoint replace_nth_l_error {A:Type} (l:list A) (n:nat) (nl:list A) {struct n} : option (list A) :=
  match n, l with
  | O, x :: tl => replace_nl_error l nl
  | S n', x :: l' => 
    let tl := replace_nth_l_error l' n' nl in
    match tl with
    | None => None
    | Some tl' => Some (x :: tl')
    end
  | _, nil => None
  end.