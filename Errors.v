Require Import List.

(* Mostly copied from CompCert *)

Section Res.

Inductive res {A : Type} : Type :=
  | OK : A -> @res A
  | ERR : @res A.

End Res.

Section RESMONAD.

Definition bind {A B : Type} (f : @res A) (g : A -> @res B) : @res B :=
  match f with
  | ERR => ERR 
  | OK x => g x
  end.

Definition bind2 {A B C : Type} (f : @res (A * B)) (g : A -> B -> @res C) : @res C :=
  match f with
  | ERR => ERR
  | OK (x, y) => g x y
  end.

Definition res_map {A B} (f : A -> B) (r : @res A) : @res B :=
  match r with
  | ERR => ERR
  | OK x => OK (f x)
  end.

Fixpoint sequence {A} (rs : list (@res A)) : @res (list A) :=
  match rs with
  | nil => OK nil
  | r :: rs' => match r with
    | ERR => ERR
    | OK r => res_map (cons r) (sequence rs')
    end
  end.

Definition lift {A} (o : option A) : @res A :=
  match o with
  | None => ERR
  | Some x => OK x
  end.

End RESMONAD.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
  (at level 200, X ident, Y ident, A at level 100, B at level 200).

Notation "'check' A ; B" := (if A then B else ERR)
  (at level 200, A at level 100, B at level 200).