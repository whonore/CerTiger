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

  Definition as_bool {A} (r : @res A) : bool :=
    match r with
    | ERR => false
    | OK _ => true
    end.

End RESMONAD.

Section MONADFACTS.

  Lemma bind_inversion : forall {A B : Type} (f : @res A) (g : A -> @res B) {y : B},
    bind f g = OK y ->
    exists x, f = OK x /\ g x = OK y.
  Proof.
    destruct f; [eauto | discriminate].
  Qed.

  Lemma bind2_inversion : forall {A B C : Type} (f : @res (A * B)) (g : A -> B -> @res C) {z : C},
    bind2 f g = OK z ->
    exists x, exists y, f = OK (x, y) /\ g x y = OK z.
  Proof.
    destruct f; [destruct p; eauto | discriminate].
  Qed.

  Lemma lift_option : forall {A : Type} (f : option A) (x : A),
    lift f = OK x ->
    f = Some x.
  Proof.
    intros. destruct f; [inversion H; reflexivity | discriminate].
  Qed.

End MONADFACTS.

Ltac monadInv1 H :=
  match type of H with
  | (OK _ = OK _) => inversion H; clear H; try subst
  | (ERR = OK _) => discriminate
  | ((if ?P then _ else ERR) = OK _) =>
      let EQ := fresh "EQ" in (
      destruct P eqn:EQ; [try (monadInv1 H) | discriminate])
  | (match ?X with | _ => _ end = OK _) => destruct X eqn:?HEQ; try (monadInv1 H)
  | (bind ?F ?G = OK ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv1 EQ2))))
  | (bind2 ?F ?G = OK ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (monadInv1 EQ2)))))
  end.

Ltac monadInv H :=
  match type of H with
  | (OK _ = OK _) => monadInv1 H
  | (ERR = OK _) => monadInv1 H
  | ((if ?P then _ else ERR) = OK _) => monadInv1 H
  | (match ?X with | _ => _ end = OK _) => monadInv1 H
  | (bind ?F ?G = OK ?X) => monadInv1 H
  | (bind2 ?F ?G = OK ?X) => monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _= OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = OK _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
  (at level 200, X ident, Y ident, A at level 100, B at level 200).

Notation "'check' A ; B" := (if A then B else ERR)
  (at level 200, A at level 100, B at level 200).
