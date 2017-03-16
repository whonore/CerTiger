(*
 * DecEqFacts.v
 * Wolf Honore
 *
 * Some useful lemmas and functions related to decidable equality.
 *)

Require Import List.

Section EQ_DEC.

  Context {t : Type}.
  Variable eq : forall (t1 t2 : t), {t1 = t2} + {t1 <> t2}.

  Definition make_beq : t -> t -> bool :=
    fun t1 t2 => if eq t1 t2 then true else false.

  Section EQ_DEC_FACTS.

    Lemma eq_refl {A} : forall t (b1 b2 : A),
      (if eq t t then b1 else b2) = b1.
    Proof.
      intros; destruct (eq t0 t0); congruence.
    Qed.

    Lemma eq_sym {A} : forall t1 t2 (b1 b2 : A),
      (if eq t1 t2 then b1 else b2) = (if eq t2 t1 then b1 else b2).
    Proof.
      intros; destruct (eq t1 t2).
      - subst; symmetry; apply eq_refl.
      - destruct (eq t2 t1); congruence.
    Qed.

    Lemma eq_true {A} : forall t1 t2 (b1 b2 : A),
      t1 = t2 ->
      (if eq t1 t2 then b1 else b2) = b1.
    Proof.
      intros; subst; apply eq_refl.
    Qed.

    Lemma eq_false {A} : forall t1 t2 (b1 b2 : A),
      t1 <> t2 ->
      (if eq t1 t2 then b1 else b2) = b2.
    Proof.
      intros; destruct (eq t1 t2); congruence.
    Qed.

  End EQ_DEC_FACTS.

  (* Some of this is in the Coq standard library for versions > 8.4 *)
  Section LIST_DEC_FACTS.

    Fixpoint nodup (xs : list t) : bool :=
      match xs with
      | nil => true
      | x :: xs' => if in_dec eq x xs' then false else nodup xs'
      end.

    Lemma nodup_sound : forall xs, nodup xs = true -> NoDup xs.
    Proof.
      induction xs.
      - constructor.
      - simpl. destruct (in_dec eq a xs).
        + discriminate.
        + constructor; auto.
    Qed.

    Lemma find_In : forall f (x : t) xs,
      find f xs = Some x ->
      In x xs.
    Proof.
      intros. induction xs.
      - discriminate.
      - inversion H. destruct (f a).
        + inversion H1; simpl; auto.
        + simpl; auto.
    Qed.

  End LIST_DEC_FACTS.

End EQ_DEC.
