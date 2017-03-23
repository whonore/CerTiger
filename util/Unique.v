(*
 * Unique.v
 * Wolf Honore
 *
 * Defines an interface for a generator of unique values.
 *)

Require Import Le.
Require Import List.
Require Import Max.

Module Type UNIQUE.

  Parameter t : Set.

  Parameter init : list t.
  Parameter new : list t -> list t * t.
  Parameter eq : forall (u1 u2 : t), {u1 = u2} + {u1 <> u2}.

  Definition is_unique (us : list t) : Prop := NoDup us.

  Hypothesis init_unique : is_unique init.

  Hypothesis new_spec : forall u us us',
    is_unique us ->
    new us = (us', u) ->
    In u us' /\ is_unique us'.

End UNIQUE.

Module NatUnique <: UNIQUE.

  Definition t := nat.

  Definition maximum (us : list t) := fold_right max 0 us.

  Definition init := @nil t.

  Definition new (us : list t) :=
    let u := S (maximum us) in
    (u :: us, u).

  Definition eq : forall (u1 u2 : t), {u1 = u2} + {u1 <> u2}.
    decide equality.
  Defined.

  Definition is_unique (us : list t) : Prop := NoDup us.

  Lemma maximum_ge : forall u us,
    In u us -> u <= maximum us.
  Proof.
    induction us; intros; inversion H; subst; simpl.
    - destruct (max_dec u (maximum us)); rewrite e.
      + constructor.
      + rewrite <- e. apply le_max_l.
    - apply IHus in H0.
      destruct (max_dec a (maximum us)); rewrite e.
      + assert (maximum us <= a).
        { rewrite <- e. apply le_max_r. }
        apply le_trans with (m := maximum us); assumption.
      + assumption.
  Qed.

  Lemma init_unique : is_unique init.
  Proof. constructor. Qed.

  Lemma new_spec : forall u us us',
    is_unique us ->
    new us = (us', u) ->
    In u us' /\ is_unique us'.
  Proof.
    unfold new, is_unique; intros.
    inversion H0; subst.
    split.
    - simpl; left; reflexivity.
    - destruct us.
      + constructor; auto.
      + constructor; [| assumption].
        unfold not; intros.
        apply maximum_ge in H1.
        apply le_Sn_n in H1; assumption.
  Qed.

End NatUnique.
