Require Import Le.
Require Import List.

Require Import Symbol.

Module Type UNIQUE.

  Parameter t : Set.

  Parameter new : list t -> list t * t.

  Definition is_unique (us : list t) : Prop := NoDup us.

  Axiom new_adds : forall u us us',
    new us = (us', u) ->
    In u us'.

  Axiom new_unique : forall us, is_unique us -> is_unique (fst (new us)).

End UNIQUE.

Module Unique <: UNIQUE.

  Definition t := nat.

  Definition maximum (us : list t) := fold_right max 0 us.

  Definition new (us : list t) :=
    let u := S (maximum us) in
    (u :: us, u).

  Definition is_unique (us : list t) : Prop := NoDup us.

  Definition unique_dec : forall (u1 u2 : t), {u1 = u2} + {u1 <> u2}.
    decide equality.
  Defined.

  Lemma maximum_ge : forall u us,
    In u us -> u <= maximum us.
  Proof.
    induction us; intros; inversion H; subst; simpl.
    - destruct (Max.max_dec u (maximum us)); rewrite e.
      + constructor.
      + rewrite <- e. apply Max.le_max_l.
    - apply IHus in H0.
      destruct (Max.max_dec a (maximum us)); rewrite e.
      + assert (maximum us <= a). 
        { rewrite <- e. apply Max.le_max_r. }
        apply le_trans with (m := maximum us); assumption. 
      + assumption.
  Qed.

  Lemma new_adds : forall u us us',
    new us = (us', u) ->
    In u us'.
  Proof.
    unfold new. intros.
    inversion H; subst; constructor; reflexivity.
  Qed.

  Lemma new_unique : forall us, is_unique us -> is_unique (fst (new us)).
  Proof.
    unfold is_unique, new. intros.
    induction us; simpl.
    - constructor; auto.
    - constructor; [| assumption].
      change (max a (maximum us)) with (maximum (a :: us)).
      unfold not. intros.
      apply maximum_ge in H0.
      apply Le.le_Sn_n in H0; assumption.
  Qed.

End Unique.

Module Types.

  Definition symbol := Symbol.t.

  Definition upool := list Unique.t.

  Definition uinit : upool := nil.
  Definition unew us : upool * Unique.t := Unique.new us.

  Inductive ty : Set :=
  | RECORD : list (symbol * ty) -> Unique.t -> ty
  | NIL : ty
  | INT : ty
  | STRING : ty
  | ARRAY : ty -> Unique.t -> ty
  | NAME : symbol -> option ty -> ty
  | UNIT : ty.

  Definition ty_eq (t1 t2 : ty) :=
    match t1, t2 with
    | RECORD _ u1, RECORD _ u2 => if Unique.unique_dec u1 u2 then true else false
    | NIL, NIL => true
    | INT, INT => true
    | STRING, STRING => true
    | ARRAY _ u1, ARRAY _ u2 => if Unique.unique_dec u1 u2 then true else false
    | NAME _ _, NAME _ _ => false
    | UNIT, UNIT => true
    | _, _ => false
    end.

End Types.