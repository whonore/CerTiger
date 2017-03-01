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

  Lemma init_unique : is_unique nil.
  Proof. constructor. Qed.

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
  | RECORD : list rfield -> Unique.t -> ty
  | NIL : ty
  | INT : ty
  | STRING : ty
  | ARRAY : ty -> Unique.t -> ty
  | NAME : symbol -> option ty -> ty
  | UNIT : ty
  with rfield : Set :=
  | mk_rfield : symbol -> ty -> rfield.

  Definition rf_name (rf : rfield) := let (name, _) := rf in name.
  Definition rf_type (rf : rfield) := let (_, type) := rf in type.

  Fixpoint ty_dec (t1 t2 : ty) : {t1 = t2} + {t1 <> t2}.
    repeat decide equality; try (apply Unique.unique_dec).
  Defined.

  Definition rf_eq (rf1 rf2 : rfield) : bool :=
    if Symbol.eq (rf_name rf1) (rf_name rf2)
      then if ty_dec (rf_type rf1) (rf_type rf2)
        then true
        else false
      else false.

  Lemma rf_eq_refl : forall rf,
    rf_eq rf rf = true.
  Proof.
    intros; unfold rf_eq; rewrite Symbol.eq_refl.
    destruct (ty_dec (rf_type rf) (rf_type rf)); congruence.
  Qed.

  Lemma rf_eq_sym : forall rf1 rf2,
    rf_eq rf1 rf2 = rf_eq rf2 rf1.
  Proof.
    destruct rf1, rf2; unfold rf_eq;
    simpl; rewrite Symbol.eq_sym.
    destruct (Symbol.eq s0 s);
    destruct (ty_dec t t0);
    destruct (ty_dec t0 t);
    try subst; congruence.
  Qed.

  Lemma rf_eq_trans : forall rf1 rf2 rf3,
    Types.rf_eq rf1 rf2 = true ->
    Types.rf_eq rf2 rf3 = true ->
    Types.rf_eq rf1 rf3 = true.
  Proof.
    unfold rf_eq; intros.
    destruct (Symbol.eq (rf_name rf1) (rf_name rf2)) eqn:EQ1;
    destruct (Symbol.eq (rf_name rf2) (rf_name rf3)) eqn:EQ2;
    destruct (Symbol.eq (rf_name rf1) (rf_name rf3)) eqn:EQ3;
    try (repeat match goal with
    | [ H : (if ?X then _ else _) = _ |- _ ] => destruct X
    | [ |- (if ?X then _ else _) = _ ] => destruct X
    end; congruence).
    generalize Symbol.eq_trans; intros.
    specialize H1 with (rf_name rf1) (rf_name rf2) (rf_name rf3).
    apply H1 in EQ1. congruence.
    assumption.
  Qed.

  Definition ty_compat (t1 t2 : ty) : bool :=
    if ty_dec t1 t2 then true
    else match t1, t2 with
    | RECORD fs u, NIL => true
    | NIL, RECORD fs u => true
    | _, _ => false
    end.

  Lemma ty_compat_sym : forall t1 t2,
    ty_compat t1 t2 = ty_compat t2 t1.
  Proof.
    destruct t1, t2; try reflexivity;
    match goal with
    | [ |- ty_compat ?X ?Y = ty_compat ?Y ?X ] =>
        destruct (ty_dec X Y) as [H1 | H1] eqn:EQ1;
        destruct (ty_dec Y X) as [H2 | H2] eqn:EQ2;
        try (inversion H1; reflexivity);
        try (inversion H2; reflexivity);
        try (unfold ty_compat; rewrite EQ1; rewrite EQ2; reflexivity)
    end.
  Qed.

  Fixpoint actual_ty (t : ty) : option ty :=
    match t with
    | NAME _ oty => match oty with
        | None => None
        | Some ty => actual_ty ty
        end
    | _ => Some t
    end.

  Lemma actual_not_name : forall t n oty,
    actual_ty t <> Some (NAME n oty).
  Proof.
    fix 1.
    destruct t; try discriminate.
    destruct o; [simpl; apply actual_not_name | discriminate].
  Qed.

End Types.
