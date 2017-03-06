(* 
 * Types.v
 * Wolf Honore
 * 
 * Defines the types of Tiger expressions.
 *)

Require Import Le.
Require Import List.

Require Import Symbol.

Module Type UNIQUE.

  Parameter t : Set.

  Parameter new : list t -> list t * t.
  Parameter dec : forall (u1 u2 : t), {u1 = u2} + {u1 <> u2}.

  Definition is_unique (us : list t) : Prop := NoDup us.

  Axiom new_adds : forall u us us',
    new us = (us', u) ->
    In u us'.

  Axiom new_unique : forall us, is_unique us -> is_unique (fst (new us)).

End UNIQUE.

Module Unique : UNIQUE.

  Definition t := nat.

  Definition maximum (us : list t) := fold_right max 0 us.

  Definition new (us : list t) :=
    let u := S (maximum us) in
    (u :: us, u).

  Definition dec : forall (u1 u2 : t), {u1 = u2} + {u1 <> u2}.
    decide equality.
  Defined.

  Definition is_unique (us : list t) : Prop := NoDup us.

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

Module Types' (U : UNIQUE).

  Definition symbol := Symbol.t.

  Definition upool := list U.t.

  Definition uinit : upool := nil.
  Definition unew us : upool * U.t := U.new us.

  Inductive ty : Set :=
    | RECORD : list rfield -> U.t -> ty
    | NIL : ty
    | INT : ty
    | STRING : ty
    | ARRAY : ty -> U.t -> ty
    | NAME : symbol -> ty
    | UNIT : ty
  with rfield : Set :=
    | mk_rfield : symbol -> ty -> rfield.

  Definition rf_name (rf : rfield) := let (name, _) := rf in name.
  Definition rf_type (rf : rfield) := let (_, type) := rf in type.

  Fixpoint ty_dec (t1 t2 : ty) : {t1 = t2} + {t1 <> t2}.
    repeat decide equality; try (apply U.dec).
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
    rf_eq rf1 rf2 = true ->
    rf_eq rf2 rf3 = true ->
    rf_eq rf1 rf3 = true.
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
    | RECORD _ u1, RECORD _ u2 => if U.dec u1 u2 then true else false
    | RECORD fs u, NIL => true
    | NIL, RECORD fs u => true
    | _, _ => false
    end.

  Lemma ty_compat_refl : forall t,
    ty_compat t t = true.
  Proof.
    destruct t; unfold ty_compat;
    match goal with
    | [ |- (if ?X then _ else _) = _ ] => destruct X; congruence
    end.
  Qed.

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
    unfold ty_compat. repeat destruct ty_dec; try discriminate.
    destruct (U.dec t t0); destruct (U.dec t0 t); congruence.
  Qed.

  Lemma ty_compat_simpl_eq : forall t1 t2,
    t2 = INT \/ t2 = STRING \/ t2 = UNIT ->
    ty_compat t1 t2 = true ->
    t1 = t2.
  Proof.
    intros; destruct H as [H | [H | H]]; destruct t2; try discriminate;
    destruct t1; try discriminate; try reflexivity.
  Qed.

  Lemma ty_compat_arr : forall t1 t2 aty u,
    t2 = ARRAY aty u ->
    ty_compat t1 t2 = true ->
    t1 = t2.
  Proof.
    intros; destruct t2; try discriminate; destruct t1; try discriminate;
    unfold ty_compat in H0; destruct (ty_dec (ARRAY t1 t0) (ARRAY t2 t)); congruence.
  Qed.

  Lemma ty_compat_rec : forall fs1 fs2 u1 u2,
    ty_compat (RECORD fs1 u1) (RECORD fs2 u2) = true ->
    u1 = u2.
  Proof.
    intros; unfold ty_compat in H;
    destruct (ty_dec (RECORD fs1 u1) (RECORD fs2 u2));
    destruct (U.dec u1 u2); congruence.
  Qed.

  (* actual_ty might return another Name, but with the possibility of infinite cycles need to add a max depth *)
  Definition max_depth := 100.

  Fixpoint actual_ty' (d : nat) (te : @Symbol.table ty) (t : ty) : option ty :=
    match d with
    | 0 => None
    | S d' => match t with
        | NAME n => match Symbol.look te n with
            | None => None
            | Some t => actual_ty' d' te t
            end
        | _ => Some t
        end
    end.

  Definition actual_ty te t := actual_ty' max_depth te t.

  Fixpoint actual_tys (te : @Symbol.table ty) (ts : list ty) : option (list ty) :=
    match ts with
    | nil => Some nil
    | t :: ts' => match actual_ty te t with
        | None => None
        | Some t' => option_map (cons t') (actual_tys te ts')
        end
    end.

  Lemma actual_not_name' : forall te t n d,
    actual_ty' d te t <> Some (NAME n).
  Proof.
    intros; destruct t;
    try solve [destruct te, d; simpl; discriminate].
    generalize dependent s; induction d; intros.
    - discriminate.
    - simpl. destruct (Symbol.look te s); try discriminate.
      destruct t; try solve [destruct te, d; simpl; try discriminate].
      apply IHd.
  Qed.

  Lemma actual_not_name : forall te t n,
    actual_ty te t <> Some (NAME n).
  Proof.
    intros; unfold actual_ty; apply actual_not_name'.
  Qed.

  Lemma actual_tys_no_none : forall te ts,
    In None (map (actual_ty te) ts) <->
    actual_tys te ts = None.
  Proof.
    split; intros.
    - induction ts; inversion H.
      + simpl; rewrite H0; reflexivity.
      + simpl. apply IHts in H0; rewrite H0.
        destruct (actual_ty te a); reflexivity.
    - induction ts; inversion H.
      destruct (actual_ty te a) eqn:?; simpl.
      + right; apply IHts; destruct (actual_tys te ts); [discriminate | reflexivity].
      + left; assumption.
  Qed.

  (* Return record if the other is nil *)
  Definition most_general (t1 t2 : ty) :=
    match t1, t2 with
    | RECORD _ _, NIL => t1
    | NIL, RECORD _ _ => t2
    | _, _ => t1
    end.

End Types'.
 
Module Types := Types' Unique.