(*
 * Types.v
 * Wolf Honore
 *
 * Defines the types of Tiger expressions.
 *)

Require Import List.

Require Import DecEqFacts.
Require Import Symbol.
Require Import Unique.

Module Types' (S : SYMBOL) (U : UNIQUE).

  Definition upool := list U.t.

  Definition uinit : upool := U.init.
  Definition unew us : upool * U.t := U.new us.

  Inductive ty : Set :=
    | RECORD : list rfield -> U.t -> ty
    | NIL : ty
    | INT : ty
    | STRING : ty
    | ARRAY : ty -> U.t -> ty
    | NAME : S.t -> ty
    | UNIT : ty
  with rfield : Set :=
    | mk_rfield : S.t -> ty -> rfield.

  Definition rf_name (rf : rfield) := let (name, _) := rf in name.
  Definition rf_type (rf : rfield) := let (_, type) := rf in type.

  Fixpoint ty_eq (t1 t2 : ty) : {t1 = t2} + {t1 <> t2}.
    repeat decide equality; try apply U.eq; try apply S.eq.
  Defined.

  Definition rf_eq (rf1 rf2 : rfield) : {rf1 = rf2} + {rf1 <> rf2}.
    decide equality; try apply ty_eq; try apply S.eq.
  Defined.

  Definition ty_compat (t1 t2 : ty) : bool :=
    if ty_eq t1 t2
      then true
      else match t1, t2 with
      | RECORD _ u1, RECORD _ u2 => if U.eq u1 u2 then true else false
      | RECORD fs u, NIL => true
      | NIL, RECORD fs u => true
      | _, _ => false
      end.

  Fixpoint tys_compat (ts1 ts2 : list ty) : bool :=
    match ts1, ts2 with
    | nil, nil => true
    | t1 :: ts1', t2 :: ts2' => andb (ty_compat t1 t2) (tys_compat ts1' ts2')
    | _, _ => false
    end.

  Lemma ty_compat_refl : forall t,
    ty_compat t t = true.
  Proof.
    destruct t; unfold ty_compat; try apply eq_refl.
  Qed.

  Lemma ty_compat_sym : forall t1 t2,
    ty_compat t1 t2 = ty_compat t2 t1.
  Proof.
    destruct t1, t2; unfold ty_compat; try rewrite eq_sym; try rewrite eq_refl; try reflexivity.
    rewrite (@eq_sym U.t). reflexivity.
  Qed.

  Lemma ty_compat_simpl_eq : forall t1 t2,
    t2 = INT \/ t2 = STRING \/ t2 = UNIT ->
    ty_compat t1 t2 = true ->
    t1 = t2.
  Proof.
    intros; destruct H as [H | [H | H]]; subst;
    destruct t1; try reflexivity;
    unfold ty_compat in H0;
    match type of H0 with
    | (if ?X then _ else _) = _ => destruct X
    end; discriminate.
  Qed.

  Lemma ty_compat_arr : forall t1 t2 aty u,
    t2 = ARRAY aty u ->
    ty_compat t1 t2 = true ->
    t1 = t2.
  Proof.
    intros. destruct t1, t2; try discriminate;
    unfold ty_compat in H0;
    match type of H0 with
    | (if ?X then _ else _) = _ => destruct X
    end; congruence.
  Qed.

  Lemma ty_compat_rec : forall fs1 fs2 u1 u2,
    ty_compat (RECORD fs1 u1) (RECORD fs2 u2) = true ->
    u1 = u2.
  Proof.
    intros; unfold ty_compat in H;
    destruct (ty_eq (RECORD fs1 u1) (RECORD fs2 u2));
    destruct (U.eq u1 u2); congruence.
  Qed.

  (* actual_ty might return another Name, but with the possibility of infinite cycles need to add a max depth *)
  Definition max_depth := 100.

  Fixpoint actual_ty' (d : nat) (te : S.table ty) (t : ty) : option ty :=
    match d with
    | 0 => None
    | S d' => match t with
        | NAME n => match S.look te n with
            | None => None
            | Some t => actual_ty' d' te t
            end
        | _ => Some t
        end
    end.

  Definition actual_ty te t := actual_ty' max_depth te t.

  Fixpoint actual_tys (te : S.table ty) (ts : list ty) : option (list ty) :=
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
    intros; destruct t; try solve [destruct d; simpl; discriminate].
    generalize dependent t; induction d; intros.
    - discriminate.
    - simpl. destruct (S.look te t); try discriminate.
      destruct t0; try solve [destruct d; simpl; try discriminate].
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

Module Types := Types' Symbol NatUnique.
