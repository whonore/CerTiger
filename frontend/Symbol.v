(*
 * Symbol.v
 * Wolf Honore
 *
 * Defines the type used to represent identifiers.
 *)

Require Import Arith.
Require Import List.

Module Type SYMBOL.

  Parameter t : Set.
  Parameter eq : t -> t -> bool.

  Parameter sym_tbl : Set.
  Parameter sym_empty : sym_tbl.

  Parameter symbol : nat -> sym_tbl -> t * sym_tbl.
  Parameter name : t -> nat.

  Section TABLE.

    Variable A : Set.

    Parameter table : forall A : Set, Set.
    Parameter empty : table A.
    Parameter enter : table A -> t -> A -> table A.
    Parameter look : table A -> t -> option A.

  End TABLE.

End SYMBOL.

Module Symbol <: SYMBOL.

  Definition t := nat.

  Definition eq (s1 s2 : t) := beq_nat s1 s2.

  (* This should probably be done with typeclasses or something cleaner. *)

  Lemma eq_refl : forall s,
    eq s s = true.
  Proof.
    unfold eq; symmetry; apply beq_nat_refl.
  Qed.

  Lemma eq_sym : forall s1 s2,
    eq s1 s2 = eq s2 s1.
  Proof.
    unfold eq; induction s1; destruct s2; simpl; auto.
  Qed.

  Lemma eq_trans : forall s1 s2 s3,
    eq s1 s2 = true ->
    eq s2 s3 = true ->
    eq s1 s3 = true.
  Proof.
    induction s1; destruct s2, s3; simpl; auto. discriminate. eauto.
  Qed.

  Definition sym_tbl := list t.
  Definition sym_empty : sym_tbl := nil.
  Fixpoint sym_find (tbl : sym_tbl) n :=
    match tbl with
    | nil => None
    | n' :: tbl' => if eq n n' then Some n else sym_find tbl' n
    end.

  Definition symbol (n : nat) tbl : t * sym_tbl :=
    match sym_find tbl n with
    | None => (n, n :: tbl)
    | Some sym => (sym, tbl)
    end.

  Definition symbol' name tbl := fst (symbol name tbl).
  Definition symbolT name tbl := snd (symbol name tbl).

  Definition add_syms tbl names : sym_tbl := fold_right symbolT tbl names.
  Definition make_syms names : sym_tbl := add_syms sym_empty names.

  Definition name (sym : t) := sym.

  Section TABLE.

    Context {A : Set}.

    Definition table := list (t * A).

    Definition empty : table := nil.

    Definition enter (tbl : table) sym val := (sym, val) :: tbl.

    Fixpoint look (tbl : table) sym :=
      match tbl with
      | nil => None
      | (sym', val) :: tbl' => if eq sym sym'
                                 then Some val
                                 else look tbl' sym
      end.

    Definition enter_all (tbl : table) (svs : list (t * A)) :=
      fold_left (fun t sv => enter t (fst sv) (snd sv)) svs tbl.

    Lemma empty_look : forall s,
      look empty s = None.
    Proof. reflexivity. Qed.

    Lemma enter_shadow : forall tbl s v1 v2,
      look tbl s = Some v1 ->
      look (enter tbl s v2) s = Some v2.
    Proof.
      intros; simpl; rewrite eq_refl; reflexivity.
    Qed.

  End TABLE.

End Symbol.
