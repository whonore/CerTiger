(*
 * Symbol.v
 * Wolf Honore
 *
 * Defines the type used to represent identifiers.
 *)

Require Import Arith.
Require Import DecEqFacts.
Require Import List.

Require Import Unique.

Module Type SYMBOL.

  Parameter t : Set.
  Parameter eq : forall (t1 t2 : t), {t1 = t2} + {t1 <> t2}.

  Parameter sym_tbl : Set.
  Parameter sym_empty : sym_tbl.

  Parameter symbol : nat -> sym_tbl -> t * sym_tbl.
  Parameter name : t -> nat.

  Section TABLE.

    Context {A : Set}.

    Parameter table : forall A : Set, Set.
    Parameter empty : table A.
    Parameter enter : table A -> t -> A -> table A.
    Parameter look : table A -> t -> option A.

    Hypothesis look_empty : forall s,
      look empty s = None.

    Hypothesis look_enter_same : forall tbl s v,
      look (enter tbl s v) s = Some v.

    Hypothesis look_enter_other : forall tbl s1 s2 v,
      s1 <> s2 ->
      look (enter tbl s1 v) s2 = look tbl s2.

  End TABLE.

End SYMBOL.

Module Symbol <: SYMBOL.

  Definition t := nat.

  Definition eq := eq_nat_dec.

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

  Definition name (sym : t) := sym.

  Definition add_syms tbl names : sym_tbl := fold_right symbolT tbl names.
  Definition make_syms names : sym_tbl := add_syms sym_empty names.

  Section TABLE.

    Context {A : Set}.

    Definition table := list (t * A).

    Definition empty : table := nil.

    Definition enter (tbl : table) sym val := (sym, val) :: tbl.

    Fixpoint look (tbl : table) (sym : t) :=
      match tbl with
      | nil => None
      | (sym', val) :: tbl' => if eq sym sym'
                                 then Some val
                                 else look tbl' sym
      end.

    Definition enter_all (tbl : table) (svs : list (t * A)) :=
      fold_left (fun t sv => enter t (fst sv) (snd sv)) svs tbl.

    Lemma look_empty : forall s,
      look empty s = None.
    Proof. reflexivity. Qed.

    Lemma look_enter_same : forall tbl s v,
      look (enter tbl s v) s = Some v.
    Proof.
      intros; simpl; apply eq_refl.
    Qed.

    Lemma look_enter_other : forall tbl s1 s2 v,
      s1 <> s2 ->
      look (enter tbl s1 v) s2 = look tbl s2.
    Proof.
      intros. simpl. rewrite eq_false; congruence.
    Qed.

  End TABLE.

End Symbol.

Module SymUnique <: UNIQUE.

  Definition t := Symbol.t.

  Definition init : list t := NatUnique.init.
  Definition new : list t -> (list t * t) := NatUnique.new.
  Definition eq : forall (u1 u2 : t), {u1 = u2} + {u1 <> u2} := NatUnique.eq.

  Definition is_unique (us : list t) : Prop := NoDup us.

  Lemma init_unique : is_unique init.
  Proof NatUnique.init_unique.

  Lemma new_spec : forall u us us',
    is_unique us ->
    new us = (us', u) ->
    In u us' /\ is_unique us'.
  Proof NatUnique.new_spec.

End SymUnique.
