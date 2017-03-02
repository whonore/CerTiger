Require Import Arith.
Require Import List.
Require Import String.

Module Type SYMBOL.

  Parameter t : Set.
  Parameter eq : t -> t -> bool.

  Parameter sym_tbl : Set.
  Parameter sym_empty : sym_tbl.

  Parameter symbol : string -> sym_tbl -> t * sym_tbl.
  Parameter name : t -> string.

  Section TABLE.

    Variable A : Set.

    Parameter table : forall A : Set, Set.
    Parameter empty : table A.
    Parameter enter : table A -> t -> A -> table A.
    Parameter look : table A -> t -> option A.

  End TABLE.

End SYMBOL.

Module Symbol <: SYMBOL.

  Definition t := (string * nat)%type.

  Definition eq (s1 s2 : t) := beq_nat (snd s1) (snd s2).

  (* This should probably be done with typeclasses or something cleaner *)

  Lemma eq_refl : forall s,
    eq s s = true.
  Proof.
    unfold eq; symmetry; apply beq_nat_refl.
  Qed.

  Lemma eq_sym : forall s1 s2,
    eq s1 s2 = eq s2 s1.
  Proof.
    unfold eq; destruct s1, s2; simpl;
    generalize dependent n0; induction n; destruct n0; simpl; auto.
  Qed.

  Lemma eq_trans : forall s1 s2 s3,
    eq s1 s2 = true ->
    eq s2 s3 = true ->
    eq s1 s3 = true.
  Proof.
    unfold eq; intros; destruct s1, s2, s3; simpl in *.
    generalize dependent n1; generalize dependent n0.
    induction n; intros; destruct n0, n1; auto.
    discriminate.
    eapply IHn; eauto.
  Qed.

  Definition sym_tbl := list t.
  Definition sym_empty : sym_tbl := nil.
  Fixpoint sym_find (tbl : sym_tbl) name :=
    match tbl with
    | nil => None
    | (s, n) :: tbl' => if string_dec s name
                            then Some n
                            else sym_find tbl' name
    end.

  Definition next_sym (tbl : sym_tbl) :=
    S (fold_left (fun m s => max m (snd s)) tbl 0).

  Definition symbol (name : string) tbl : t * sym_tbl :=
    match sym_find tbl name with
    | None => let num := next_sym tbl in ((name, num), (name, num) :: tbl)
    | Some n => ((name, n), tbl)
    end.

  Definition symbol' name tbl := fst (symbol name tbl).
  Definition symbolT name tbl := snd (symbol name tbl).

  Definition name (sym : t) := fst sym.

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
