Require Import Absyn.
Require Import Errors.
Require Import Examples.
Require Import Semant.
Require Import Types.

Section TypeDec_CHECKS.

  Definition checkEx (ex : Absyn.exp) :=
    exists ty us, transProg ex = OK (ty, us).

  Ltac solve := 
    match goal with
    | [ |- checkEx ?E ] => unfold checkEx; unfold E; unfold transProg; simpl; eauto
    end.

  Example ex1 : checkEx EX1.ex.
  Proof. solve. Qed.

  Example ex2 : checkEx EX2.ex.
  Proof. solve. Qed.

  Example ex3 : checkEx EX3.ex.
  Proof. solve. Qed.

End TypeDec_CHECKS.
