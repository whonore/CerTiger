Require Import Absyn.
Require Import Errors.
Require Import Examples.
Require Import Semant.
Require Import Types.

Section TypeDec_CHECKS.
  (* With soundness this also implies wt_prog ex ty us *)
  Definition checkEx (ex : Absyn.exp) :=
    exists ty us, transProg ex = OK (ty, us).

  (* With soundness this implies that transProg ex = ERR *)
  Definition failEx (ex : Absyn.exp) := forall ty us,
    ~(wt_prog ex ty us).

  Ltac inv H := inversion H; subst; clear H.
  Ltac inv_all :=
    repeat match goal with
    | [ H : wt_prog _ _ _ |- _ ] => inv H
    | [ H : wt_exp _ _ _ _ _ |- _ ] => inv H
    | [ H : wt_op _ _ _ _ |- _ ] => inv H
    | [ H : Some _ = Some _ |- _ ] => inv H
    | [ H : Some _ = None |- _ ] => inv H
    | [ H : None = Some _ |- _ ] => inv H
    | [ H : None = None |- _ ] => inv H
    | [ H : Types.actual_ty _ Types.STRING = Some _ |- _] => unfold Types.actual_ty in H; simpl in H
    | [ H : Types.actual_ty _ Types.INT = Some _ |- _] => unfold Types.actual_ty in H; simpl in H
    end; simpl in *; try discriminate.

  Ltac solve :=
    match goal with
    | [ |- checkEx ?E ] => unfold checkEx, E, transProg; simpl; eauto
    | [ |- failEx ?E ] => unfold failEx, E, not; intros; inv_all
    end.

  Example ex1 : checkEx EX1.ex.
  Proof. solve. Qed.

  Example ex2 : checkEx EX2.ex.
  Proof. solve. Qed.

  Example ex3 : checkEx EX3.ex.
  Proof. solve. Qed.

  Example ex4 : checkEx EX4.ex.
  Proof. solve. Qed.

  Example ex5 : checkEx EX5.ex.
  Proof. solve. Qed.

  Example ex6 : checkEx EX6.ex.
  Proof. solve. Qed.

  Example ex7 : checkEx EX7.ex.
  Proof. solve. Qed.

  Example ex8 : checkEx EX8.ex.
  Proof. solve. Qed.

  Example ex9 : failEx EX9.ex.
  Proof. solve. Qed.

  Example ex10 : failEx EX10.ex.
  Proof. solve. Qed.

  Example ex11 : failEx EX11.ex.
  Proof. solve. Qed.

End TypeDec_CHECKS.
