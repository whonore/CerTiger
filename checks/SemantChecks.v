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
    | [ H : Some _ = None |- _ ] => inv H
    | [ H : None = Some _ |- _ ] => inv H
    | [ H : Some _ = Some _ |- _ ] => inv H
    | [ H : wt_op _ _ _ _ |- _ ] => inv H
    | [ H : wt_fields _ _ _ _ |- _ ] => inv H
    | [ H : wt_ty _ _ _ _ _ |- _ ] => inv H
    | [ H : wt_tydec_heads _ _ _ |- _ ] => inv H
    | [ H : wt_tydecs _ _ _ _ _ |- _ ] => inv H
    | [ H : wt_formals_heads _ _ _ |- _ ] => inv H
    | [ H : wt_formals _ _ _ _ |- _ ] => inv H
    | [ H : wt_fundec_heads _ _ _ |- _ ] => inv H
    | [ H : wt_exp _ _ _ _ _ |- _ ] => inv H
    | [ H : wt_explist _ _ _ _ _ |- _ ] => inv H
    | [ H : wt_var _ _ _ _ _ |- _ ] => inv H
    | [ H : wt_dec _ _ _ _ _ |- _ ] => inv H
    | [ H : wt_declist _ _ _ _ _ |- _ ] => inv H
    | [ H : wt_fundecs _ _ _ _ _  |- _ ] => inv H
    | [ H : wt_prog _ _ _ |- _ ] => inv H
    | [ H : Types.actual_ty _ _ = Some _ |- _ ] => unfold Types.actual_ty in H; simpl in H
    end; simpl in *; try discriminate.

  Ltac solve :=
    match goal with
    | [ |- checkEx ?E ] => unfold checkEx, E, transProg; simpl; eauto
    | [ |- failEx ?E ] => unfold failEx, E, not; intros; repeat inv_all
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

  Example ex12 : checkEx EX12.ex.
  Proof. solve. Qed.

  Example ex13 : failEx EX13.ex.
  Proof. solve. Qed.

  (* Very slow *)
  Example ex14 : failEx EX14.ex.
  Proof. solve. Qed.

  Example ex15 : failEx EX15.ex.
  Proof. solve. Qed.

  Example ex16 : failEx EX16.ex.
  Proof. solve. Qed.

  Example ex17 : failEx EX17.ex.
  Proof. solve. Qed.

  (* Slow *)
  Example ex18 : failEx EX18.ex.
  Proof. solve. Qed.

  (* Slow *)
  Example ex19 : failEx EX19.ex.
  Proof. solve. Qed.

End TypeDec_CHECKS.
