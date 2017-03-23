(*
 * SemantChecks.v
 * Wolf Honore
 *
 * Tests to ensure that the typing semantics defined in Semant.v
 * match the informal semantics described in the book.
 *)

Require Import Absyn.
Require Import Errors.
Require Import Examples.
Require Import Types.
Require Import Typing.

Section TypeDec_CHECKS.
  (* With soundness this also implies wt_prog ex ty us *)
  Definition checkEx (ex : Absyn.exp) :=
    exists ty us, typeProg ex = OK (ty, us).

  (* With soundness this implies that typeProg ex = ERR *)
  Definition failEx (ex : Absyn.exp) := forall ty us,
    ~(wt_prog ex ty us).

  Ltac inv H := inversion H; subst; clear H.
  Ltac inv_all :=
    match goal with
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
    | [ H : _ \/ _ |- _ ] => inv H
    | [ H : (_, _) = Types.unew _ |- _ ] => inv H
    | [ H : Types.actual_ty _ Types.INT = Some _ |- _ ] => unfold Types.actual_ty in H; simpl in H
    | [ H : Types.actual_ty _ Types.STRING = Some _ |- _ ] => unfold Types.actual_ty in H; simpl in H
    | [ H : Types.actual_ty _ Types.NIL = Some _ |- _ ] => unfold Types.actual_ty in H; simpl in H
    | [ H : Types.actual_ty _ Types.UNIT = Some _ |- _ ] => unfold Types.actual_ty in H; simpl in H
    | [ H : Types.actual_ty _ (Types.ARRAY _ _) = Some _ |- _ ] => unfold Types.actual_ty in H; simpl in H
    | [ H : Types.actual_ty _ (Types.RECORD _ _) = Some _ |- _ ] => unfold Types.actual_ty in H; simpl in H
    | [ H : Types.actual_ty _ (Types.NAME _) = Some _ |- _ ] => unfold Types.actual_ty in H; simpl in H
    | [ H : List.NoDup _ |- _ ] => inv H
    end; simpl in *; try discriminate; try tauto.

  Ltac solve_actual :=
    match goal with
    | [ H : Types.actual_ty _ ?X = Some _ |- _ ] => destruct X; try discriminate
    end.

  Ltac solve :=
    match goal with
    | [ |- checkEx ?E ] => unfold checkEx, E, typeProg; simpl; eauto
    | [ |- failEx ?E ] => unfold failEx, E, not; intros; repeat (repeat inv_all; try solve_actual)
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

  (* Moved to the end *)
  (* Example ex14 : failEx EX14.ex *)

  Example ex15 : failEx EX15.ex.
  Proof. solve. Qed.

  Example ex16 : failEx EX16.ex.
  Proof. solve. Qed.

  Example ex17 : failEx EX17.ex.
  Proof. solve. Qed.

  (* Moved to the end *)
  (* Example ex18 : failEx EX18.ex. *)

  (* Moved to the end *)
  (* Example ex19 : failEx EX19.ex. *)

  (* Moved to the end *)
  (* Example ex20 : failEx EX20.ex. *)

  Example ex21 : failEx EX21.ex.
  Proof. solve. Qed.

  Example ex22 : failEx EX22.ex.
  Proof. solve. Qed.

  Example ex23 : failEx EX23.ex.
  Proof. solve. Qed.

  Example ex24 : failEx EX24.ex.
  Proof. solve. Qed.

  Example ex25 : failEx EX25.ex.
  Proof. solve. Qed.

  Example ex26 : failEx EX26.ex.
  Proof. solve. Qed.

  Example ex27 : checkEx EX27.ex.
  Proof. solve. Qed.

  Example ex28 : failEx EX28.ex.
  Proof. solve. Qed.

  Example ex29 : failEx EX29.ex.
  Proof. solve. Qed.

  Example ex30 : checkEx EX30.ex.
  Proof. solve. Qed.

  Example ex31 : failEx EX31.ex.
  Proof. solve. Qed.

  Example ex32 : failEx EX32.ex.
  Proof. solve. Qed.

  Example ex33 : failEx EX33.ex.
  Proof. solve. Qed.

  Example ex34 : failEx EX34.ex.
  Proof. solve. Qed.

  Example ex35 : failEx EX35.ex.
  Proof. solve. Qed.

  Example ex36 : failEx EX36.ex.
  Proof. solve. Qed.

  Example ex37 : checkEx EX37.ex.
  Proof. solve. Qed.

  Example ex38 : failEx EX38.ex.
  Proof. solve. Qed.

  Example ex39 : failEx EX39.ex.
  Proof. solve. Qed.

  Example ex40 : failEx EX40.ex.
  Proof. solve. Qed.

  Example ex41 : checkEx EX41.ex.
  Proof. solve. Qed.

  Example ex42 : checkEx EX42.ex.
  Proof. solve. Qed.

  Example ex43 : failEx EX43.ex.
  Proof. solve. Qed.

  Example ex44 : checkEx EX44.ex.
  Proof. solve. Qed.

  Example ex45 : failEx EX45.ex.
  Proof. solve. Qed.

  Example ex46 : failEx EX46.ex.
  Proof. solve. Qed.

  Example ex47 : failEx EX47.ex.
  Proof. solve. Qed.

  Example ex48 : checkEx EX48.ex.
  Proof. solve. Qed.

  Example ex49 : checkEx EX49.ex.
  Proof. solve. Qed.

  (* Slow examples *)

  Example ex14 : failEx EX14.ex.
  Proof. solve. Qed.

  Example ex18 : failEx EX18.ex.
  Proof. solve. Qed.

  Example ex19 : failEx EX19.ex.
  Proof. solve. Qed.

  Example ex20 : failEx EX20.ex.
  Proof. solve. Qed.

End TypeDec_CHECKS.
