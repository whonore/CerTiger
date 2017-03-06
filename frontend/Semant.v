(*
 * Semant.v
 * Wolf Honore
 *
 * Defines typing semantics and the type checker.
 *)

Require Import Arith.
Require Import List.

Require Import Absyn.
Require Import Env.
Require Import Errors.
Require Import Symbol.
Require Import Types.

Definition tenv := @Symbol.table Types.ty.
Definition venv := @Symbol.table Env.enventry.

(* Will be used later to create IR *)
Module Translate.
  Definition exp := unit.
End Translate.

Record expty := {
  exp : Translate.exp;
  ty : Types.ty
}.

Record composite_env := {
  te : tenv;
  ve : venv;
  ll : nat (* loop-level *)
}.

Definition base_cenv : composite_env :=
  {| ve := Env.base_venv; te := Env.base_tenv; ll := 0 |}.

Definition update_te (ce : composite_env) (te : tenv) :=
  {| te := te; ve := ve ce; ll := ll ce |}.

Definition update_ve (ce : composite_env) (ve : venv) :=
  {| te := te ce; ve := ve; ll := ll ce |}.

Definition incr_ll (ce : composite_env) :=
  {| te := te ce; ve := ve ce; ll := S (ll ce) |}.

Definition reset_ll (ce : composite_env) :=
  {| te := te ce; ve := ve ce; ll := 0 |}.

Section HELPERS.

  (* Some of these should be moved elsewhere *)

  Definition mk_expty ty := {| exp := tt; ty := ty |}.

  Fixpoint list_eq {A} (eq : A -> A -> bool) (xs1 xs2 : list A) : bool :=
    match xs1, xs2 with
    | nil, nil => true
    | x1 :: xs1', x2 :: xs2' => andb (eq x1 x2) (list_eq eq xs1' xs2')
    | _, _ => false
    end.

  Fixpoint list_in {A} (eq : A -> A -> bool) (x : A) (xs : list A) : bool :=
    match xs with
    | nil => false
    | x' :: xs' => orb (eq x x') (list_in eq x xs')
    end.

  Fixpoint list_nodup {A} (fin : A -> list A -> bool) (xs : list A) : bool :=
    match xs with
    | nil => true
    | x :: xs' => andb (negb (fin x xs')) (list_nodup fin xs')
    end.

  Definition tys_compat := list_eq Types.ty_compat.

  Definition syms_eq := list_eq Symbol.eq.
  Definition sym_in := list_in Symbol.eq.
  Definition sym_nodup := list_nodup sym_in.

  Definition rf_in := list_in Types.rf_eq.
  Fixpoint rf_find (s : Symbol.t) (rfs : list Types.rfield) : option Types.rfield :=
    match rfs with
    | nil => None
    | rf :: rfs' => if Symbol.eq s (Types.rf_name rf)
                      then Some rf
                      else rf_find s rfs'
    end.

  Lemma rf_find_name : forall s rf rfs,
    rf_find s rfs = Some rf ->
    Symbol.eq (Types.rf_name rf) s = true.
  Proof.
    intros; induction rfs; inversion H.
    destruct (Symbol.eq s (Types.rf_name a)) eqn:EQ.
    - inversion H1; subst; rewrite Symbol.eq_sym; assumption.
    - auto.
  Qed.

  Lemma rf_find_in : forall s rf rfs,
    rf_find s rfs = Some rf ->
    rf_in rf rfs = true.
  Proof.
    intros; induction rfs; inversion H.
    destruct (Symbol.eq s (Types.rf_name a)) eqn:EQ.
    - inversion H1; subst; unfold rf_in; simpl.
      rewrite Types.rf_eq_refl; reflexivity.
    - unfold rf_in; simpl.
      apply IHrfs in H1; fold (rf_in rf rfs); rewrite H1.
      rewrite Bool.orb_true_r; reflexivity.
  Qed.

  Lemma rf_eq_in : forall rf1 rf2 rfs,
    Types.rf_eq rf1 rf2 = true ->
    rf_in rf1 rfs = rf_in rf2 rfs.
  Proof.
    intros; induction rfs.
    - unfold rf_in; reflexivity.
    - unfold rf_in; simpl.
      fold (rf_in rf1 rfs); fold (rf_in rf2 rfs); rewrite IHrfs.
      destruct (rf_in rf2 rfs); [repeat rewrite Bool.orb_true_r; reflexivity | repeat rewrite Bool.orb_false_r].
      destruct (Types.rf_eq rf1 a) eqn:EQ1; destruct (Types.rf_eq rf2 a) eqn:EQ2; try reflexivity;
      [specialize Types.rf_eq_trans with rf2 rf1 a; intros; apply H0 in EQ1 |
       specialize Types.rf_eq_trans with rf1 rf2 a; intros; apply H0 in EQ2];
      try congruence; eauto using Types.rf_eq_sym.
  Qed.

  Lemma sym_eq_rf_eq : forall s1 s2 ty,
    Symbol.eq s1 s2 = true ->
    Types.rf_eq (Types.mk_rfield s1 ty) (Types.mk_rfield s2 ty) = true.
  Proof.
    intros; unfold Types.rf_eq; simpl; rewrite H.
    destruct (Types.ty_dec ty0 ty0); congruence.
  Qed.

  Fixpoint make_rfs (names : list Symbol.t) (tys : list Types.ty) : list Types.rfield :=
    match names, tys with
    | nil, nil => nil
    | n :: names', ty :: tys' => Types.mk_rfield n ty :: make_rfs names' tys'
    | _, _ => nil
    end.

  Inductive opType : Set :=
    | Arith : opType
    | Ineq : opType
    | Eq : opType.

  Definition getOpType f :=
    match f with
    | PlusOp | MinusOp | TimesOp | DivideOp => Arith
    | LtOp | LeOp | GtOp | GeOp => Ineq
    | EqOp | NeqOp => Eq
    end.

  Fixpoint getVarName v :=
    match v with
    | SimpleVar n => n
    | FieldVar v _ => getVarName v
    | SubscriptVar v _ => getVarName v
    end.

  (* Nestings of NAME greater than Types.max_depth are treated as cycles to remove issue of
     possible non-termination. Since actual_ty already implements this, just check that it
     doesn't return failure. *)
  Fixpoint no_cycles (te : tenv) (ts : list Symbol.t) : bool :=
    match ts with
    | nil => true
    | n :: ts' => as_bool (
        check no_cycles te ts';
        do ty <- lift (Symbol.look te n);
        lift (Types.actual_ty te ty))
    end.

End HELPERS.

Section TYPE_CHECK.

  (* The trans* functions attempt to assign a type to Tiger expressions, but they
     may fail. *)

  Definition transOp (lty rty : Types.ty) (f : opType) : @res expty:=
    if Types.ty_compat lty rty
      then match f with
      | Arith => match lty with
          | Types.INT => OK (mk_expty Types.INT)
          | _ => ERR
          end
      | Ineq => match lty with
          | Types.INT => OK (mk_expty Types.INT)
          | Types.STRING => OK (mk_expty Types.INT)
          | _ => ERR
          end
      | Eq => match lty with
          | Types.INT => OK (mk_expty Types.INT)
          | Types.STRING => OK (mk_expty Types.INT)
          | Types.RECORD _ _ => OK (mk_expty Types.INT)
          | Types.ARRAY _ _ => OK (mk_expty Types.INT)
          | Types.NIL => match rty with
              | Types.RECORD _ _ => OK (mk_expty Types.INT)
              | _ => ERR
              end
          | _ => ERR
        end
      end
      else ERR.

  Fixpoint transFields (te : tenv) (us : Types.upool) (fs : list Symbol.t) : @res (list Types.ty) :=
    match fs with
    | nil => OK nil
    | f :: fs' => do fty <- lift (Symbol.look te f);
                  do ftys <- transFields te us fs';
                  OK (fty :: ftys)
    end.

  Definition transTy (te : tenv) (us : Types.upool) (aty : Absyn.ty) : @res (Types.ty * Types.upool) :=
    match aty with
    | NameTy name => do ty <- lift (Symbol.look te name);
                     OK (ty, us)
    | RecordTy fields => do ftys <- transFields te us (map tf_typ fields);
                         check sym_nodup (map tf_name fields);
                         let (us', u) := Types.unew us in
                         OK (Types.RECORD (make_rfs (map tf_name fields) ftys) u, us')
    | ArrayTy name => do ty <- lift (Symbol.look te name);
                      let (us', u) := Types.unew us in
                      OK (Types.ARRAY ty u, us')
    end.

  Fixpoint transTydecHeads (te : tenv) (decs : list Absyn.tydec) : @res tenv :=
    match decs with
    | nil => OK te
    | dec :: decs' => let te' := Symbol.enter te (td_name dec) (Types.NAME (td_name dec)) in
                      transTydecHeads te' decs'
    end.

  Fixpoint transTydecs (te : tenv) (us : Types.upool) (decs : list Absyn.tydec) : @res (tenv * Types.upool) :=
    match decs with
    | nil => OK (te, us)
    | dec :: decs' => do (dty, us') <- transTy te us (td_ty dec);
                      let te' := Symbol.enter te (td_name dec) dty in
                      transTydecs te' us' decs'
    end.

  Fixpoint transFormalsHeads (te : tenv) (fs : list Absyn.formals) : @res (list Types.ty) :=
    match fs with
    | nil => OK nil
    | f :: fs' => do fty <- lift (Symbol.look te (frm_typ f));
                  do ftys <- transFormalsHeads te fs';
                  OK (fty :: ftys)
    end.

  Fixpoint transFormals (ve : venv) (fs : list Absyn.formals) (ftys : list Types.ty) : @res venv :=
    match fs, ftys with
    | nil, nil => OK ve
    | f :: fs', fty :: ftys' => let ve' := Symbol.enter ve (vd_name (frm_var f)) (Env.VarEntry fty Env.RW) in
                                transFormals ve' fs' ftys'
    | _, _ => ERR
    end.

  Fixpoint transFundecHeads (ce : composite_env) (fds : list Absyn.fundec) : @res composite_env :=
    match fds with
    | nil => OK ce
    | fd :: fds' => check sym_nodup (map (fun p => vd_name (frm_var p)) (fd_params fd));
                    do formtys <- transFormalsHeads (te ce) (fd_params fd);
                    do rty' <- match fd_result fd with
                               | None => OK Types.UNIT
                               | Some rty => lift (Symbol.look (te ce) rty)
                               end;
                    let ve' := Symbol.enter (ve ce) (fd_name fd) (Env.FunEntry formtys rty') in
                    transFundecHeads (update_ve ce ve') fds'
    end.

  Fixpoint transExp (ce : composite_env) (us : Types.upool) (exp : Absyn.exp) : @res (expty * Types.upool) :=
    match exp with
    | VarExp v => transVar ce us v
    | NilExp => OK (mk_expty Types.NIL, us)
    | IntExp _ => OK (mk_expty Types.INT, us)
    | StringExp _ => OK (mk_expty Types.STRING, us)
    | AppExp f args => do entry <- lift (Symbol.look (ve ce) f);
                       match entry with
                       | Env.FunEntry formtys retty =>
                           do (argtys, us') <- transExplist ce us args;
                           do formtys' <- lift (Types.actual_tys (te ce) formtys);
                           do argtys' <- lift (Types.actual_tys (te ce) (map ty argtys));
                           check tys_compat argtys' formtys';
                           OK (mk_expty retty, us')
                       | _ => ERR
                       end
    | OpExp l f r => do (lty, us') <- transExp ce us l;
                     do (rty, us'') <- transExp ce us' r;
                     do lty' <- lift (Types.actual_ty (te ce) (ty lty));
                     do rty' <- lift (Types.actual_ty (te ce) (ty rty));
                     do ty <- transOp lty' rty' (getOpType f);
                     OK (ty, us'')
    | RecordExp fvals fnames rty => do recty <- lift (Symbol.look (te ce) rty);
                                    do recty' <- lift (Types.actual_ty (te ce) recty);
                                    match recty' with
                                    | Types.RECORD fields _ =>
                                        check syms_eq fnames (map Types.rf_name fields);
                                        do (etys, us') <- transExplist ce us fvals;
                                        do etys' <- lift (Types.actual_tys (te ce) (map ty etys));
                                        do fieldtys <- lift (Types.actual_tys (te ce) (map Types.rf_type fields));
                                        check tys_compat etys' fieldtys;
                                        OK (mk_expty recty', us')
                                    | _ => ERR
                                    end
    | SeqExp es => do (etys, us') <- transExplist ce us es;
                   OK (last etys (mk_expty Types.UNIT), us')
    | AssignExp l r => do (vty, us') <- transVar ce us l;
                       do (ety, us'') <- transExp ce us' r;
                       do vty' <- lift (Types.actual_ty (te ce) (ty vty));
                       do ety' <- lift (Types.actual_ty (te ce) (ty ety));
                       check Types.ty_compat vty' ety';
                       match Symbol.look (ve ce) (getVarName l) with
                       | Some (Env.VarEntry _ Env.RW) => OK (mk_expty Types.UNIT, us'')
                       | _ => ERR
                       end
    | IfExp p t (Some e) => do (pty, us') <- transExp ce us p;
                            do (tty, us'') <- transExp ce us' t;
                            do (ety, us''') <- transExp ce us'' e;
                            do pty' <- lift (Types.actual_ty (te ce) (ty pty));
                            do tty' <- lift (Types.actual_ty (te ce) (ty tty));
                            do ety' <- lift (Types.actual_ty (te ce) (ty ety));
                            check Types.ty_compat pty' Types.INT;
                            check Types.ty_compat tty' ety';
                            OK (mk_expty (Types.most_general tty' ety'), us''')
    | IfExp p t None => do (pty, us') <- transExp ce us p;
                        do (tty, us'') <- transExp ce us' t;
                        do pty' <- lift (Types.actual_ty (te ce) (ty pty));
                        do tty' <- lift (Types.actual_ty (te ce) (ty tty));
                        check Types.ty_compat pty' Types.INT;
                        check Types.ty_compat tty' Types.UNIT;
                        OK (mk_expty Types.UNIT, us'')
    | WhileExp g b => do (gty, us') <- transExp ce us g;
                      do (bty, us'') <- transExp (incr_ll ce) us' b;
                      do gty' <- lift (Types.actual_ty (te ce) (ty gty));
                      do bty' <- lift (Types.actual_ty (te ce) (ty bty));
                      check Types.ty_compat gty' Types.INT;
                      check Types.ty_compat bty' Types.UNIT;
                      OK (mk_expty Types.UNIT, us'')
    | ForExp v lo hi b => do (loty, us') <- transExp ce us lo;
                          do (hity, us'') <- transExp ce us' hi;
                          do loty' <- lift (Types.actual_ty (te ce) (ty loty));
                          do hity' <- lift (Types.actual_ty (te ce) (ty hity));
                          check Types.ty_compat loty' Types.INT;
                          check Types.ty_compat hity' Types.INT;
                          let ve' := Symbol.enter (ve ce) (vd_name v) (Env.VarEntry Types.INT Env.RO) in
                          do (bty, us''') <- transExp (incr_ll (update_ve ce ve')) us'' b;
                          do bty' <- lift (Types.actual_ty (te ce) (ty bty));
                          check Types.ty_compat bty' Types.UNIT;
                          OK (mk_expty Types.UNIT, us''')
    | BreakExp => check leb 1 (ll ce);
                  OK (mk_expty Types.UNIT, us)
    | LetExp decs b => do (ce', us') <- transDeclist ce us decs;
                       do (bty, us'') <- transExp ce' us' b;
                       OK (bty, us'')
    | ArrayExp aty sz init => do arrty <- lift (Symbol.look (te ce) aty);
                              do arrty' <- lift (Types.actual_ty (te ce) arrty);
                              do (szty, us') <- transExp ce us sz;
                              do (initty, us'') <- transExp ce us' init;
                              do szty' <- lift (Types.actual_ty (te ce) (ty szty));
                              do initty' <- lift (Types.actual_ty (te ce) (ty initty));
                              check Types.ty_compat szty' Types.INT;
                              match arrty' with
                              | Types.ARRAY elty _ => do elty' <- lift (Types.actual_ty (te ce) elty);
                                                      check Types.ty_compat initty' elty';
                                                      OK (mk_expty arrty', us'')
                              | _ => ERR
                              end
    end
  with transExplist (ce : composite_env) (us : Types.upool) (exps : Absyn.explist) :  @res (list expty * Types.upool) :=
    match exps with
    | ENil => OK (nil, us)
    | ECons e es => do (ety, us') <- transExp ce us e;
                    do (etys, us'') <- transExplist ce us' es;
                    OK (ety :: etys, us'')
    end
  with transVar (ce : composite_env) (us : Types.upool) (var : Absyn.var) : @res (expty * Types.upool) :=
    match var with
    | SimpleVar name => do entry <- lift (Symbol.look (ve ce) name);
                        match entry with
                        | Env.VarEntry ty _ => do ty' <- lift (Types.actual_ty (te ce) ty);
                                               OK (mk_expty ty', us)
                        | _ => ERR
                        end
    | FieldVar v field => do (vty, us') <- transVar ce us v;
                          do vty' <- lift (Types.actual_ty (te ce) (ty vty));
                          match vty' with
                          | Types.RECORD ftys _ =>
                              do field' <- lift (rf_find field ftys);
                              do fieldty <- lift (Types.actual_ty (te ce) (Types.rf_type field'));
                              OK (mk_expty fieldty, us')
                          | _ => ERR
                          end
    | SubscriptVar v idx => do (idxty, us') <- transExp ce us idx;
                            do (vty, us'') <- transVar ce us' v;
                            do idxty' <- lift (Types.actual_ty (te ce) (ty idxty));
                            do vty' <- lift (Types.actual_ty (te ce) (ty vty));
                            check Types.ty_compat idxty' Types.INT;
                            match vty' with
                            | Types.ARRAY elty _ => do elty' <- lift (Types.actual_ty (te ce) elty);
                                                    OK (mk_expty elty', us'')
                            | _ => ERR
                            end
    end
  with transDec (ce : composite_env) (us : Types.upool) (dec : Absyn.dec) : @res (composite_env * Types.upool) :=
    match dec with
    | FunctionDec decs bodies => check sym_nodup (map fd_name decs);
                                 do ce' <- transFundecHeads ce decs;
                                 do us' <- transFundecs ce' us decs bodies;
                                 OK (ce', us')
    | VarDec v None val => do (valty, us') <- transExp ce us val;
                           do valty' <- lift (Types.actual_ty (te ce) (ty valty));
                           match valty' with
                           | Types.NIL => ERR
                           | _ => let ve' := Symbol.enter (ve ce) (vd_name v) (Env.VarEntry (ty valty) Env.RW) in
                                  OK (update_ve ce ve', us')
                           end
    | VarDec v (Some tyname) val => do (valty, us') <- transExp ce us val;
                                    do vty <- lift (Symbol.look (te ce) tyname);
                                    do vty' <- lift (Types.actual_ty (te ce) vty);
                                    do valty' <- lift (Types.actual_ty (te ce) (ty valty));
                                    check Types.ty_compat valty' vty';
                                    let ve' := Symbol.enter (ve ce) (vd_name v) (Env.VarEntry vty Env.RW) in
                                    OK (update_ve ce ve', us')
    | TypeDec decs => check sym_nodup (map td_name decs);
                      do te' <- transTydecHeads (te ce) decs;
                      do (te'', us') <- transTydecs te' us decs;
                      check no_cycles te'' (map td_name decs);
                      OK (update_te ce te'', us')
    end
  with transDeclist (ce : composite_env) (us : Types.upool) (decs : declist) : @res (composite_env * Types.upool) :=
    match decs with
    | DNil => OK (ce, us)
    | DCons d ds => do (ce', us') <- transDec ce us d;
                    do (ce'', us'') <- transDeclist ce' us' ds;
                    OK (ce'', us'')
    end
  with transFundecs (ce : composite_env) (us : Types.upool) (fds : list Absyn.fundec) (bs : Absyn.explist) : @res Types.upool :=
    match fds, bs with
    | nil, ENil => OK us
    | fd :: fds', ECons b bs' => do entry <- lift (Symbol.look (ve ce) (fd_name fd));
                                 match entry with
                                 | Env.FunEntry formtys rty =>
                                     do ve' <- transFormals (ve ce) (fd_params fd) formtys;
                                     do (bty, us') <- transExp (reset_ll (update_ve ce ve')) us b;
                                     do rty' <- lift (Types.actual_ty (te ce) rty);
                                     do bty' <- lift (Types.actual_ty (te ce) (ty bty));
                                     check Types.ty_compat rty' bty';
                                     transFundecs ce us' fds' bs'
                                 | _ => ERR
                                 end
    | _, _ => ERR
    end.

  Definition transProg (tree : Absyn.exp) := transExp base_cenv Types.uinit tree.

End TYPE_CHECK.

Section TYPE_SPEC.

  (* The wt_* inductive relations define the semantics of well-typed Tiger expressions. *)

  Inductive wt_op : Types.ty -> Types.ty -> opType -> Types.ty -> Prop :=
    | wt_arith :
        wt_op Types.INT Types.INT Arith Types.INT
    | wt_ineq_int :
        wt_op Types.INT Types.INT Ineq Types.INT
    | wt_ineq_str :
        wt_op Types.STRING Types.STRING Ineq Types.INT
    | wt_eq_int :
        wt_op Types.INT Types.INT Eq Types.INT
    | wt_eq_str :
        wt_op Types.STRING Types.STRING Eq Types.INT
    | wt_eq_arr : forall aty u,
        wt_op (Types.ARRAY aty u) (Types.ARRAY aty u) Eq Types.INT
    | wt_eq_rec : forall rfs1 rfs2 u,
        wt_op (Types.RECORD rfs1 u) (Types.RECORD rfs2 u) Eq Types.INT
    | wt_eq_lnil : forall rfs u,
        wt_op Types.NIL (Types.RECORD rfs u) Eq Types.INT
    | wt_eq_rnil : forall rfs u,
        wt_op (Types.RECORD rfs u) Types.NIL Eq Types.INT.

  Inductive wt_fields (te : tenv) (us : Types.upool) : list Symbol.t -> list Types.ty -> Prop :=
    | wt_fnil :
        wt_fields te us nil nil
    | wt_fcons : forall f fs fty ftys,
        Symbol.look te f = Some fty ->
        wt_fields te us fs ftys ->
        wt_fields te us (f :: fs) (fty :: ftys).

  Inductive wt_ty (te : tenv) (us : Types.upool) : Absyn.ty -> Types.ty -> Types.upool -> Prop :=
    | wt_namety : forall n ty,
        Symbol.look te n = Some ty ->
        wt_ty te us (NameTy n) ty us
    | wt_recty : forall fs ftys u us',
        sym_nodup (map tf_name fs) = true ->
        wt_fields te us (map tf_typ fs) ftys ->
        (us', u) = Types.unew us ->
        wt_ty te us (RecordTy fs) (Types.RECORD (make_rfs (map tf_name fs) ftys) u) us'
    | wt_arrty : forall n ty u us',
        Symbol.look te n = Some ty ->
        (us', u) = Types.unew us ->
        wt_ty te us (ArrayTy n) (Types.ARRAY ty u) us'.

  Inductive wt_tydec_heads (te : tenv) : list Absyn.tydec -> tenv -> Prop :=
    | wt_tdh_nil :
        wt_tydec_heads te nil te
    | wt_tdh_cons : forall td tds te' te'',
        Symbol.enter te (td_name td) (Types.NAME (td_name td)) = te' ->
        wt_tydec_heads te' tds te'' ->
        wt_tydec_heads te (td :: tds) te''.

  Inductive wt_tydecs (te : tenv) (us : Types.upool) : list Absyn.tydec -> tenv -> Types.upool -> Prop :=
    | wt_td_nil :
        wt_tydecs te us nil te us
    | wt_td_cons : forall td tds ty te' us' te'' us'',
        wt_ty te us (td_ty td) ty us' ->
        Symbol.enter te (td_name td) ty = te' ->
        wt_tydecs te' us' tds te'' us'' ->
        wt_tydecs te us (td :: tds) te'' us''.

  Inductive wt_formals_heads (te : tenv) : list Absyn.formals -> list Types.ty -> Prop :=
    | wt_formhd_nil :
        wt_formals_heads te nil nil
    | wt_formhd_cons : forall f fs ty tys,
        Symbol.look te (frm_typ f) = Some ty ->
        wt_formals_heads te fs tys ->
        wt_formals_heads te (f :: fs) (ty :: tys).

  Inductive wt_formals (ve : venv) : list Absyn.formals -> list Types.ty -> venv -> Prop :=
    | wt_form_nil :
        wt_formals ve nil nil ve
    | wt_form_cons : forall f fs ty tys ve' ve'',
        Symbol.enter ve (vd_name (frm_var f)) (Env.VarEntry ty Env.RW) = ve' ->
        wt_formals ve' fs tys ve'' ->
        wt_formals ve (f :: fs) (ty :: tys) ve''.

  Inductive wt_fundec_heads (ce : composite_env) : list Absyn.fundec -> composite_env -> Prop :=
    | wt_fdh_nil :
        wt_fundec_heads ce nil ce
    | wt_fdh_noty : forall name params fds formtys ve' ce',
        sym_nodup (map (fun p => vd_name (frm_var p)) params) = true ->
        wt_formals_heads (te ce) params formtys ->
        Symbol.enter (ve ce) name (Env.FunEntry formtys Types.UNIT) = ve' ->
        wt_fundec_heads (update_ve ce ve') fds ce' ->
        wt_fundec_heads ce ({| fd_name := name; fd_params := params; fd_result := None|} :: fds) ce'
    | wt_fdh_cons : forall name params fds formtys rty rty' ve' ce',
        sym_nodup (map (fun p => vd_name (frm_var p)) params) = true ->
        wt_formals_heads (te ce) params formtys ->
        Symbol.look (te ce) rty = Some rty' ->
        Symbol.enter (ve ce) name (Env.FunEntry formtys rty') = ve' ->
        wt_fundec_heads (update_ve ce ve') fds ce' ->
        wt_fundec_heads ce ({| fd_name := name; fd_params := params; fd_result := Some rty |} :: fds) ce'.

  (* Some of the actual_ty calls may be redundant, but to be safe there
     should be one before any ty_compat. *)
  Inductive wt_exp (ce : composite_env) (us : Types.upool) : Absyn.exp -> Types.ty -> Types.upool -> Prop :=
    | wt_varexp : forall v ty us',
        wt_var ce us v ty us' ->
        wt_exp ce us (VarExp v) ty us'
    | wt_nilexp :
        wt_exp ce us NilExp Types.NIL us
    | wt_intexp : forall n,
        wt_exp ce us (IntExp n) Types.INT us
    | wt_strexp : forall s,
        wt_exp ce us (StringExp s) Types.STRING us
    | wt_appexp : forall f args argtys formtys argtys' formtys' retty us',
        Symbol.look (ve ce) f = Some (Env.FunEntry formtys retty) ->
        wt_explist ce us args argtys us' ->
        Types.actual_tys (te ce) formtys = Some formtys' ->
        Types.actual_tys (te ce) argtys = Some argtys' ->
        tys_compat argtys' formtys' = true ->
        wt_exp ce us (AppExp f args) retty us'
    | wt_oppexp : forall f l r fty lty rty lty' rty' us' us'',
        wt_exp ce us l lty us' ->
        wt_exp ce us' r rty us'' ->
        Types.actual_ty (te ce) lty = Some lty' ->
        Types.actual_ty (te ce) rty = Some rty' ->
        wt_op lty' rty' (getOpType f) fty ->
        wt_exp ce us (OpExp l f r) fty us''
    | wt_recexp : forall fvals fnames ftys ftys' rty ty u fields fieldtys us',
        Symbol.look (te ce) rty = Some ty ->
        Types.actual_ty (te ce) ty = Some (Types.RECORD fields u) ->
        syms_eq fnames (map Types.rf_name fields) = true ->
        wt_explist ce us fvals ftys us' ->
        Types.actual_tys (te ce) (map Types.rf_type fields) = Some fieldtys ->
        Types.actual_tys (te ce) ftys = Some ftys' ->
        tys_compat ftys' fieldtys = true ->
        wt_exp ce us (RecordExp fvals fnames rty) (Types.RECORD fields u) us'
    | wt_seqexp : forall es tys ty us',
        wt_explist ce us es tys us' ->
        ty = last tys Types.UNIT ->
        wt_exp ce us (SeqExp es) ty us'
    | wt_assignexp : forall v e vty ety vty' ety' us' us'' ty,
        wt_var ce us v vty us' ->
        wt_exp ce us' e ety us'' ->
        Types.actual_ty (te ce) vty = Some vty' ->
        Types.actual_ty (te ce) ety = Some ety' ->
        Types.ty_compat vty' ety' = true ->
        Symbol.look (ve ce) (getVarName v) = Some (Env.VarEntry ty Env.RW) ->
        wt_exp ce us (AssignExp v e) Types.UNIT us''
    | wt_ifthenelseexp : forall p t e pty tty ety tty' ety' us' us'' us''',
        wt_exp ce us p pty us' ->
        wt_exp ce us' t tty us'' ->
        wt_exp ce us'' e ety us''' ->
        Types.actual_ty (te ce) pty = Some Types.INT ->
        Types.actual_ty (te ce) tty = Some tty' ->
        Types.actual_ty (te ce) ety = Some ety' ->
        Types.ty_compat tty' ety' = true ->
        wt_exp ce us (IfExp p t (Some e)) (Types.most_general tty' ety') us'''
    | wt_ifthenexp : forall p t pty tty us' us'',
        wt_exp ce us p pty us' ->
        wt_exp ce us' t tty us'' ->
        Types.actual_ty (te ce) pty = Some Types.INT ->
        Types.actual_ty (te ce) tty = Some Types.UNIT ->
        wt_exp ce us (IfExp p t None) Types.UNIT us''
    | wt_whileexp : forall g b gty bty us' us'',
        wt_exp ce us g gty us' ->
        wt_exp (incr_ll ce) us' b bty us'' ->
        Types.actual_ty (te ce) gty = Some Types.INT ->
        Types.actual_ty (te ce) bty = Some Types.UNIT ->
        wt_exp ce us (WhileExp g b) Types.UNIT us''
    | wt_forexp : forall v lo hi loty hity b bty us' us'' us''' ve',
        wt_exp ce us lo loty us' ->
        wt_exp ce us' hi hity us'' ->
        Types.actual_ty (te ce) loty = Some Types.INT ->
        Types.actual_ty (te ce) hity = Some Types.INT ->
        Symbol.enter (ve ce) (vd_name v) (Env.VarEntry Types.INT Env.RO) = ve' ->
        wt_exp (incr_ll (update_ve ce ve')) us'' b bty us''' ->
        Types.actual_ty (te ce) bty = Some Types.UNIT ->
        wt_exp ce us (ForExp v lo hi b) Types.UNIT us'''
    | wt_breakexp :
        0 < ll ce ->
        wt_exp ce us BreakExp Types.UNIT us
    | wt_letexp : forall decs e ty ce' us' us'',
        wt_declist ce us decs ce' us' ->
        wt_exp ce' us' e ty us'' ->
        wt_exp ce us (LetExp decs e) ty us''
    | wt_arrexp : forall aty ty ty' ty'' sz szty init initty initty' u us' us'',
        Symbol.look (te ce) aty = Some ty ->
        Types.actual_ty (te ce) ty = Some (Types.ARRAY ty' u) ->
        wt_exp ce us sz szty us' ->
        wt_exp ce us' init initty us'' ->
        Types.actual_ty (te ce) szty = Some Types.INT ->
        Types.actual_ty (te ce) ty' = Some ty'' ->
        Types.actual_ty (te ce) initty = Some initty' ->
        Types.ty_compat ty'' initty' = true ->
        wt_exp ce us (ArrayExp aty sz init) (Types.ARRAY ty' u) us''
  with wt_explist (ce : composite_env) (us : Types.upool) : Absyn.explist -> list Types.ty -> Types.upool -> Prop :=
    | wt_enil :
        wt_explist ce us ENil nil us
    | wt_econs : forall e ty es tys us' us'',
        wt_exp ce us e ty us' ->
        wt_explist ce us' es tys us'' ->
        wt_explist ce us (ECons e es) (ty :: tys) us''
  with wt_var (ce : composite_env) (us : Types.upool) : Absyn.var -> Types.ty -> Types.upool -> Prop :=
    | wt_svar : forall n ty ty' rw,
        Symbol.look (ve ce) n = Some (Env.VarEntry ty rw) ->
        Types.actual_ty (te ce) ty = Some ty' ->
        wt_var ce us (SimpleVar n) ty' us
    | wt_fvar : forall v vty f fs u ty ty' us',
        wt_var ce us v vty us' ->
        Types.actual_ty (te ce) vty = Some (Types.RECORD fs u) ->
        rf_in (Types.mk_rfield f ty) fs = true ->
        Types.actual_ty (te ce) ty = Some ty' ->
        wt_var ce us (FieldVar v f) ty' us'
    | wt_ssvar : forall v idx u idxty vty ty ty' us' us'',
        wt_exp ce us idx idxty us' ->
        wt_var ce us' v vty us'' ->
        Types.actual_ty (te ce) idxty = Some Types.INT ->
        Types.actual_ty (te ce) vty = Some (Types.ARRAY ty u) ->
        Types.actual_ty (te ce) ty = Some ty' ->
        wt_var ce us (SubscriptVar v idx) ty' us''
  with wt_dec (ce : composite_env) (us : Types.upool) : Absyn.dec -> composite_env -> Types.upool -> Prop :=
    | wt_fundec : forall fs bs ce' us',
        sym_nodup (map fd_name fs) = true ->
        wt_fundec_heads ce fs ce' ->
        wt_fundecs ce' us fs bs us' ->
        wt_dec ce us (FunctionDec fs bs) ce' us'
    | wt_vardec_noty : forall v e ety ety' ve' us',
        wt_exp ce us e ety us' ->
        Types.actual_ty (te ce) ety = Some ety' ->
        ety' <> Types.NIL ->
        Symbol.enter (ve ce) (vd_name v) (Env.VarEntry ety Env.RW) = ve' ->
        wt_dec ce us (VarDec v None e) (update_ve ce ve') us'
    | wt_vardec_ty : forall v e tyname ty ty' ety ety' ve' us',
        Symbol.look (te ce) tyname = Some ty ->
        wt_exp ce us e ety us' ->
        Types.actual_ty (te ce) ty = Some ty' ->
        Types.actual_ty (te ce) ety = Some ety' ->
        Types.ty_compat ety' ty' = true ->
        Symbol.enter (ve ce) (vd_name v) (Env.VarEntry ty Env.RW) = ve' ->
        wt_dec ce us (VarDec v (Some tyname) e) (update_ve ce ve') us'
    | wt_tydec : forall tds te' te'' us',
        sym_nodup (map td_name tds) = true ->
        wt_tydec_heads (te ce) tds te' ->
        wt_tydecs te' us tds te'' us' ->
        no_cycles te'' (map td_name tds) = true ->
        wt_dec ce us (TypeDec tds) (update_te ce te'') us'
  with wt_declist (ce : composite_env) (us : Types.upool) : declist -> composite_env -> Types.upool -> Prop :=
    | wt_dnil :
        wt_declist ce us DNil ce us
    | wt_dcons : forall d ds ce' ce'' us' us'',
        wt_dec ce us d ce' us' ->
        wt_declist ce' us' ds ce'' us'' ->
        wt_declist ce us (DCons d ds) ce'' us''
  with wt_fundecs (ce : composite_env) (us : Types.upool) : list Absyn.fundec -> Absyn.explist -> Types.upool -> Prop :=
    | wt_fd_nil :
        wt_fundecs ce us nil ENil us
    | wt_fd_cons : forall fd fds b bs formtys rty rty' bty bty' us' us'' ve',
        Symbol.look (ve ce) (fd_name fd) = Some (Env.FunEntry formtys rty) ->
        wt_formals (ve ce) (fd_params fd) formtys ve' ->
        wt_exp (reset_ll (update_ve ce ve')) us b bty us' ->
        Types.actual_ty (te ce) rty = Some rty' ->
        Types.actual_ty (te ce) bty = Some bty' ->
        Types.ty_compat rty' bty' = true ->
        wt_fundecs ce us' fds bs us'' ->
        wt_fundecs ce us (fd :: fds) (ECons b bs) us''.

  Inductive wt_prog : Absyn.exp -> Types.ty -> Types.upool -> Prop :=
    | wt_prog_exp : forall p ty us',
        wt_exp base_cenv Types.uinit p ty us' ->
        wt_prog p ty us'.

End TYPE_SPEC.

Section SOUNDNESS.

  (* Proofs that if transProg returns success with some type, then the program
     is well-typed with respect to the wt_prog semantics. *)

  Ltac type_subst := match goal with
                     | [ H1 : lift (Types.actual_ty _ ?X) = OK ?Y,
                         H2 : Types.ty_compat ?Y ?Z = true
                         |- Types.actual_ty _ ?X = Some ?Z ] =>
                       solve [apply Types.ty_compat_simpl_eq in H2; apply lift_option in H1; subst; auto]
                     end.

  Ltac sound_solve H := monadInv H; econstructor; eauto; try type_subst.

  Local Hint Resolve lift_option.
  Local Hint Resolve Types.ty_compat_sym.

  Lemma transOp_sound : forall l r f ety,
    transOp l r f = OK ety ->
    wt_op l r f (ty ety).
  Proof.
    destruct f; intros; monadInv H; try (destruct r; try discriminate); try solve [constructor].
    apply Types.ty_compat_rec in EQ; subst; constructor.
    eapply Types.ty_compat_arr in EQ; eauto; inversion EQ; constructor.
  Qed.
  Local Hint Resolve transOp_sound.

  Lemma transFields_sound : forall te us fs tys,
    transFields te us fs = OK tys ->
    wt_fields te us fs tys.
  Proof.
    induction fs; intros; sound_solve H.
  Qed.
  Local Hint Resolve transFields_sound.

  Lemma transTy_sound : forall te us abty ty us',
    transTy te us abty = OK (ty, us') ->
    wt_ty te us abty ty us'.
  Proof.
    destruct abty; intros; sound_solve H.
  Qed.
  Local Hint Resolve transTy_sound.

  Lemma transTydecHeads_sound : forall te tds te',
    transTydecHeads te tds = OK te' ->
    wt_tydec_heads te tds te'.
  Proof.
    intros; generalize dependent te0; induction tds; intros; [sound_solve H | econstructor; eauto].
  Qed.
  Local Hint Resolve transTydecHeads_sound.

  Lemma transTydecs_sound : forall te us tds te' us',
    transTydecs te us tds = OK (te', us') ->
    wt_tydecs te us tds te' us'.
  Proof.
    intros; generalize dependent te0; generalize dependent us; induction tds; intros; sound_solve H.
  Qed.
  Local Hint Resolve transTydecs_sound.

  Lemma transFormalsHeads_sound : forall te fs tys,
    transFormalsHeads te fs = OK tys ->
    wt_formals_heads te fs tys.
  Proof.
    induction fs; intros; sound_solve H.
  Qed.
  Local Hint Resolve transFormalsHeads_sound.

  Lemma transFormals_sound : forall ve fs ftys ve',
    transFormals ve fs ftys = OK ve' ->
    wt_formals ve fs ftys ve'.
  Proof.
    intros; generalize dependent ftys; generalize dependent ve0; induction fs; intros; sound_solve H.
  Qed.
  Local Hint Resolve transFormals_sound.

  Lemma transFundecHeads_sound : forall ce fds ce',
    transFundecHeads ce fds = OK ce' ->
    wt_fundec_heads ce fds ce'.
  Proof.
    intros; generalize dependent ce; induction fds; intros; try (destruct a; destruct fd_result); sound_solve H.
  Qed.
  Local Hint Resolve transFundecHeads_sound.

  Theorem transExp_sound : forall ce us e ety us',
    transExp ce us e = OK (ety, us') ->
    wt_exp ce us e (ty ety) us'
  with transExplist_sound : forall ce us es etys us',
    transExplist ce us es = OK (etys, us') ->
    wt_explist ce us es (map ty etys) us'
  with transVar_sound : forall ce us v ety us',
    transVar ce us v = OK (ety, us') ->
    wt_var ce us v (ty ety) us'
  with transDec_sound : forall ce us d ce' us',
    transDec ce us d = OK (ce', us') ->
    wt_dec ce us d ce' us'
  with transDeclist_sound : forall ce us ds ce' us',
    transDeclist ce us ds = OK (ce', us') ->
    wt_declist ce us ds ce' us'
  with transFundecs_sound : forall ce us fds bs us',
    transFundecs ce us fds bs = OK us' ->
    wt_fundecs ce us fds bs us'.
  Proof.
    - destruct e; intros; try solve [sound_solve H].
      + simpl in H; constructor; auto.
      + monadInv H; destruct e.
        * monadInv EQ; econstructor; [econstructor | reflexivity].
        * monadInv EQ; econstructor.
          econstructor; eauto.
          assert (Htymap : forall xs d, ty (last xs d) = last (map ty xs) (ty d)).
          { induction xs.
            - reflexivity.
            - intros; simpl; rewrite <- IHxs; destruct xs; reflexivity.
          }
          apply Htymap.
      + monadInv H; constructor.
        unfold lt; fold (leb 1 (ll ce)) in EQ; auto using leb_complete.
    - destruct es; intros; sound_solve H.
    - destruct v; intros;
      try solve [sound_solve H].
      + monadInv H; econstructor; eauto.
        { apply lift_option in EQ0.
          pose proof EQ0.
          apply rf_find_in in EQ0.
          apply rf_find_name in H.
          erewrite rf_eq_in. eassumption.
          apply sym_eq_rf_eq.
          fold (Types.rf_name x2).
          rewrite Symbol.eq_sym; assumption.
        }
    - destruct d; intros.
      + sound_solve H.
      + destruct o; monadInv H; econstructor; eauto; congruence.
      + sound_solve H.
    - destruct ds; intros; sound_solve H.
    - destruct bs; intros; sound_solve H.
  Qed.

  Local Hint Resolve transExp_sound.

  Theorem transProg_sound : forall p ety us',
    transProg p = OK (ety, us') ->
    wt_prog p (ty ety) us'.
  Proof.
    unfold transProg; constructor; auto.
  Qed.

End SOUNDNESS.
