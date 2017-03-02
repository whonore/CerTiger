Require Import Arith.
Require Import List.

Require Import Absyn.
Require Import Env.
Require Import Errors.
Require Import Symbol.
Require Import Types.

Definition tenv := @Symbol.table Types.ty.
Definition venv := @Symbol.table Env.enventry.
Definition ros := @Symbol.table unit.

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
  ro : ros; (* read-only variables *)
  ll : nat (* loop-level *)
}.

Definition base_cenv : composite_env :=
  {| ve := Env.base_venv; te := Env.base_tenv; ro := Symbol.empty; ll := 0 |}.

Definition update_te (ce : composite_env) (te : tenv) :=
  {| te := te; ve := ve ce; ro := ro ce; ll := ll ce |}.

Definition update_ve (ce : composite_env) (ve : venv) :=
  {| te := te ce; ve := ve; ro := ro ce; ll := ll ce |}.

Definition update_ro (ce : composite_env) (ro : ros) :=
  {| te := te ce; ve := ve ce; ro := ro; ll := ll ce |}.

Definition incr_ll (ce : composite_env) :=
  {| te := te ce; ve := ve ce; ro := ro ce; ll := S (ll ce) |}.

Section HELPERS.

(* Some of these should be moved elsewhere *)

Definition mk_expty ty := {| exp := tt; ty := ty |}.
Definition tmp : @res (expty * Types.upool) := ERR.

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

End HELPERS.

Section TYPE_CHECK.

Definition transOp (lty rty : expty) (f : opType) : @res expty:=
  if Types.ty_compat (ty lty) (ty rty)
    then match f with
    | Arith => match (ty lty) with
        | Types.INT => OK (mk_expty Types.INT)
        | _ => ERR
        end
    | Ineq => match (ty lty) with
        | Types.INT => OK (mk_expty Types.INT)
        | Types.STRING => OK (mk_expty Types.INT)
        | _ => ERR
        end
    | Eq => match (ty lty) with
        | Types.INT => OK (mk_expty Types.INT)
        | Types.STRING => OK (mk_expty Types.INT)
        | Types.RECORD _ _ => OK (mk_expty Types.INT)
        | Types.ARRAY _ _ => OK (mk_expty Types.INT)
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

Definition transTy (te : tenv) (us : Types.upool) (tree : Absyn.ty) : @res (Types.ty * Types.upool) :=
  match tree with
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
                         check tys_compat (map ty argtys) formtys;
                         OK (mk_expty retty, us')
                     | _ => ERR
                     end
  | OpExp l f r => do (lty, us') <- transExp ce us l;
                   do (rty, us'') <- transExp ce us' r;
                   do ty <- transOp lty rty (getOpType f);
                   OK (ty, us'')
  | RecordExp fvals fnames rty => do recty <- lift (Symbol.look (te ce) rty);
                                  do recty' <- lift (Types.actual_ty recty);
                                  match recty' with
                                  | Types.RECORD fields _ =>
                                      check syms_eq fnames (map Types.rf_name fields);
                                      do (etys, us') <- transExplist ce us fvals;
                                      check tys_compat (map ty etys) (map Types.rf_type fields);
                                      OK (mk_expty recty', us')
                                  | _ => ERR
                                  end
  | SeqExp es => do (etys, us') <- transExplist ce us es;
                 OK (last etys (mk_expty Types.UNIT), us')
  | AssignExp l r => do (vty, us') <- transVar ce us l;
                     do (ety, us'') <- transExp ce us' r;
                     check Types.ty_compat (ty vty) (ty ety);
                     match Symbol.look (ro ce) (getVarName l) with
                     | None => OK (mk_expty Types.UNIT, us'')
                     | _ => ERR
                     end
  | IfExp p t (Some e) => do (pty, us') <- transExp ce us p;
                          do (tty, us'') <- transExp ce us' t;
                          do (ety, us''') <- transExp ce us'' e;
                          check Types.ty_compat (ty pty) Types.INT;
                          check Types.ty_compat (ty tty) (ty ety);
                          OK (tty, us''')
  | IfExp p t None => do (pty, us') <- transExp ce us p;
                      do (tty, us'') <- transExp ce us' t;
                      check Types.ty_compat (ty pty) Types.INT;
                      check Types.ty_compat (ty tty) Types.UNIT;
                      OK (mk_expty Types.UNIT, us'')
  | WhileExp g b => do (gty, us') <- transExp ce us g;
                    do (bty, us'') <- transExp (incr_ll ce) us' b;
                    check Types.ty_compat (ty gty) Types.INT;
                    check Types.ty_compat (ty bty) Types.UNIT;
                    OK (mk_expty Types.UNIT, us'')
  | ForExp v lo hi b => do (loty, us') <- transExp ce us lo;
                        do (hity, us'') <- transExp ce us' hi;
                        check Types.ty_compat (ty loty) Types.INT;
                        check Types.ty_compat (ty hity) Types.INT;
                        let ve' := Symbol.enter (ve ce) (vd_name v) (Env.VarEntry Types.INT) in
                        let ro' := Symbol.enter (ro ce) (vd_name v) tt in
                        do (bty, us''') <- transExp (incr_ll (update_ve (update_ro ce ro') ve')) us'' b;
                        check Types.ty_compat (ty bty) Types.UNIT;
                        OK (mk_expty Types.UNIT, us''')
  | BreakExp => check leb 1 (ll ce);
                OK (mk_expty Types.UNIT, us)
  | LetExp decs b => do (ce', us') <- transDeclist ce us decs;
                     do (bty, us'') <- transExp ce' us' b;
                     OK (bty, us'')
  | ArrayExp aty sz init => do arrty <- lift (Symbol.look (te ce) aty);
                            do (szty, us') <- transExp ce us sz;
                            do (initty, us'') <- transExp ce us' init;
                            check Types.ty_compat (ty szty) Types.INT;
                            match arrty with
                            | Types.ARRAY elty _ => check Types.ty_compat (ty initty) elty;
                                                    OK (mk_expty arrty, us'')
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
                      | Env.VarEntry ty => do ty' <- lift (Types.actual_ty ty);
                                           OK (mk_expty ty', us)
                      | _ => ERR
                      end
  | FieldVar v field => do (vty, us') <- transVar ce us v;
                        match ty vty with
                        | Types.RECORD ftys _ =>
                            do field' <- lift (rf_find field ftys);
                            do fieldty <- lift (Types.actual_ty (Types.rf_type field'));
                            OK (mk_expty fieldty, us')
                        | _ => ERR
                        end
  | SubscriptVar v idx => do (idxty, us') <- transExp ce us idx;
                          do (vty, us'') <- transVar ce us' v;
                          check Types.ty_compat (ty idxty) Types.INT;
                          match ty vty with
                          | Types.ARRAY elty _ => do elty' <- lift (Types.actual_ty elty);
                                                  OK (mk_expty elty', us'')
                          | _ => ERR
                          end
  end
with transDec (ce : composite_env) (us : Types.upool) (dec : Absyn.dec) : @res (composite_env * Types.upool) :=
  match dec with
  | FunctionDec decs => OK (ce, us) (* tmp *)
  | VarDec v None val => do (valty, us') <- transExp ce us val;
                         match ty valty with
                         | Types.NIL => ERR
                         | _ => let ve' := Symbol.enter (ve ce) (vd_name v) (Env.VarEntry (ty valty)) in
                                OK (update_ve ce ve', us')
                         end
  | VarDec v (Some tyname) val => do (valty, us') <- transExp ce us val;
                                  do vty <- lift (Symbol.look (te ce) tyname);
                                  do vty' <- lift (Types.actual_ty vty);
                                  check Types.ty_compat (ty valty) vty';
                                  let ve' := Symbol.enter (ve ce) (vd_name v) (Env.VarEntry (ty valty)) in
                                  OK (update_ve ce ve', us')
  | TypeDec decs => OK (ce, us) (* tmp *)
  end
with transDeclist (ce : composite_env) (us : Types.upool) (decs : declist) : @res (composite_env * Types.upool) :=
  match decs with
  | DNil => OK (ce, us)
  | DCons d ds => do (ce', us') <- transDec ce us d;
                  do (ce'', us'') <- transDeclist ce' us' ds;
                  OK (ce'', us'')
  end.

Definition transProg (tree : Absyn.exp) := transExp base_cenv Types.uinit tree.

End TYPE_CHECK.

Section TYPE_SPEC.

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
  | wt_eq_rec : forall rty u,
      wt_op (Types.RECORD rty u) (Types.RECORD rty u) Eq Types.INT
  | wt_eq_lnil : forall rty u,
      wt_op Types.NIL (Types.RECORD rty u) Eq Types.INT
  | wt_eq_rnil : forall rty u,
      wt_op (Types.RECORD rty u) Types.NIL Eq Types.INT.

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
  | wt_appexp : forall f args argtys formtys retty us',
      Symbol.look (ve ce) f = Some (Env.FunEntry formtys retty) ->
      wt_explist ce us args argtys us' ->
      tys_compat argtys formtys = true ->
      wt_exp ce us (AppExp f args) retty us'
  | wt_oppexp : forall f l r fty lty rty us' us'',
      wt_exp ce us l lty us' ->
      wt_exp ce us' r rty us'' ->
      wt_op lty rty (getOpType f) fty ->
      wt_exp ce us (OpExp l f r) fty us''
  | wt_recexp : forall fvals fnames ftys rty ty u fields us',
      Symbol.look (te ce) rty = Some ty ->
      Types.actual_ty ty = Some (Types.RECORD fields u) ->
      syms_eq fnames (map Types.rf_name fields) = true ->
      wt_explist ce us fvals ftys us' ->
      tys_compat ftys (map Types.rf_type fields) = true ->
      wt_exp ce us (RecordExp fvals fnames rty) (Types.RECORD fields u) us'
  | wt_seqexp : forall es tys ty us',
      wt_explist ce us es tys us' ->
      ty = last tys Types.UNIT ->
      wt_exp ce us (SeqExp es) ty us'
  | wt_assignexp : forall v e vty ety us' us'',
      wt_var ce us v vty us' ->
      wt_exp ce us' e ety us'' ->
      Types.ty_compat vty ety = true ->
      Symbol.look (ro ce) (getVarName v) = None ->
      wt_exp ce us (AssignExp v e) Types.UNIT us''
  | wt_ifthenelseexp : forall p t e tty ety us' us'' us''',
      wt_exp ce us p Types.INT us' ->
      wt_exp ce us' t tty us'' ->
      wt_exp ce us'' e ety us''' ->
      Types.ty_compat tty ety = true ->
      wt_exp ce us (IfExp p t (Some e)) tty us'''
  | wt_ifthenexp : forall p t us' us'',
      wt_exp ce us p Types.INT us' ->
      wt_exp ce us' t Types.UNIT us'' ->
      wt_exp ce us (IfExp p t None) Types.UNIT us''
  | wt_whileexp : forall g b us' us'',
      wt_exp ce us g Types.INT us' ->
      wt_exp (incr_ll ce) us' b Types.UNIT us'' ->
      wt_exp ce us (WhileExp g b) Types.UNIT us''
  | wt_forexp : forall v lo hi b us' us'' us''' ve' ro',
      wt_exp ce us lo Types.INT us' ->
      wt_exp ce us' hi Types.INT us'' ->
      Symbol.enter (ve ce) (vd_name v) (Env.VarEntry Types.INT) = ve' ->
      Symbol.enter (ro ce) (vd_name v) tt = ro' ->
      wt_exp (incr_ll (update_ve (update_ro ce ro') ve')) us'' b Types.UNIT us''' ->
      wt_exp ce us (ForExp v lo hi b) Types.UNIT us'''
  | wt_breakexp :
      0 < ll ce ->
      wt_exp ce us BreakExp Types.UNIT us
  | wt_letexp : forall decs e ty ce' us' us'',
      wt_declist ce us decs ce' us' ->
      wt_exp ce' us' e ty us'' ->
      wt_exp ce us (LetExp decs e) ty us''
  | wt_arrexp : forall aty ty ty' sz init initty u us' us'',
      Symbol.look (te ce) aty = Some ty ->
      Types.actual_ty ty = Some (Types.ARRAY ty' u) ->
      wt_exp ce us sz Types.INT us' ->
      wt_exp ce us' init initty us'' ->
      Types.ty_compat ty' initty = true ->
      wt_exp ce us (ArrayExp aty sz init) (Types.ARRAY ty' u) us''
with wt_explist (ce : composite_env) (us : Types.upool) : Absyn.explist -> list Types.ty -> Types.upool -> Prop :=
  | wt_enil :
      wt_explist ce us ENil nil us
  | wt_econs : forall e ty es tys us' us'',
      wt_exp ce us e ty us' ->
      wt_explist ce us' es tys us'' ->
      wt_explist ce us (ECons e es) (ty :: tys) us''
with wt_var (ce : composite_env) (us : Types.upool) : Absyn.var -> Types.ty -> Types.upool -> Prop :=
  | wt_svar : forall n ty ty',
      Symbol.look (ve ce) n = Some (Env.VarEntry ty) ->
      Types.actual_ty ty = Some ty' ->
      wt_var ce us (SimpleVar n) ty' us
  | wt_fvar : forall v f fs u ty ty' us',
      wt_var ce us v (Types.RECORD fs u) us' ->
      rf_in (Types.mk_rfield f ty) fs = true ->
      Types.actual_ty ty = Some ty' ->
      wt_var ce us (FieldVar v f) ty' us'
  | wt_ssvar : forall v idx u ty ty' us' us'',
      wt_exp ce us idx Types.INT us' ->
      wt_var ce us' v (Types.ARRAY ty u) us'' ->
      Types.actual_ty ty = Some ty' ->
      wt_var ce us (SubscriptVar v idx) ty' us''
with wt_dec (ce : composite_env) (us : Types.upool) : Absyn.dec -> composite_env -> Types.upool -> Prop :=
  | wt_fundec : forall fs, (* tmp *)
      wt_dec ce us (FunctionDec fs) ce us
  | wt_vardec_noty : forall v e ety ve' us',
      wt_exp ce us e ety us' ->
      ety <> Types.NIL ->
      Symbol.enter (ve ce) (vd_name v) (Env.VarEntry ety) = ve' ->
      wt_dec ce us (VarDec v None e) (update_ve ce ve') us'
  | wt_vardec_ty : forall v e tyname ty ty' ety ve' us',
      Symbol.look (te ce) tyname = Some ty ->
      Types.actual_ty ty = Some ty' ->
      wt_exp ce us e ety us' ->
      Types.ty_compat ety ty' = true ->
      Symbol.enter (ve ce) (vd_name v) (Env.VarEntry ety) = ve' ->
      wt_dec ce us (VarDec v (Some tyname) e) (update_ve ce ve') us'
  | wt_tydec : forall tys us', (* tmp *)
      wt_dec ce us (TypeDec tys) ce us'
with wt_declist (ce : composite_env) (us : Types.upool) : declist -> composite_env -> Types.upool -> Prop :=
  | wt_dnil :
      wt_declist ce us DNil ce us
  | wt_dcons : forall d ds ce' ce'' us' us'',
      wt_dec ce us d ce' us' ->
      wt_declist ce' us' ds ce'' us'' ->
      wt_declist ce us (DCons d ds) ce'' us''.

Inductive wt_prog : Absyn.exp -> Types.ty -> Types.upool -> Set :=
  | wt_prog_exp : forall p ty us',
      wt_exp base_cenv Types.uinit p ty us' ->
      wt_prog p ty us'.

Lemma transOp_sound : forall l r f ety,
  transOp l r f = OK ety ->
  wt_op (ty l) (ty r) f (ty ety).
Proof.
  destruct f; intros; unfold transOp in H; simpl in H;
  destruct (Types.ty_compat (ty l) (ty r)) eqn:?; try discriminate;
  destruct (ty l); inversion H;
  destruct (ty r); try discriminate;
  try constructor;
  unfold Types.ty_compat in Heqb; destruct Types.ty_dec; try discriminate; inversion e; constructor.
Qed.

Lemma transFields_sound : forall te us fs tys,
  transFields te us fs = OK tys ->
  wt_fields te us fs tys.
Proof.
  induction fs; intros; monadInv H; constructor; auto using lift_option.
Qed.

Lemma transTy_sound : forall te us abty ty us',
  transTy te us abty = OK (ty, us') ->
  wt_ty te us abty ty us'.
Proof.
  destruct abty; intros; monadInv H; constructor; auto using lift_option, transFields_sound.
Qed.

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
  wt_declist ce us ds ce' us'.
Proof.
  - destruct e; intros;
    try solve [monadInv H; econstructor; eauto using lift_option, transOp_sound].
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
    + destruct o; monadInv H.
      * econstructor; eauto.
        apply transExp_sound in EQ; destruct (ty x); try discriminate; eassumption.
      * econstructor.
        apply transExp_sound in EQ; destruct (ty x); try discriminate; eassumption.
        apply transExp_sound in EQ1; destruct (ty x1); try discriminate; eassumption.
    + monadInv H; econstructor. (* Should make a tactic or lemma for this pattern *)
      apply transExp_sound in EQ; destruct (ty x); try discriminate; eassumption.
      apply transExp_sound in EQ1; destruct (ty x1); try discriminate; eassumption.
    + monadInv H; econstructor; eauto.
      apply transExp_sound in EQ; destruct (ty x); try discriminate; eassumption.
      apply transExp_sound in EQ1; destruct (ty x1); try discriminate; eassumption.
      apply transExp_sound in EQ4; destruct (ty x3); try discriminate; eassumption.
    + monadInv H; constructor.
      unfold lt; fold (leb 1 (ll ce)) in EQ; auto using leb_complete.
    + monadInv H; econstructor; eauto using lift_option, Types.ty_compat_sym. (* should make a hint database *)
      apply transExp_sound in EQ1; destruct (ty x0); try discriminate; eassumption.
  - destruct es; intros; monadInv H; econstructor; eauto.
  - destruct v; intros.
    + monadInv H; econstructor; eauto using lift_option.
    + monadInv H; econstructor; eauto using lift_option.
      apply transVar_sound in EQ; rewrite HEQ in EQ; eassumption.
      { apply lift_option in EQ1.
        pose proof EQ1.
        apply rf_find_in in EQ1.
        apply rf_find_name in H.
        erewrite rf_eq_in. apply EQ1.
        apply sym_eq_rf_eq.
        fold (Types.rf_name x1).
        rewrite Symbol.eq_sym; apply H.
      }
    + monadInv H; econstructor; eauto using lift_option.
      apply transExp_sound in EQ; destruct (ty x); try discriminate; eassumption.
      apply transVar_sound in EQ1; rewrite HEQ in EQ1; eassumption.
  - destruct d; intros.
    + monadInv H; constructor. (* tmp *)
    + destruct o.
      * monadInv H; econstructor; eauto using lift_option.
      * monadInv H; econstructor; eauto; subst; congruence.
    + monadInv H; constructor. (* tmp *)
  - destruct ds; intros; monadInv H; econstructor; eauto.
Qed.

Theorem transProg_sound : forall p ety us',
  transProg p = OK (ety, us') ->
  wt_prog p (ty ety) us'.
Proof.
  unfold transProg; constructor; auto using transExp_sound.
Qed.

Theorem transExp_complete : forall ce us e ety us',
  wt_exp ce us e (ty ety) us' ->
  transExp ce us e = OK (ety, us')
with transExplist_complete : forall ce us es etys us',
  wt_explist ce us es (map ty etys) us' ->
  transExplist ce us es = OK (etys, us')
with transVar_complete : forall ce us v ety us',
  wt_var ce us v (ty ety) us' ->
  transVar ce us v = OK (ety, us')
with transDec_complete : forall ce us d ce' us',
  wt_dec ce us d ce' us' ->
  transDec ce us d = OK (ce', us')
with transDeclist_complete : forall ce us ds ce' us',
  wt_declist ce us ds ce' us' ->
  transDeclist ce us ds = OK (ce', us').
Proof.
Admitted.

Theorem transProg_complete : forall p ety us',
  wt_prog p (ty ety) us' ->
  transProg p = OK (ety, us').
Proof.
  intros; unfold transProg; inversion H; auto using transExp_complete.
Qed.

Lemma transExp_not_name : forall ce us e ety us' n oty,
  transExp ce us e = OK (ety, us') ->
  ty ety <> Types.NAME n oty.
Proof.
Admitted.

End TYPE_SPEC.
