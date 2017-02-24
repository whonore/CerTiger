Require Import List.

Require Import Absyn.
Require Import Env.
Require Import Errors.
Require Import Symbol.
Require Import Types.

Definition tenv := @Symbol.table Types.ty.
Definition venv := @Symbol.table Env.enventry.

Module Translate.
  Definition exp := unit.
End Translate.

Record expty := {
  exp : Translate.exp;
  ty : Types.ty
}.

Record composite_env := {
  te : tenv;
  ve : venv
}.

Definition mk_expty ty := {| exp := tt; ty := ty |}.
Definition tmp : @res (expty * Types.upool) := ERR.

Fixpoint tys_compat (ts1 ts2 : list Types.ty) : bool :=
  match ts1, ts2 with
  | nil, nil => true
  | t1 :: ts1', t2 :: ts2' => andb (Types.ty_compat t1 t2) (tys_compat ts1' ts2')
  | _, _ => false
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

Fixpoint transTy (te : tenv) (us : Types.upool) (tree : Absyn.ty) : @res (Types.ty * Types.upool) :=
  match tree with
  | NameTy name => OK (Types.NIL, us) (* tmp *)
  | RecordTy fields => OK (Types.NIL, us) (* tmp *)
  | ArrayTy name => OK (Types.NIL, us) (* tmp *)
  end.

Fixpoint transExp (ce : composite_env) (us : Types.upool) (tree : Absyn.exp) : @res (expty * Types.upool) :=
  match tree with
  | VarExp v => transVar ce us v
  | NilExp => OK (mk_expty Types.NIL, us)
  | IntExp _ => OK (mk_expty Types.INT, us)
  | StringExp _ => OK (mk_expty Types.STRING, us)
  | AppExp f args => do entry <- lift (Symbol.look (ve ce) f);
                     do argtys <- sequence (map (transExp ce us) args);
                     match entry with
                     | Env.FunEntry formtys retty =>
                         check tys_compat (map (fun a => ty (fst a)) argtys) formtys;
                         OK (mk_expty retty, us)
                     | _ => ERR
                     end
  | OpExp l f r => do (lty, us') <- transExp ce us l; 
                   do (rty, us'') <- transExp ce us' r;
                   do ty <- transOp lty rty (getOpType f);
                   OK (ty, us'')
  | RecordExp fields rty => do recty <- lift (Symbol.look (te ce) rty);
                            tmp (* tmp *)
  | SeqExp es => do etys <- sequence (map (transExp ce us) es); (* tmp *)
                 (* OK (last etys {| exp := tt; ty := Types.UNIT |}) *)
                 tmp
  | AssignExp l r => tmp (* tmp *)
  | IfExp p t (Some e) => do (pty, us') <- transExp ce us p;
                          do (tty, us'') <- transExp ce us' t;
                          do (ety, us''') <- transExp ce us'' e;
                          (* check Types.ty_compat (ty pty) Types.INT *) (* should be caught in proof *)
                          check Types.ty_compat (ty tty) (ty ety);
                          OK (mk_expty (ty tty), us''')
  | IfExp p t None => do (pty, us') <- transExp ce us p;
                      do (tty, us'') <- transExp ce us' t;
                      (* check Types.ty_compat (ty pty) Types.INT *)
                      check Types.ty_compat (ty tty) Types.UNIT;
                      OK (mk_expty Types.UNIT, us'')
  | WhileExp g b => do (gty, us') <- transExp ce us g;
                    do (bty, us'') <- transExp ce us' b;
                    check Types.ty_compat (ty gty) Types.INT;
                    check Types.ty_compat (ty bty) Types.UNIT;
                    OK (mk_expty Types.UNIT, us'')
  | ForExp _ lo hi b => do (loty, us') <- transExp ce us lo;
                        do (hity, us'') <- transExp ce us' hi;
                        do (bty, us''') <- transExp ce us'' b;
                        check Types.ty_compat (ty loty) Types.INT;
                        check Types.ty_compat (ty hity) Types.INT;
                        check Types.ty_compat (ty bty) Types.UNIT;
                        OK (mk_expty Types.UNIT, us''')
  | BreakExp => OK (mk_expty Types.UNIT, us)
  | LetExp decs b => tmp (* tmp *)
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
with transVar (ce : composite_env) (us : Types.upool) (tree : Absyn.var) : @res (expty * Types.upool) :=
  match tree with
  | SimpleVar name => do entry <- lift (Symbol.look (ve ce) name);
                      match entry with
                      | Env.VarEntry ty => do ty' <- lift (Types.actual_ty ty);
                                           OK (mk_expty ty', us)
                      | _ => ERR
                      end
  | FieldVar v field => do (vty, us') <- transVar ce us v;
                        match ty vty with
                        | Types.RECORD ftys _ =>
                            do field' <- lift (find (fun f => Symbol.sym_eq (fst f) field) ftys);
                            OK (mk_expty (snd field'), us')
                        | _ => ERR
                        end
  | SubscriptVar v idx => do (vty, us') <- transVar ce us v;
                          do (idxty, us'') <- transExp ce us' idx;
                          check Types.ty_compat (ty idxty) Types.INT;
                          match ty vty with
                          | Types.ARRAY elty _ => OK (mk_expty elty, us'')
                          | _ => ERR
                          end
  end
with transDec (ce : composite_env) (us : Types.upool) (tree : Absyn.dec) : @res (composite_env * Types.upool) :=
  match tree with
  | FunctionDec decs => OK (ce, us) (* tmp *)
  | VarDec v ty val => OK (ce, us) (* tmp *)
  | TypeDec decs => OK (ce, us) (* tmp *)
  end.

Definition base_cenv : composite_env := {| ve := Env.base_venv; te := Env.base_tenv |}.
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

Inductive wt_ty (te : tenv) (us : Types.upool) : Absyn.ty -> Types.ty -> Types.upool -> Prop :=
  | wt_namety : forall n ty,
      Symbol.look te n = Some ty ->
      wt_ty te us (NameTy n) ty us
  | wt_recty : forall fs ftys u us',
      NoDup fs ->
      wt_fs te us (map tf_typ fs) ftys ->
      (us', u) = Types.unew us ->
      wt_ty te us (RecordTy fs) (Types.RECORD (combine (map tf_typ fs) ftys) u) us'
  | wt_arrty : forall n ty u us',
      Symbol.look te n = Some ty ->
      (us', u) = Types.unew us ->
      wt_ty te us (ArrayTy n) (Types.ARRAY ty u) us'
with wt_fs (te : tenv) (us : Types.upool) : list Symbol.t -> list Types.ty -> Prop :=
  | wt_fnil :
      wt_fs te us nil nil
  | wt_fcons : forall f fs fty ftys,
      Symbol.look te f = Some fty ->
      wt_fs te us fs ftys ->
      wt_fs te us (f :: fs) (fty :: ftys).

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
  | wt_appexp : forall f args formtys retty us',
      Symbol.look (ve ce) f = Some (Env.FunEntry formtys retty) ->
      wt_explist ce us args formtys us' ->
      wt_exp ce us (AppExp f args) retty us'
  | wt_oppexp : forall f l r fty lty rty us' us'',
      wt_exp ce us l lty us' ->
      wt_exp ce us' r rty us'' ->
      wt_op lty rty (getOpType f) fty ->
      wt_exp ce us (OpExp l f r) fty us''
  | wt_recexp : (* tmp *)
      wt_exp ce us NilExp Types.NIL us
  | wt_seqexp : forall es tys us',
      wt_explist ce us es tys us' ->
      wt_exp ce us (SeqExp es) (last tys Types.UNIT) us'
  | wt_assignexp : forall v e vty ety us' us'' u fs,
      wt_var ce us v vty us' ->
      wt_exp ce us' e ety us'' ->
      vty = ety \/ (vty = Types.NIL \/ ety = Types.RECORD fs u) \/ (vty = Types.RECORD fs u \/ ety = Types.NIL) ->
      wt_exp ce us (AssignExp v e) Types.UNIT us''
  | wt_ifthenexp : forall p t e ty us' us'' us''',
      wt_exp ce us p Types.INT us' ->
      wt_exp ce us t ty us'' ->
      wt_exp ce us' e ty us''' ->   
      wt_exp ce us (IfExp p t (Some e)) ty us'''
  | wt_ifthen : forall p t us' us'',
      wt_exp ce us p Types.INT us' ->
      wt_exp ce us' t Types.UNIT us'' ->
      wt_exp ce us (IfExp p t None) Types.UNIT us''
  | wt_whileexp : forall g b us' us'',
      wt_exp ce us g Types.INT us' ->
      wt_exp ce us' b Types.UNIT us'' ->
      wt_exp ce us (WhileExp g b) Types.UNIT us''
  | wt_forexp : forall v lo hi b us' us'' us''', (* need to add v to ce? *)
      wt_exp ce us lo Types.INT us' ->
      wt_exp ce us' hi Types.INT us'' ->
      wt_exp ce us'' b Types.UNIT us''' ->
      wt_exp ce us (ForExp v lo hi b) Types.UNIT us'''
  | wt_breakexp :
      wt_exp ce us BreakExp Types.UNIT us (* must be in loop *)
  | wt_letexp : forall decs e ty ce' us' us'',
      wt_declist ce us decs ce' us' ->
      wt_exp ce' us' e ty us'' ->
      wt_exp ce us (LetExp decs e) ty us'
  | wt_arrexp : forall aty ty ty' sz init u us' us'',
      Symbol.look (te ce) aty = Some ty ->
      Types.actual_ty ty = Some (Types.ARRAY ty' u) ->
      wt_exp ce us sz Types.INT us' ->
      wt_exp ce us init ty' us'' ->
      wt_exp ce us (ArrayExp aty sz init) (Types.ARRAY ty' u) us''
with wt_explist (ce : composite_env) (us : Types.upool) : list Absyn.exp -> list Types.ty -> Types.upool -> Prop := 
  | wt_enil : 
      wt_explist ce us nil nil us
  | wt_econs : forall e ty es tys us' us'',
      wt_exp ce us e ty us' ->
      wt_explist ce us' es tys us'' ->
      wt_explist ce us (e :: es) (ty :: tys) us''
with wt_var (ce : composite_env) (us : Types.upool) : Absyn.var -> Types.ty -> Types.upool -> Prop :=
  | wt_svar : forall n ty ty',
      Symbol.look (ve ce) n = Some (Env.VarEntry ty) ->
      Types.actual_ty ty = Some ty' ->
      wt_var ce us (SimpleVar n) ty' us
  | wt_fvar : forall v f fs u ty ty' us',
      wt_var ce us v (Types.RECORD fs u) us' ->
      In (f, ty) fs ->
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
      wt_dec ce us (VarDec v None e) {| ve := ve'; te := (te ce) |} us'
  | wt_vardec_ty : forall v e tyname ty ty' ve' us',
      Symbol.look (te ce) tyname = Some ty ->
      Types.actual_ty ty = Some ty' ->
      wt_exp ce us e ty us' ->
      Symbol.enter (ve ce) (vd_name v) (Env.VarEntry ty) = ve' ->
      wt_dec ce us (VarDec v (Some tyname) e) {| ve := ve'; te := (te ce) |} us'
  | wt_tydec : forall tys us', (* tmp *)
      wt_dec ce us (TypeDec tys) ce us'
with wt_declist (ce : composite_env) (us : Types.upool) : list Absyn.dec -> composite_env -> Types.upool -> Prop :=
  | wt_dnil :
      wt_declist ce us nil ce us
  | wt_dcons : forall d ds ce' ce'' us' us'',
      wt_dec ce us d ce' us' ->
      wt_declist ce' us' ds ce'' us'' ->
      wt_declist ce us (d :: ds) ce'' us''.

Inductive wt_prog : Absyn.exp -> Types.ty -> Types.upool -> Set :=
  | wt_prog_exp : forall p ty us',
      wt_exp {| ve := Env.base_venv; te := Env.base_tenv |} Types.uinit p ty us' ->
      wt_prog p ty us'.

Ltac inv_texp := match goal with
  | [H : transExp _ _ _ = OK (_, _) |- _] => inversion H; subst; try solve [constructor]
  | _ => idtac
  end.

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

Lemma transNilExp_sound : forall ce us ety us',
  transExp ce us NilExp = OK (ety, us') ->
  wt_exp ce us NilExp (ty ety) us'.
Proof. intros; inv_texp. Qed.

Lemma transIntExp_sound : forall ce us n ety us',
  transExp ce us (IntExp n) = OK (ety, us') ->
  wt_exp ce us (IntExp n) (ty ety) us'.
Proof. intros; inv_texp. Qed.

Lemma transStringExp_sound : forall ce us s ety us',
  transExp ce us (StringExp s) = OK (ety, us') ->
  wt_exp ce us (StringExp s) (ty ety) us'.
Proof. intros; inv_texp. Qed.

Theorem transExp_sound : forall ce us e ety us',
  transExp ce us e = OK (ety, us') ->
  wt_exp ce us e (ty ety) us'.
Proof.
Admitted.

Theorem transProg_sound : forall p ety us',
  transProg p = OK (ety, us') ->
  wt_exp {| ve := Env.base_venv; te := Env.base_tenv |} Types.uinit p (ty ety) us'.
Proof.
  unfold transProg; eapply transExp_sound; eassumption.
Qed.

End TYPE_SPEC.