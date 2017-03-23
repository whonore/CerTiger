(*
 * Typing.v
 * Wolf Honore
 *
 * Defines typing semantics and the type checker.
 *)

Require Import Arith.
Require Import List.

Require Import Absyn.
Require Import DecEqFacts.
Require Import Env.
Require Import Errors.
Require Import Symbol.
Require Import Translate.
Require Import Types.

Definition tenv := @Symbol.table Types.ty.
Definition venv := @Symbol.table Env.enventry.

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

  Definition rf_find (s : Symbol.t) := find (fun rf => if Symbol.eq s (Types.rf_name rf) then true else false).

  Lemma rf_find_name : forall s rf rfs,
    rf_find s rfs = Some rf ->
    Types.rf_name rf = s.
  Proof.
    intros; induction rfs; inversion H.
    destruct (Symbol.eq s (Types.rf_name a)).
    - inversion H1; subst; reflexivity.
    - auto.
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

  (* These fields are only needed in the translation phase so they can be ignored
     during typechecking. *)
  Definition dummyAcc : Env.access := (Translate.outermost, 0).
  Definition dummyLvl : Env.level := Translate.outermost.
  Definition dummyLbl : Env.label := 0.

  Definition mkVentry vty rw := Env.VarEntry vty rw dummyAcc.
  Definition mkFentry fty rty := Env.FunEntry fty rty dummyLvl dummyLbl.

End HELPERS.

Section TYPE_CHECK.

  Let syms_eq := list_eq_dec Symbol.eq.
  Let syms_nodup := nodup Symbol.eq.

  (* The type* functions attempt to assign a type to Tiger expressions, but they
     may fail. *)

  Definition typeOp (lty rty : Types.ty) (f : opType) : @res Types.ty :=
    if Types.ty_compat lty rty
      then match f with
      | Arith => match lty with
          | Types.INT => OK Types.INT
          | _ => ERR
          end
      | Ineq => match lty with
          | Types.INT => OK Types.INT
          | Types.STRING => OK Types.INT
          | _ => ERR
          end
      | Eq => match lty with
          | Types.INT => OK Types.INT
          | Types.STRING => OK Types.INT
          | Types.RECORD _ _ => OK Types.INT
          | Types.ARRAY _ _ => OK Types.INT
          | Types.NIL => match rty with
              | Types.RECORD _ _ => OK Types.INT
              | _ => ERR
              end
          | _ => ERR
        end
      end
      else ERR.

  Fixpoint typeFields (te : tenv) (us : Types.upool) (fs : list Symbol.t) : @res (list Types.ty) :=
    match fs with
    | nil => OK nil
    | f :: fs' => do fty <- lift (Symbol.look te f);
                  do ftys <- typeFields te us fs';
                  OK (fty :: ftys)
    end.

  Definition typeTy (te : tenv) (us : Types.upool) (aty : Absyn.ty) : @res (Types.ty * Types.upool) :=
    match aty with
    | NameTy name => do ty <- lift (Symbol.look te name);
                     OK (ty, us)
    | RecordTy fields => do ftys <- typeFields te us (map tf_typ fields);
                         check syms_nodup (map tf_name fields);
                         let (us', u) := Types.unew us in
                         OK (Types.RECORD (make_rfs (map tf_name fields) ftys) u, us')
    | ArrayTy name => do ty <- lift (Symbol.look te name);
                      let (us', u) := Types.unew us in
                      OK (Types.ARRAY ty u, us')
    end.

  Fixpoint typeTydecHeads (te : tenv) (decs : list Absyn.tydec) : @res tenv :=
    match decs with
    | nil => OK te
    | dec :: decs' => let te' := Symbol.enter te (td_name dec) (Types.NAME (td_name dec)) in
                      typeTydecHeads te' decs'
    end.

  Fixpoint typeTydecs (te : tenv) (us : Types.upool) (decs : list Absyn.tydec) : @res (tenv * Types.upool) :=
    match decs with
    | nil => OK (te, us)
    | dec :: decs' => do (dty, us') <- typeTy te us (td_ty dec);
                      let te' := Symbol.enter te (td_name dec) dty in
                      typeTydecs te' us' decs'
    end.

  Fixpoint typeFormalsHeads (te : tenv) (fs : list Absyn.formals) : @res (list Types.ty) :=
    match fs with
    | nil => OK nil
    | f :: fs' => do fty <- lift (Symbol.look te (frm_typ f));
                  do ftys <- typeFormalsHeads te fs';
                  OK (fty :: ftys)
    end.

  Fixpoint typeFormals (ve : venv) (fs : list Absyn.formals) (ftys : list Types.ty) : @res venv :=
    match fs, ftys with
    | nil, nil => OK ve
    | f :: fs', fty :: ftys' => let ve' := Symbol.enter ve (vd_name (frm_var f)) (mkVentry fty Env.RW) in
                                typeFormals ve' fs' ftys'
    | _, _ => ERR
    end.

  Fixpoint typeFundecHeads (ce : composite_env) (fds : list Absyn.fundec) : @res composite_env :=
    match fds with
    | nil => OK ce
    | fd :: fds' => check syms_nodup (map (fun p => vd_name (frm_var p)) (fd_params fd));
                    do formtys <- typeFormalsHeads (te ce) (fd_params fd);
                    do rty' <- match fd_result fd with
                               | None => OK Types.UNIT
                               | Some rty => lift (Symbol.look (te ce) rty)
                               end;
                    let ve' := Symbol.enter (ve ce) (fd_name fd) (mkFentry formtys rty') in
                    typeFundecHeads (update_ve ce ve') fds'
    end.

  Fixpoint typeExp (ce : composite_env) (us : Types.upool) (exp : Absyn.exp) : @res (Types.ty * Types.upool) :=
    match exp with
    | VarExp v => typeVar ce us v
    | NilExp => OK (Types.NIL, us)
    | IntExp _ => OK (Types.INT, us)
    | StringExp _ => OK (Types.STRING, us)
    | AppExp f args => do entry <- lift (Symbol.look (ve ce) f);
                       match entry with
                       | Env.FunEntry formtys retty _ _ =>
                           do (argtys, us') <- typeExplist ce us args;
                           do formtys' <- lift (Types.actual_tys (te ce) formtys);
                           do argtys' <- lift (Types.actual_tys (te ce) argtys);
                           check Types.tys_compat argtys' formtys';
                           OK (retty, us')
                       | _ => ERR
                       end
    | OpExp l f r => do (lty, us') <- typeExp ce us l;
                     do (rty, us'') <- typeExp ce us' r;
                     do lty' <- lift (Types.actual_ty (te ce) lty);
                     do rty' <- lift (Types.actual_ty (te ce) rty);
                     do ty <- typeOp lty' rty' (getOpType f);
                     OK (ty, us'')
    | RecordExp fvals fnames rty => do recty <- lift (Symbol.look (te ce) rty);
                                    do recty' <- lift (Types.actual_ty (te ce) recty);
                                    match recty' with
                                    | Types.RECORD fields _ =>
                                        check syms_eq fnames (map Types.rf_name fields);
                                        do (etys, us') <- typeExplist ce us fvals;
                                        do etys' <- lift (Types.actual_tys (te ce) etys);
                                        do fieldtys <- lift (Types.actual_tys (te ce) (map Types.rf_type fields));
                                        check Types.tys_compat etys' fieldtys;
                                        OK (recty', us')
                                    | _ => ERR
                                    end
    | SeqExp es => do (etys, us') <- typeExplist ce us es;
                   OK (last etys (Types.UNIT), us')
    | AssignExp l r => do (vty, us') <- typeVar ce us l;
                       do (ety, us'') <- typeExp ce us' r;
                       do vty' <- lift (Types.actual_ty (te ce) vty);
                       do ety' <- lift (Types.actual_ty (te ce) ety);
                       check Types.ty_compat vty' ety';
                       match Symbol.look (ve ce) (getVarName l) with
                       | Some (Env.VarEntry _ Env.RW _) => OK (Types.UNIT, us'')
                       | _ => ERR
                       end
    | IfExp p t (Some e) => do (pty, us') <- typeExp ce us p;
                            do (tty, us'') <- typeExp ce us' t;
                            do (ety, us''') <- typeExp ce us'' e;
                            do pty' <- lift (Types.actual_ty (te ce) pty);
                            do tty' <- lift (Types.actual_ty (te ce) tty);
                            do ety' <- lift (Types.actual_ty (te ce) ety);
                            check Types.ty_compat pty' Types.INT;
                            check Types.ty_compat tty' ety';
                            OK (Types.most_general tty' ety', us''')
    | IfExp p t None => do (pty, us') <- typeExp ce us p;
                        do (tty, us'') <- typeExp ce us' t;
                        do pty' <- lift (Types.actual_ty (te ce) pty);
                        do tty' <- lift (Types.actual_ty (te ce) tty);
                        check Types.ty_compat pty' Types.INT;
                        check Types.ty_compat tty' Types.UNIT;
                        OK (Types.UNIT, us'')
    | WhileExp g b => do (gty, us') <- typeExp ce us g;
                      do (bty, us'') <- typeExp (incr_ll ce) us' b;
                      do gty' <- lift (Types.actual_ty (te ce) gty);
                      do bty' <- lift (Types.actual_ty (te ce) bty);
                      check Types.ty_compat gty' Types.INT;
                      check Types.ty_compat bty' Types.UNIT;
                      OK (Types.UNIT, us'')
    | ForExp v lo hi b => do (loty, us') <- typeExp ce us lo;
                          do (hity, us'') <- typeExp ce us' hi;
                          do loty' <- lift (Types.actual_ty (te ce) loty);
                          do hity' <- lift (Types.actual_ty (te ce) hity);
                          check Types.ty_compat loty' Types.INT;
                          check Types.ty_compat hity' Types.INT;
                          let ve' := Symbol.enter (ve ce) (vd_name v) (mkVentry Types.INT Env.RO) in
                          do (bty, us''') <- typeExp (incr_ll (update_ve ce ve')) us'' b;
                          do bty' <- lift (Types.actual_ty (te ce) bty);
                          check Types.ty_compat bty' Types.UNIT;
                          OK (Types.UNIT, us''')
    | BreakExp => check leb 1 (ll ce);
                  OK (Types.UNIT, us)
    | LetExp decs b => do (ce', us') <- typeDeclist ce us decs;
                       do (bty, us'') <- typeExp ce' us' b;
                       OK (bty, us'')
    | ArrayExp aty sz init => do arrty <- lift (Symbol.look (te ce) aty);
                              do arrty' <- lift (Types.actual_ty (te ce) arrty);
                              do (szty, us') <- typeExp ce us sz;
                              do (initty, us'') <- typeExp ce us' init;
                              do szty' <- lift (Types.actual_ty (te ce) szty);
                              do initty' <- lift (Types.actual_ty (te ce) initty);
                              check Types.ty_compat szty' Types.INT;
                              match arrty' with
                              | Types.ARRAY elty _ => do elty' <- lift (Types.actual_ty (te ce) elty);
                                                      check Types.ty_compat initty' elty';
                                                      OK (arrty', us'')
                              | _ => ERR
                              end
    end
  with typeExplist (ce : composite_env) (us : Types.upool) (exps : Absyn.explist) :  @res (list Types.ty * Types.upool) :=
    match exps with
    | ENil => OK (nil, us)
    | ECons e es => do (ety, us') <- typeExp ce us e;
                    do (etys, us'') <- typeExplist ce us' es;
                    OK (ety :: etys, us'')
    end
  with typeVar (ce : composite_env) (us : Types.upool) (var : Absyn.var) : @res (Types.ty * Types.upool) :=
    match var with
    | SimpleVar name => do entry <- lift (Symbol.look (ve ce) name);
                        match entry with
                        | Env.VarEntry ty _ _ => do ty' <- lift (Types.actual_ty (te ce) ty);
                                               OK (ty', us)
                        | _ => ERR
                        end
    | FieldVar v field => do (vty, us') <- typeVar ce us v;
                          do vty' <- lift (Types.actual_ty (te ce) vty);
                          match vty' with
                          | Types.RECORD ftys _ =>
                              do field' <- lift (rf_find field ftys);
                              do fieldty <- lift (Types.actual_ty (te ce) (Types.rf_type field'));
                              OK (fieldty, us')
                          | _ => ERR
                          end
    | SubscriptVar v idx => do (idxty, us') <- typeExp ce us idx;
                            do (vty, us'') <- typeVar ce us' v;
                            do idxty' <- lift (Types.actual_ty (te ce) idxty);
                            do vty' <- lift (Types.actual_ty (te ce) vty);
                            check Types.ty_compat idxty' Types.INT;
                            match vty' with
                            | Types.ARRAY elty _ => do elty' <- lift (Types.actual_ty (te ce) elty);
                                                    OK (elty', us'')
                            | _ => ERR
                            end
    end
  with typeDec (ce : composite_env) (us : Types.upool) (dec : Absyn.dec) : @res (composite_env * Types.upool) :=
    match dec with
    | FunctionDec decs bodies => check syms_nodup (map fd_name decs);
                                 do ce' <- typeFundecHeads ce decs;
                                 do us' <- typeFundecs ce' us decs bodies;
                                 OK (ce', us')
    | VarDec v None val => do (valty, us') <- typeExp ce us val;
                           do valty' <- lift (Types.actual_ty (te ce) valty);
                           match valty' with
                           | Types.NIL => ERR
                           | _ => let ve' := Symbol.enter (ve ce) (vd_name v) (mkVentry valty Env.RW) in
                                  OK (update_ve ce ve', us')
                           end
    | VarDec v (Some tyname) val => do (valty, us') <- typeExp ce us val;
                                    do vty <- lift (Symbol.look (te ce) tyname);
                                    do vty' <- lift (Types.actual_ty (te ce) vty);
                                    do valty' <- lift (Types.actual_ty (te ce) valty);
                                    check Types.ty_compat valty' vty';
                                    let ve' := Symbol.enter (ve ce) (vd_name v) (mkVentry vty Env.RW) in
                                    OK (update_ve ce ve', us')
    | TypeDec decs => check syms_nodup (map td_name decs);
                      do te' <- typeTydecHeads (te ce) decs;
                      do (te'', us') <- typeTydecs te' us decs;
                      check no_cycles te'' (map td_name decs);
                      OK (update_te ce te'', us')
    end
  with typeDeclist (ce : composite_env) (us : Types.upool) (decs : declist) : @res (composite_env * Types.upool) :=
    match decs with
    | DNil => OK (ce, us)
    | DCons d ds => do (ce', us') <- typeDec ce us d;
                    do (ce'', us'') <- typeDeclist ce' us' ds;
                    OK (ce'', us'')
    end
  with typeFundecs (ce : composite_env) (us : Types.upool) (fds : list Absyn.fundec) (bs : Absyn.explist) : @res Types.upool :=
    match fds, bs with
    | nil, ENil => OK us
    | fd :: fds', ECons b bs' => do entry <- lift (Symbol.look (ve ce) (fd_name fd));
                                 match entry with
                                 | Env.FunEntry formtys rty _ _ =>
                                     do ve' <- typeFormals (ve ce) (fd_params fd) formtys;
                                     do (bty, us') <- typeExp (reset_ll (update_ve ce ve')) us b;
                                     do rty' <- lift (Types.actual_ty (te ce) rty);
                                     do bty' <- lift (Types.actual_ty (te ce) bty);
                                     check Types.ty_compat rty' bty';
                                     typeFundecs ce us' fds' bs'
                                 | _ => ERR
                                 end
    | _, _ => ERR
    end.

  Definition typeProg (tree : Absyn.exp) := typeExp base_cenv Types.uinit tree.

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
        NoDup (map tf_name fs) ->
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
    | wt_form_cons : forall f fs ty tys ve' ve'' acc,
        Symbol.enter ve (vd_name (frm_var f)) (Env.VarEntry ty Env.RW acc) = ve' ->
        wt_formals ve' fs tys ve'' ->
        wt_formals ve (f :: fs) (ty :: tys) ve''.

  Inductive wt_fundec_heads (ce : composite_env) : list Absyn.fundec -> composite_env -> Prop :=
    | wt_fdh_nil :
        wt_fundec_heads ce nil ce
    | wt_fdh_noty : forall name params fds formtys ve' ce' lvl lbl,
        NoDup (map (fun p => vd_name (frm_var p)) params) ->
        wt_formals_heads (te ce) params formtys ->
        Symbol.enter (ve ce) name (Env.FunEntry formtys Types.UNIT lvl lbl) = ve' ->
        wt_fundec_heads (update_ve ce ve') fds ce' ->
        wt_fundec_heads ce ({| fd_name := name; fd_params := params; fd_result := None|} :: fds) ce'
    | wt_fdh_cons : forall name params fds formtys rty rty' ve' ce' lvl lbl,
        NoDup (map (fun p => vd_name (frm_var p)) params) ->
        wt_formals_heads (te ce) params formtys ->
        Symbol.look (te ce) rty = Some rty' ->
        Symbol.enter (ve ce) name (Env.FunEntry formtys rty' lvl lbl) = ve' ->
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
    | wt_appexp : forall f args argtys formtys argtys' formtys' retty us' lvl lbl,
        Symbol.look (ve ce) f = Some (Env.FunEntry formtys retty lvl lbl) ->
        wt_explist ce us args argtys us' ->
        Types.actual_tys (te ce) formtys = Some formtys' ->
        Types.actual_tys (te ce) argtys = Some argtys' ->
        Types.tys_compat argtys' formtys' = true ->
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
        fnames = (map Types.rf_name fields) ->
        wt_explist ce us fvals ftys us' ->
        Types.actual_tys (te ce) (map Types.rf_type fields) = Some fieldtys ->
        Types.actual_tys (te ce) ftys = Some ftys' ->
        Types.tys_compat ftys' fieldtys = true ->
        wt_exp ce us (RecordExp fvals fnames rty) (Types.RECORD fields u) us'
    | wt_seqexp : forall es tys ty us',
        wt_explist ce us es tys us' ->
        ty = last tys Types.UNIT ->
        wt_exp ce us (SeqExp es) ty us'
    | wt_assignexp : forall v e vty ety vty' ety' us' us'' ty acc,
        wt_var ce us v vty us' ->
        wt_exp ce us' e ety us'' ->
        Types.actual_ty (te ce) vty = Some vty' ->
        Types.actual_ty (te ce) ety = Some ety' ->
        Types.ty_compat vty' ety' = true ->
        Symbol.look (ve ce) (getVarName v) = Some (Env.VarEntry ty Env.RW acc) ->
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
    | wt_forexp : forall v lo hi loty hity b bty us' us'' us''' ve' acc,
        wt_exp ce us lo loty us' ->
        wt_exp ce us' hi hity us'' ->
        Types.actual_ty (te ce) loty = Some Types.INT ->
        Types.actual_ty (te ce) hity = Some Types.INT ->
        Symbol.enter (ve ce) (vd_name v) (Env.VarEntry Types.INT Env.RO acc) = ve' ->
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
    | wt_svar : forall n ty ty' rw acc,
        Symbol.look (ve ce) n = Some (Env.VarEntry ty rw acc) ->
        Types.actual_ty (te ce) ty = Some ty' ->
        wt_var ce us (SimpleVar n) ty' us
    | wt_fvar : forall v vty f fs u ty ty' us',
        wt_var ce us v vty us' ->
        Types.actual_ty (te ce) vty = Some (Types.RECORD fs u) ->
        In (Types.mk_rfield f ty) fs ->
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
        NoDup (map fd_name fs) ->
        wt_fundec_heads ce fs ce' ->
        wt_fundecs ce' us fs bs us' ->
        wt_dec ce us (FunctionDec fs bs) ce' us'
    | wt_vardec_noty : forall v e ety ety' ve' us' acc,
        wt_exp ce us e ety us' ->
        Types.actual_ty (te ce) ety = Some ety' ->
        ety' <> Types.NIL ->
        Symbol.enter (ve ce) (vd_name v) (Env.VarEntry ety Env.RW acc) = ve' ->
        wt_dec ce us (VarDec v None e) (update_ve ce ve') us'
    | wt_vardec_ty : forall v e tyname ty ty' ety ety' ve' us' acc,
        Symbol.look (te ce) tyname = Some ty ->
        wt_exp ce us e ety us' ->
        Types.actual_ty (te ce) ty = Some ty' ->
        Types.actual_ty (te ce) ety = Some ety' ->
        Types.ty_compat ety' ty' = true ->
        Symbol.enter (ve ce) (vd_name v) (Env.VarEntry ty Env.RW acc) = ve' ->
        wt_dec ce us (VarDec v (Some tyname) e) (update_ve ce ve') us'
    | wt_tydec : forall tds te' te'' us',
        NoDup (map td_name tds) ->
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
    | wt_fd_cons : forall fd fds b bs formtys rty rty' bty bty' us' us'' ve' lvl lbl,
        Symbol.look (ve ce) (fd_name fd) = Some (Env.FunEntry formtys rty lvl lbl) ->
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

  (* Proofs that if typeProg returns success with some type, then the program
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
  Local Hint Resolve nodup_sound.

  Lemma typeOp_sound : forall l r f ty,
    typeOp l r f = OK ty ->
    wt_op l r f ty.
  Proof.
    destruct f; intros; monadInv H; try (destruct r; try discriminate); try solve [constructor].
    apply Types.ty_compat_rec in EQ; subst; constructor.
    eapply Types.ty_compat_arr in EQ; eauto; inversion EQ; constructor.
  Qed.
  Local Hint Resolve typeOp_sound.

  Lemma typeFields_sound : forall te us fs tys,
    typeFields te us fs = OK tys ->
    wt_fields te us fs tys.
  Proof.
    induction fs; intros; sound_solve H.
  Qed.
  Local Hint Resolve typeFields_sound.

  Lemma typeTy_sound : forall te us abty ty us',
    typeTy te us abty = OK (ty, us') ->
    wt_ty te us abty ty us'.
  Proof.
    destruct abty; intros; sound_solve H.

  Qed.
  Local Hint Resolve typeTy_sound.

  Lemma typeTydecHeads_sound : forall te tds te',
    typeTydecHeads te tds = OK te' ->
    wt_tydec_heads te tds te'.
  Proof.
    intros; generalize dependent te0; induction tds; intros; [sound_solve H | econstructor; eauto].
  Qed.
  Local Hint Resolve typeTydecHeads_sound.

  Lemma typeTydecs_sound : forall te us tds te' us',
    typeTydecs te us tds = OK (te', us') ->
    wt_tydecs te us tds te' us'.
  Proof.
    intros; generalize dependent te0; generalize dependent us; induction tds; intros; sound_solve H.
  Qed.
  Local Hint Resolve typeTydecs_sound.

  Lemma typeFormalsHeads_sound : forall te fs tys,
    typeFormalsHeads te fs = OK tys ->
    wt_formals_heads te fs tys.
  Proof.
    induction fs; intros; sound_solve H.
  Qed.
  Local Hint Resolve typeFormalsHeads_sound.

  Lemma typeFormals_sound : forall ve fs ftys ve',
    typeFormals ve fs ftys = OK ve' ->
    wt_formals ve fs ftys ve'.
  Proof.
    intros; generalize dependent ftys; generalize dependent ve0; induction fs; intros; sound_solve H.
  Qed.
  Local Hint Resolve typeFormals_sound.

  Lemma typeFundecHeads_sound : forall ce fds ce',
    typeFundecHeads ce fds = OK ce' ->
    wt_fundec_heads ce fds ce'.
  Proof.
    intros; generalize dependent ce; induction fds; intros; try (destruct a; destruct fd_result); sound_solve H.
  Qed.
  Local Hint Resolve typeFundecHeads_sound.

  Theorem typeExp_sound : forall ce us e ty us',
    typeExp ce us e = OK (ty, us') ->
    wt_exp ce us e ty us'
  with typeExplist_sound : forall ce us es tys us',
    typeExplist ce us es = OK (tys, us') ->
    wt_explist ce us es tys us'
  with typeVar_sound : forall ce us v ty us',
    typeVar ce us v = OK (ty, us') ->
    wt_var ce us v ty us'
  with typeDec_sound : forall ce us d ce' us',
    typeDec ce us d = OK (ce', us') ->
    wt_dec ce us d ce' us'
  with typeDeclist_sound : forall ce us ds ce' us',
    typeDeclist ce us ds = OK (ce', us') ->
    wt_declist ce us ds ce' us'
  with typeFundecs_sound : forall ce us fds bs us',
    typeFundecs ce us fds bs = OK us' ->
    wt_fundecs ce us fds bs us'.
  Proof.
    - destruct e; intros; try solve [sound_solve H].
      + simpl in H; constructor; auto.
      + monadInv H; constructor.
        unfold lt; fold (leb 1 (ll ce)) in EQ; auto using leb_complete.
    - destruct es; intros; sound_solve H.
    - destruct v; intros;
      try solve [sound_solve H].
      + monadInv H; econstructor; eauto.
        apply lift_option in EQ0.
        pose proof EQ0.
        unfold rf_find in H.
        apply find_In in H.
        apply rf_find_name in EQ0.
        subst; destruct x2; simpl; assumption.
    - destruct d; intros.
      + sound_solve H.
      + destruct o; monadInv H; econstructor; eauto; reflexivity || congruence.
      + sound_solve H.
    - destruct ds; intros; sound_solve H.
    - destruct bs; intros; sound_solve H.
  Qed.

  Local Hint Resolve typeExp_sound.

  Theorem typeProg_sound : forall p ty us',
    typeProg p = OK (ty, us') ->
    wt_prog p ty us'.
  Proof.
    unfold typeProg; constructor; auto.
  Qed.

End SOUNDNESS.
