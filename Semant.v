Require Import List.

Require Import Absyn.
Require Import Env.
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

Definition mk_expty ty := Some {| exp := tt; ty := ty |}.
Definition tmp : option expty := None.

Section MONAD.

(* Copied from CompCert Error monad *)
Definition bind {A B : Type} (f : option A) (g : A -> option B) : option B :=
  match f with
  | None => None
  | Some x => g x
  end.

Fixpoint sequence {A} (os : list (option A)) : option (list A) :=
  match os with
  | nil => Some nil
  | o :: os' => match o with
    | None => None
    | Some o => option_map (cons o) (sequence os')
    end
  end.

End MONAD.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'assert' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200).

Fixpoint actual_ty (t : Types.ty) : option Types.ty :=
  match t with
  | Types.NAME _ oty => bind oty actual_ty
  | _ => Some t
  end.

Fixpoint tys_eq (ts1 ts2 : list Types.ty) : bool :=
  match ts1, ts2 with
  | nil, nil => true
  | t1 :: ts1', t2 :: ts2' => andb (Types.ty_eq t1 t2) (tys_eq ts1' ts2')
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

Definition transOp lty rty f := 
  match getOpType f with
  | Arith => match (ty lty), (ty rty) with
    | Types.INT, Types.INT => mk_expty Types.INT
    | _, _ => None
    end
  | Ineq => match (ty lty), (ty rty) with
    | Types.INT, Types.INT => mk_expty Types.INT
    | Types.STRING, Types.STRING => mk_expty Types.INT
    | _, _ => None
    end
  | Eq => match (ty lty), (ty rty) with
    | Types.INT, Types.INT => mk_expty Types.INT
    | Types.STRING, Types.STRING => mk_expty Types.INT
    | Types.RECORD _ _, Types.RECORD _ _ => mk_expty Types.INT
    | Types.ARRAY _ _, Types.ARRAY _ _ => mk_expty Types.INT
    | _, _ => None
    end
  end.

Fixpoint transTy (te : tenv) (tree : Absyn.ty) : option Types.ty :=
  match tree with
  | NameTy name => Some Types.NIL (* tmp *)
  | RecordTy fields => Some Types.NIL (* tmp *)
  | ArrayTy name => Some Types.NIL (* tmp *)
  end.

Fixpoint transExp (ve : venv) (te : tenv) (us : Types.upool) (tree : Absyn.exp) : option expty :=
  match tree with
  | VarExp v => transVar ve te us v
  | NilExp => mk_expty Types.NIL
  | IntExp _ => mk_expty Types.INT
  | StringExp _ => mk_expty Types.STRING
  | AppExp f args => do entry <- Symbol.look ve f;
                     do argtys <- sequence (map (transExp ve te us) args);
                     match entry with
                     | Env.FunEntry formtys retty =>
                         assert tys_eq (map ty argtys) formtys;
                         mk_expty retty
                     | _ => None
                     end
  | OpExp l f r => do lty <- transExp ve te us l; 
                   do rty <- transExp ve te us r;
                   transOp lty rty f
  | RecordExp fields rty => do recty <- Symbol.look te rty;
                            tmp (* tmp *)
  | SeqExp es => do etys <- sequence (map (transExp ve te us) es);
                 Some (last etys {| exp := tt; ty := Types.UNIT |})
  | AssignExp l r => tmp (* tmp *)
  | IfExp p t (Some e) => do pty <- transExp ve te us p;
                          do tty <- transExp ve te us t;
                          do ety <- transExp ve te us e;
                          (* assert Types.ty_eq (ty pty) Types.INT *)
                          assert Types.ty_eq (ty tty) (ty ety);
                          mk_expty (ty tty)
  | IfExp p t None => do pty <- transExp ve te us p;
                      do tty <- transExp ve te us t;
                      (* assert Types.ty_eq (ty pty) Types.INT *)
                      assert Types.ty_eq (ty tty) (Types.UNIT);
                      mk_expty Types.UNIT
  | WhileExp g b => do gty <- transExp ve te us g;
                    do bty <- transExp ve te us b;
                    assert Types.ty_eq (ty gty) Types.INT;
                    assert Types.ty_eq (ty bty) Types.UNIT;
                    mk_expty Types.UNIT
  | ForExp _ lo hi b => do loty <- transExp ve te us lo;
                        do hity <- transExp ve te us hi;
                        do bty <- transExp ve te us b;
                        assert Types.ty_eq (ty loty) Types.INT;
                        assert Types.ty_eq (ty hity) Types.INT;
                        assert Types.ty_eq (ty bty) Types.UNIT;
                        mk_expty Types.UNIT
  | BreakExp => mk_expty Types.UNIT
  | LetExp decs b => tmp (* tmp *)
  | ArrayExp aty sz init => do arrty <- Symbol.look te aty;
                            do szty <- transExp ve te us sz;
                            do initty <- transExp ve te us init;
                            assert Types.ty_eq (ty szty) Types.INT;
                            match arrty with
                            | Types.ARRAY elty _ => assert Types.ty_eq (ty initty) elty;
                                                    mk_expty arrty
                            | _ => None
                            end
  end
with transVar (ve : venv) (te : tenv) (us : Types.upool) (tree : Absyn.var) : option expty :=
  match tree with
  | SimpleVar name => do entry <- Symbol.look ve name;
                      match entry with
                      | Env.VarEntry ty => bind (actual_ty ty) mk_expty
                      | _ => None
                      end
  | FieldVar v field => do vty <- transVar ve te us v;
                        match ty vty with
                        | Types.RECORD ftys _ =>
                            let field' := find (fun f => Symbol.sym_eq (fst f) field) ftys in
                            bind field' (fun f => mk_expty (snd f))
                        | _ => None
                        end
  | SubscriptVar v idx => do vty <- transVar ve te us v;
                          do idxty <- transExp ve te us idx;
                          assert Types.ty_eq (ty idxty) Types.INT;
                          match ty vty with
                          | Types.ARRAY elty _ => mk_expty elty
                          | _ => None
                          end
  end
with transDec (ve : venv) (te : tenv) (us : Types.upool) (tree : Absyn.dec) : option (tenv * venv) :=
  match tree with
  | FunctionDec decs => Some (te, ve) (* tmp *)
  | VarDec v ty val => Some (te, ve) (* tmp *)
  | TypeDec decs => Some (te, ve) (* tmp *)
  end.

Definition transProg (tree : Absyn.exp) := transExp Env.base_venv Env.base_tenv Types.uinit tree.

End TYPE_CHECK.

Section TYPE_SPEC.

Record combine_env := {
  te : tenv;
  ve : venv
}.

Inductive wt_op : Absyn.oper -> Types.ty -> Types.ty -> Types.ty -> Prop :=
  | wt_arith : forall f,
      getOpType f = Arith ->
      wt_op f Types.INT Types.INT Types.INT
  | wt_ineq : forall f ty,
      getOpType f = Ineq ->
      ty = Types.INT \/ ty = Types.STRING ->
      wt_op f ty ty Types.INT
  | wt_eq : forall f ty aty rty u,
      getOpType f = Eq ->
      ty = Types.INT \/ ty = Types.STRING \/ ty = Types.ARRAY aty u \/ ty = Types.RECORD rty u ->
      wt_op f ty ty Types.INT.

Inductive wt_ty (env : combine_env) (us : Types.upool) : Absyn.ty -> Types.ty -> Types.upool -> Prop :=
  | wt_namety : forall n ty,
      Symbol.look (te env) n = Some ty ->
      wt_ty env us (NameTy n) ty us
  | wt_recty : forall fs ftys u us',
      NoDup fs ->
      wt_fs env us (map tf_typ fs) ftys ->
      (us', u) = Types.unew us ->
      wt_ty env us (RecordTy fs) (Types.RECORD (combine (map tf_typ fs) ftys) u) us'
  | wt_arrty : forall n ty u us',
      Symbol.look (te env) n = Some ty ->
      (us', u) = Types.unew us ->
      wt_ty env us (ArrayTy n) (Types.ARRAY ty u) us'
with wt_fs (env : combine_env) (us : Types.upool) : list Symbol.t -> list Types.ty -> Prop :=
  | wt_fnil :
      wt_fs env us nil nil
  | wt_fcons : forall f fs fty ftys,
      Symbol.look (te env) f = Some fty ->
      wt_fs env us fs ftys ->
      wt_fs env us (f :: fs) (fty :: ftys).

Inductive wt_exp (env : combine_env) (us : Types.upool) : Absyn.exp -> Types.ty -> Types.upool -> Prop :=
  | wt_varexp : forall v ty us', 
      wt_var env us v ty us' ->
      wt_exp env us (VarExp v) ty us'
  | wt_nilexp :
      wt_exp env us NilExp Types.NIL us
  | wt_intexp : forall n,
      wt_exp env us (IntExp n) Types.INT us
  | wt_strexp : forall s,
      wt_exp env us (StringExp s) Types.STRING us
  | wt_appexp : forall f args formtys retty us',
      Symbol.look (ve env) f = Some (Env.FunEntry formtys retty) ->
      wt_explist env us args formtys us' ->
      wt_exp env us (AppExp f args) retty us'
  | wt_oppexp : forall f l r fty lty rty us' us'',
      wt_exp env us l lty us' ->
      wt_exp env us' r rty us'' ->
      wt_op f lty rty fty ->
      wt_exp env us (OpExp l f r) fty us''
  | wt_recexp : (* tmp *)
      wt_exp env us NilExp Types.NIL us
  | wt_seqexp : forall es tys us',
      wt_explist env us es tys us' ->
      wt_exp env us (SeqExp es) (last tys Types.UNIT) us'
  | wt_assignexp : forall v e vty ety us' us'' u fs,
      wt_var env us v vty us' ->
      wt_exp env us' e ety us'' ->
      vty = ety \/ (vty = Types.NIL \/ ety = Types.RECORD fs u) \/ (vty = Types.RECORD fs u \/ ety = Types.NIL) ->
      wt_exp env us (AssignExp v e) Types.UNIT us''
  | wt_ifthenexp : forall p t e ty us' us'',
      wt_exp env us p Types.INT us ->
      wt_exp env us t ty us' ->
      wt_exp env us' e ty us'' ->   
      wt_exp env us (IfExp p t (Some e)) ty us''
  | wt_ifthen : forall p t us' us'',
      wt_exp env us p Types.INT us' ->
      wt_exp env us' t Types.UNIT us'' ->
      wt_exp env us (IfExp p t None) Types.UNIT us''
  | wt_whileexp : forall g b us' us'',
      wt_exp env us g Types.INT us' ->
      wt_exp env us' b Types.UNIT us'' ->
      wt_exp env us (WhileExp g b) Types.UNIT us''
  | wt_forexp : forall v lo hi b us' us'' us''', (* need to add v to env? *)
      wt_exp env us lo Types.INT us' ->
      wt_exp env us' hi Types.INT us'' ->
      wt_exp env us'' b Types.UNIT us''' ->
      wt_exp env us (ForExp v lo hi b) Types.UNIT us'''
  | wt_breakexp :
      wt_exp env us BreakExp Types.UNIT us (* must be in loop *)
  | wt_letexp : forall decs e ty env' us' us'',
      wt_declist env us decs env' us' ->
      wt_exp env' us' e ty us'' ->
      wt_exp env us (LetExp decs e) ty us'
  | wt_arrexp : forall aty ty ty' sz init u us' us'',
      Symbol.look (te env) aty = Some ty ->
      actual_ty ty = Some (Types.ARRAY ty' u) ->
      wt_exp env us sz Types.INT us' ->
      wt_exp env us init ty' us'' ->
      wt_exp env us (ArrayExp aty sz init) (Types.ARRAY ty' u) us''
with wt_explist (env : combine_env) (us : Types.upool) : list Absyn.exp -> list Types.ty -> Types.upool -> Prop := 
  | wt_enil : 
      wt_explist env us nil nil us
  | wt_econs : forall e ty es tys us' us'',
      wt_exp env us e ty us' ->
      wt_explist env us' es tys us'' ->
      wt_explist env us (e :: es) (ty :: tys) us''
with wt_var (env : combine_env) (us : Types.upool) : Absyn.var -> Types.ty -> Types.upool -> Prop :=
  | wt_svar : forall n ty ty',
      Symbol.look (ve env) n = Some (Env.VarEntry ty) ->
      actual_ty ty = Some ty' ->
      wt_var env us (SimpleVar n) ty' us
  | wt_fvar : forall v f fs u ty ty' us',
      wt_var env us v (Types.RECORD fs u) us' ->
      In (f, ty) fs ->
      actual_ty ty = Some ty' ->
      wt_var env us (FieldVar v f) ty' us'
  | wt_ssvar : forall v idx u ty ty' us' us'',
      wt_exp env us idx Types.INT us' ->
      wt_var env us' v (Types.ARRAY ty u) us'' ->
      actual_ty ty = Some ty' ->
      wt_var env us (SubscriptVar v idx) ty' us''
with wt_dec (env : combine_env) (us : Types.upool) : Absyn.dec -> combine_env -> Types.upool -> Prop :=
  | wt_fundec : forall fs, (* tmp *)
      wt_dec env us (FunctionDec fs) env us
  | wt_vardec_noty : forall v e ety ve' us',
      wt_exp env us e ety us' ->
      ety <> Types.NIL ->
      Symbol.enter (ve env) (vd_name v) (Env.VarEntry ety) = ve' ->
      wt_dec env us (VarDec v None e) {| ve := ve'; te := (te env) |} us'
  | wt_vardec_ty : forall v e tyname ty ty' ve' us',
      Symbol.look (te env) tyname = Some ty ->
      actual_ty ty = Some ty' ->
      wt_exp env us e ty us' ->
      Symbol.enter (ve env) (vd_name v) (Env.VarEntry ty) = ve' ->
      wt_dec env us (VarDec v (Some tyname) e) {| ve := ve'; te := (te env) |} us'
  | wt_tydec : forall tys us',
      wt_dec env us (TypeDec tys) env us'
with wt_declist (env : combine_env) (us : Types.upool) : list Absyn.dec -> combine_env -> Types.upool -> Prop :=
  | wt_dnil :
      wt_declist env us nil env us
  | wt_dcons : forall d ds env' env'' us' us'',
      wt_dec env us d env' us' ->
      wt_declist env' us' ds env'' us'' ->
      wt_declist env us (d :: ds) env'' us''.

Theorem transExp_sound : forall ve te us e ety,
  transExp ve te us e = Some ety ->
  wt_exp ve te e (ty ety).
Proof.
Admitted.

Theorem transProg_sound : forall p ety,
  transProg p = Some ety ->
  wt_exp Env.base_venv Env.base_tenv p (ty ety).
Proof.
  unfold transProg; eapply transExp_sound; eassumption.
Qed.

End TYPE_SPEC.