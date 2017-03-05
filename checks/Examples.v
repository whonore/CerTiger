Require Import List.

Require Import Absyn.
Require Import Env.
Require Import Symbol.
Require Import Types.

Module Type EX.
  Parameter ex : Absyn.exp.
End EX.

Module AbsynListNotations.
  Notation "D[ ]" := DNil.
  Notation "D[ x ]" := (DCons x DNil).
  Notation "D[ x ; .. ; y ]" := (DCons x .. (DCons y DNil) ..).

  Notation "E[ ]" := ENil.
  Notation "E[ x ]" := (ECons x ENil).
  Notation "E[ x ; .. ; y ]" := (ECons x .. (ECons y ENil) ..).
End AbsynListNotations.

Import ListNotations.
Import AbsynListNotations.

Definition sy n := Symbol.symbol' n Symbol.sym_empty.

Module EX1 <: EX.
  (* let
       type arrtype = array of int
       var arr1 : arrtype := arrtype [10] of 0
     in
       arr1
     end *)
  Definition s_arrtype := sy 20.
  Definition s_arr1 := sy 21.

  Definition ex : exp :=
    LetExp
      D[TypeDec [mk_tydec s_arrtype (ArrayTy Env.s_int)];
        VarDec (mk_vardec s_arr1 true) (Some s_arrtype) (ArrayExp s_arrtype (IntExp 10) (IntExp 0))]
      (SeqExp
        E[VarExp (SimpleVar s_arr1)]).
End EX1.

Module EX2 <: EX.
  (* let
       type myint = int
       type arrtype = array of myint
       var arr1 : arrtype := arrtype [10] of 0
     in
       arr1
     end *)
  Definition s_arrtype := sy 20.
  Definition s_arr1 := sy 21.
  Definition s_myint := sy 22.

  Definition ex : exp :=
    LetExp
      D[TypeDec [mk_tydec s_myint (NameTy Env.s_int);
                 mk_tydec s_arrtype (ArrayTy s_myint)];
        VarDec (mk_vardec s_arr1 true) (Some s_arrtype) (ArrayExp s_arrtype (IntExp 10) (IntExp 0))]
      (SeqExp
        E[VarExp (SimpleVar s_arr1)]).
End EX2.

Module EX3 <: EX.
  (* let
       type rectype = {name : string, age : int}
       var rec1 : rectype := rectype {name="Nobody", age=1000}
     in
       rec1.name := "Somebody";
       rec1
     end *)
  Definition s_rectype := sy 20.
  Definition s_name := sy 21.
  Definition s_rec1 := sy 22.
  Definition s_age := sy 23.

  Definition ex : exp :=
    LetExp
      D[TypeDec [mk_tydec s_rectype (RecordTy [mk_tfield s_name Env.s_string;
                                               mk_tfield s_age Env.s_int])];
        VarDec (mk_vardec s_rec1 true) (Some s_rectype) (RecordExp E[StringExp "Nobody"; IntExp 1000]
                                                                   [s_name; s_age] s_rectype)]
      (SeqExp
        E[AssignExp (FieldVar (SimpleVar s_rec1) s_name) (StringExp "Someboy");
          VarExp (SimpleVar s_rec1)]).
End EX3.
