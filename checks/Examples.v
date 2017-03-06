(* 
 * Examples.v
 * Wolf Honore
 * 
 * A set of example Tiger programs to be used in testing 
 * various parts of the compiler. Examples taken from those
 * provided by Zhong Shao in CPSC (4/5)21 (Yale).
 *)

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
      D[TypeDec [Build_tydec s_arrtype (ArrayTy Env.s_int)];
        VarDec (Build_vardec s_arr1 true) (Some s_arrtype) (ArrayExp s_arrtype (IntExp 10) (IntExp 0))]
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
      D[TypeDec [Build_tydec s_myint (NameTy Env.s_int);
                 Build_tydec s_arrtype (ArrayTy s_myint)];
        VarDec (Build_vardec s_arr1 true) (Some s_arrtype) (ArrayExp s_arrtype (IntExp 10) (IntExp 0))]
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
      D[TypeDec [Build_tydec s_rectype (RecordTy [Build_tfield s_name Env.s_string;
                                                  Build_tfield s_age Env.s_int])];
        VarDec (Build_vardec s_rec1 true) (Some s_rectype) (RecordExp E[StringExp "Nobody"; IntExp 1000]
                                                                      [s_name; s_age] s_rectype)]
      (SeqExp
        E[AssignExp (FieldVar (SimpleVar s_rec1) s_name) (StringExp "Someboy");
          VarExp (SimpleVar s_rec1)]).
End EX3.

Module EX4 <: EX.
  (* let
       function nfactor(n: int) : int =
         if  n = 0
           then 1
           else n * nfactor(n - 1)
         in
           nfactor(10)
         end *)
  Definition s_nfactor := sy 20.
  Definition s_n := sy 21.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_nfactor [Build_formals (Build_vardec s_n true) Env.s_int] (Some Env.s_int)]
                    E[IfExp (OpExp (VarExp (SimpleVar s_n)) EqOp (IntExp 0))
                            (IntExp 1)
                            (Some (OpExp (VarExp (SimpleVar s_n)) TimesOp
                                          (AppExp s_nfactor E[OpExp (VarExp (SimpleVar s_n)) MinusOp (IntExp 1)])))]]
      (SeqExp E[AppExp s_nfactor E[IntExp 10]]).
End EX4.

Module EX5 <: EX.
  (* let
       type intlist = {hd : int, tl : intlist}
       type tree = {key : int, children : treelist}
       type treelist = {hd : tree, tl : treelist}
       var lis : intlist := intlist {hd=0, tl=nil}
     in
	lis
     end *)
  Definition s_intlist := sy 20.
  Definition s_hd := sy 21.
  Definition s_tl := sy 22.
  Definition s_tree := sy 23.
  Definition s_key := sy 24.
  Definition s_children := sy 25.
  Definition s_treelist := sy 26.
  Definition s_lis := sy 27.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_intlist (RecordTy [Build_tfield s_hd Env.s_int;
                                                  Build_tfield s_tl s_intlist]);
                 Build_tydec s_tree (RecordTy [Build_tfield s_key Env.s_int;
                                               Build_tfield s_children s_treelist]);
                 Build_tydec s_treelist (RecordTy [Build_tfield s_hd s_tree;
                                                   Build_tfield s_tl s_treelist])];
        VarDec (Build_vardec s_lis true) (Some s_intlist) (RecordExp E[IntExp 0; NilExp]
                                                                     [s_hd; s_tl]
                                                                     s_intlist)]
      (SeqExp E[VarExp (SimpleVar s_lis)]).
End EX5.

Module EX6 <: EX.
  (* let
       function do_nothing1(a : int, b : string) = do_nothing2(a + 1)
       function do_nothing2(d : int) = do_nothing1(d, "str")
     in
       do_nothing1(0, "str2")
     end *)
  Definition s_do_nothing1 := sy 20.
  Definition s_a := sy 21.
  Definition s_b := sy 22.
  Definition s_do_nothing2 := sy 23.
  Definition s_d := sy 24.

  Definition ex : exp :=
  LetExp
    D[FunctionDec [Build_fundec s_do_nothing1 [Build_formals (Build_vardec s_a true) Env.s_int;
                                               Build_formals (Build_vardec s_b true) Env.s_string]
                                               None;
                   Build_fundec s_do_nothing2 [Build_formals (Build_vardec s_d true) Env.s_int]
                                               None]
                  E[AppExp s_do_nothing2 E[OpExp (VarExp (SimpleVar s_a)) PlusOp (IntExp 1)];
                                           AppExp s_do_nothing1 E[VarExp (SimpleVar s_d);
                                                                  StringExp "str"]]]
    (SeqExp E[AppExp s_do_nothing1 E[IntExp 0; StringExp "str2"]]).
End EX6.

Module EX7 <: EX.
  (* let
       function do_nothing1(a : int, b : string) : int = (do_nothing2(a + 1); 0)
       function do_nothing2(d : int) : string = (do_nothing1(d, "str"); " ")
     in
       do_nothing1(0, "str2")
     end *)
  Definition s_do_nothing1 := sy 20.
  Definition s_a := sy 21.
  Definition s_b := sy 22.
  Definition s_do_nothing2 := sy 23.
  Definition s_d := sy 24.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_do_nothing1 [Build_formals (Build_vardec s_a true) Env.s_int;
                                                 Build_formals (Build_vardec s_b true) Env.s_string]
                                  (Some Env.s_int);
                     Build_fundec s_do_nothing2 [Build_formals (Build_vardec s_d true) Env.s_int]
                                  (Some Env.s_string)]
                    E[SeqExp E[AppExp s_do_nothing2 E[OpExp (VarExp (SimpleVar s_a)) PlusOp (IntExp 1)];
                               IntExp 0];
                      SeqExp E[AppExp s_do_nothing1 E[VarExp (SimpleVar s_d); StringExp "str"];
                               StringExp " "]]]
      (SeqExp E[AppExp s_do_nothing1 E[IntExp 0; StringExp "str2"]]).
End EX7.

Module EX8 <: EX.
  (* if (10 > 20) then 30 else 40 *)

  Definition ex : exp :=
    IfExp (OpExp (IntExp 10) GtOp (IntExp 20))
          (IntExp 30)
          (Some (IntExp 40)).
End EX8.

Module EX9 <: EX.
  (* Error *)
  (* if (5>4) then 13 else  " " *)

  Definition ex : exp :=
    IfExp (OpExp (IntExp 5) GtOp (IntExp 4))
          (IntExp 13)
          (Some (StringExp " ")).
End EX9.

Module EX10 <: EX.
  (* Error *)
  (* while(10 > 5) do 5 + 6 *)

  Definition ex : exp :=
    WhileExp (OpExp (IntExp 10) GtOp (IntExp 5)) (OpExp (IntExp 5) PlusOp (IntExp 6)).
End EX10.

Module EX11 <: EX.
  (* Error *)
  (* for i := 10 to " " do i := i - 1 *)
  Definition s_i := sy 20.

  Definition ex : exp :=
    ForExp (Build_vardec s_i true) (IntExp 10) (StringExp " ")
           (AssignExp (SimpleVar s_i) (OpExp (VarExp (SimpleVar s_i)) MinusOp (IntExp 1))).
End EX11.

Module EX12 <: EX.
  (* let
       var a := 0
     in
       for i := 0 to 100 do (a := a + 1; ())
     end *)
  Definition s_a := sy 20.
  Definition s_i := sy 21.

  Definition ex : exp :=
    LetExp
      D[VarDec (Build_vardec s_a true) None (IntExp 0)]
      (SeqExp E[ForExp (Build_vardec s_i true)
                       (IntExp 0) (IntExp 100)
                       (SeqExp E[AssignExp (SimpleVar s_a)
                                           (OpExp (VarExp (SimpleVar s_a)) PlusOp (IntExp 1));
                                 SeqExp E[]])]).
End EX12.

Module EX13 <: EX.
  (* 3 > "df" *)
  Definition ex : exp :=
    OpExp (IntExp 3) GtOp (StringExp "df").
End EX13.

Module EX14 <: EX.
  (* let
       type arrtype = array of int
       type rectype = {name : string, id : int}
       var rec := rectype {name="aname", id=0}
       var arr := arrtype [3] of 0
     in
       if rec <> arr then 3 else 4
     end *)
  Definition s_arrtype := sy 20.
  Definition s_rectype := sy 21.
  Definition s_rec := sy 22.
  Definition s_name := sy 23.
  Definition s_id := sy 24.
  Definition s_arr := sy 25.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_arrtype (ArrayTy Env.s_int);
                 Build_tydec s_rectype (RecordTy [Build_tfield s_name Env.s_string;
                                                  Build_tfield s_id Env.s_int])];
        VarDec (Build_vardec s_rec true) None (RecordExp E[StringExp "aname"; IntExp 0]
                                                         [s_name; s_id]
                                                         s_rectype);
        VarDec (Build_vardec s_arr true) None (ArrayExp s_arrtype (IntExp 3) (IntExp 0))]
      (SeqExp E[IfExp (OpExp (VarExp (SimpleVar s_rec)) NeqOp (VarExp (SimpleVar s_arr)))
                      (IntExp 3)
                      (Some (IntExp 4))]).
End EX14.

Module EX15 <: EX.
  (* if 20 then 3 *)
  Definition ex : exp :=
    IfExp (IntExp 20) (IntExp 3) None.
End EX15.

Module EX16 <: EX.
  (* let
       type a = c
       type b = a
       type c = d
       type d = a
     in
       ""
     end *)
  Definition s_a := sy 20.
  Definition s_b := sy 21.
  Definition s_c := sy 22.
  Definition s_d := sy 23.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_a (NameTy s_c);
                 Build_tydec s_b (NameTy s_a);
                 Build_tydec s_c (NameTy s_d);
                 Build_tydec s_d (NameTy s_a)]]
      (SeqExp E[StringExp ""]).
End EX16.

Module EX17 <: EX.
 (* let
      type tree = {key : int, children : treelist}
      var d : int := 0
      type treelist = {hd : tree, tl : treelist}
    in
      d
    end *)
  Definition s_tree := sy 20.
  Definition s_key := sy 21.
  Definition s_children := sy 22.
  Definition s_d := sy 23.
  Definition s_treelist := sy 24.
  Definition s_hd := sy 25.
  Definition s_tl := sy 26.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_tree (RecordTy [Build_tfield s_key Env.s_int;
                                               Build_tfield s_children s_treelist])];
        VarDec (Build_vardec s_d true) (Some Env.s_int) (IntExp 0);
        TypeDec [Build_tydec s_treelist (RecordTy [Build_tfield s_hd s_tree;
                                                   Build_tfield s_tl s_treelist])]]
      (SeqExp E[VarExp (SimpleVar s_d)]).
End EX17.

Module EX18 <: EX.
  (* let
       function do_nothing1(a : int, b : string) : int = (do_nothing2(a + 1); 0)
       var d := 0
       function do_nothing2(d : int) : string = (do_nothing1(d, "str"); " ")
     in
       do_nothing1(0, "str2")
     end *)
  Definition s_do_nothing1 := sy 20.
  Definition s_a := sy 21.
  Definition s_b := sy 22.
  Definition s_do_nothing2 := sy 23.
  Definition s_d := sy 24.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_do_nothing1 [Build_formals (Build_vardec s_a true) Env.s_int;
                                                 Build_formals (Build_vardec s_b true) Env.s_string]
                                  (Some Env.s_int)]
                    E[SeqExp E[AppExp s_do_nothing2
                               E[OpExp (VarExp (SimpleVar s_a)) PlusOp (IntExp 1)];
                                 IntExp 0]];
        VarDec (Build_vardec s_d true) None (IntExp 0);
        FunctionDec [Build_fundec s_do_nothing2 [Build_formals (Build_vardec s_d true) Env.s_int]
                                  (Some Env.s_string)]
                    E[SeqExp E[AppExp s_do_nothing1 E[VarExp (SimpleVar s_d); StringExp "str"];
                               StringExp " "]]]
      (SeqExp E[AppExp s_do_nothing1 E[IntExp 0; StringExp "str2"]]).
End EX18.

Module EX19 <: EX.
  (* let
       function do_nothing1(a : int, b : string) : int = (do_nothing2(a + 1); 0)
       function do_nothing2(d : int) : string = (do_nothing1(a, "str"); " ")
     in
       do_nothing1(0, "str2")
     end *)
  Definition s_do_nothing1 := sy 20.
  Definition s_a := sy 21.
  Definition s_b := sy 22.
  Definition s_do_nothing2 := sy 23.
  Definition s_d := sy 24.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_do_nothing1 [Build_formals (Build_vardec s_a true) Env.s_int;
                                                 Build_formals (Build_vardec s_b true) Env.s_string]
                                  (Some Env.s_int);
                     Build_fundec s_do_nothing2 [Build_formals (Build_vardec s_d true) Env.s_int]
                                  (Some Env.s_string)]
                    E[SeqExp E[AppExp s_do_nothing2 E[OpExp (VarExp (SimpleVar s_a)) PlusOp (IntExp 1)];
                               IntExp 0];
                      SeqExp E[AppExp s_do_nothing1 E[VarExp (SimpleVar s_a); StringExp "str"];
                               StringExp " "]]]
      (SeqExp E[AppExp s_do_nothing1 E[IntExp 0; StringExp "str2"]]).
End EX19.
