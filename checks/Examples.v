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
         if n = 0
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
  (* if (5>4) then 13 else " " *)

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
  (* Error *)
  (* 3 > "df" *)

  Definition ex : exp :=
    OpExp (IntExp 3) GtOp (StringExp "df").
End EX13.

Module EX14 <: EX.
  (* Error *)
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
  (* Error *)
  (* if 20 then 3 *)

  Definition ex : exp :=
    IfExp (IntExp 20) (IntExp 3) None.
End EX15.

Module EX16 <: EX.
  (* Error *)
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
  (* Error *)
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
  (* Error *)
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
  (* Error *)
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

Module EX20 <: EX.
  (* Error *)
  (* while 10 > 5 do (i + 1; ()) *)
  Definition s_i := sy 20.

  Definition ex : exp :=
    WhileExp (OpExp (IntExp 10) GtOp (IntExp 5))
             (SeqExp E[OpExp (VarExp (SimpleVar s_i)) PlusOp (IntExp 1);
                     SeqExp E[]]).
End EX20.

Module EX21 <: EX.
  (* Error *)
  (* let
       function nfactor(n : int) =
         if n = 0
           then 1
           else n * nfactor(n - 1)
     in
       nfactor(10)
     end *)
  Definition s_n := sy 20.
  Definition s_nfactor := sy 21.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_nfactor [Build_formals (Build_vardec s_n true) Env.s_int] None]
                    E[IfExp (OpExp (VarExp (SimpleVar s_n)) EqOp (IntExp 0))
                            (IntExp 1)
                            (Some (OpExp (VarExp (SimpleVar s_n)) TimesOp
                                         (AppExp s_nfactor E[OpExp (VarExp (SimpleVar s_n)) MinusOp
                                                                   (IntExp 1)])))]]
      (SeqExp E[AppExp s_nfactor E[IntExp 10]]).
End EX21.

Module EX22 <: EX.
  (* Error *)
  (* let
       type rectype = {name : string, id : int}
       var rec1 := rectype {name="Name", id=0}
     in
       rec1.nam := "asd"
     end *)
  Definition s_nam := sy 20.
  Definition s_rec1 := sy 21.
  Definition s_id := sy 22.
  Definition s_name := sy 23.
  Definition s_rectype := sy 24.

  Definition ex : exp :=
  LetExp
    D[TypeDec [Build_tydec s_rectype (RecordTy [Build_tfield s_name Env.s_string;
                                                Build_tfield s_id Env.s_int])];
      VarDec (Build_vardec s_rec1 true) None (RecordExp E[StringExp "Name";
                                                          IntExp 0]
                                                        [s_name; s_id]
                                                        s_rectype)]
    (SeqExp E[AssignExp (FieldVar (SimpleVar s_rec1) s_nam) (StringExp "asd")]).
End EX22.

Module EX23 <: EX.
  (* Error *)
  (* let
       type rectype = {name : string, id : int}
       var rec1 := rectype {name="aname", id=0}
     in
       rec1.name := 3
       rec1.id := ""
     end *)
  Definition s_rec1 := sy 20.
  Definition s_id := sy 21.
  Definition s_name := sy 22.
  Definition s_rectype := sy 23.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_rectype (RecordTy [Build_tfield s_name Env.s_string;
                                                  Build_tfield s_id Env.s_int])];
        VarDec (Build_vardec s_rec1 true) None (RecordExp E[StringExp "aname";
                                                            IntExp 0]
                                                          [s_name; s_id]
                                                          s_rectype)]
      (SeqExp E[AssignExp (FieldVar (SimpleVar s_rec1) s_name) (IntExp 3);
                AssignExp (FieldVar (SimpleVar s_rec1) s_id) (StringExp "")]).
End EX23.

Module EX24 <: EX.
  (* Error *)
  (* let
       var d := 0
     in
       d[3]
     end *)
  Definition s_d := sy 20.

  Definition ex : exp :=
    LetExp
      D[VarDec (Build_vardec s_d true) None (IntExp 0)]
      (SeqExp E[VarExp (SubscriptVar (SimpleVar s_d) (IntExp 3))]).
End EX24.

Module EX25 <: EX.
  (* Error *)
  (* let
       var d := 0
     in
       d.f
     end *)
  Definition s_f := sy 20.
  Definition s_d := sy 21.

  Definition ex : exp :=
    LetExp
      D[VarDec (Build_vardec s_d true) None (IntExp 0)]
      (SeqExp E[VarExp (FieldVar (SimpleVar s_d) s_f)]).
End EX25.

Module EX26 <: EX.
  (* Error *)
  (* 3 + "var" *)
  Definition ex : exp :=
    OpExp (IntExp 3) PlusOp (StringExp "var").
End EX26.

Module EX27 <: EX.
(* let
     var a := 0
     function g(a : int) : int = a
   in
     g(2)
   end *)
  Definition s_g := sy 20.
  Definition s_a := sy 21.

  Definition ex : exp :=
    LetExp
      D[VarDec (Build_vardec s_a true) None (IntExp 0);
        FunctionDec [Build_fundec s_g [Build_formals (Build_vardec s_a true) Env.s_int]
                                      (Some Env.s_int)]
                    E[VarExp (SimpleVar s_a)]]
      (SeqExp E[AppExp s_g E[IntExp 2]]).
End EX27.

Module EX28 <: EX.
  (* Error *)
  (* let
       type rectype1 = {name : string, id : int}
       type rectype2 = {name : string, id : int}
       var rec1 : rectype1 := rectype2 {name="Name", id=0}
     in
       rec1
     end *)
  Definition s_rec1 := sy 20.
  Definition s_rectype2 := sy 21.
  Definition s_id := sy 22.
  Definition s_name := sy 23.
  Definition s_rectype1 := sy 24.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_rectype1 (RecordTy [Build_tfield s_name Env.s_string;
                                                   Build_tfield s_id Env.s_int]);
                 Build_tydec s_rectype2 (RecordTy [Build_tfield s_name Env.s_string;
                                                   Build_tfield s_id Env.s_int])];
        VarDec (Build_vardec s_rec1 true) (Some s_rectype1) (RecordExp E[StringExp "Name";
                                                                         IntExp 0]
                                                                       [s_name; s_id]
                                                                       s_rectype2)]
      (SeqExp E[VarExp (SimpleVar s_rec1)]).
End EX28.

Module EX29 <: EX.
  (* Error *)
  (* let
       type arrtype1 = array of int
       type arrtype2 = array of int
       var arr1 : arrtype1 := arrtype2 [10] of 0
     in
       arr1
     end *)
  Definition s_arr1 := sy 20.
  Definition s_arrtype2 := sy 21.
  Definition s_arrtype1 := sy 22.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_arrtype1 (ArrayTy Env.s_int);
                 Build_tydec s_arrtype2 (ArrayTy Env.s_int)];
        VarDec (Build_vardec s_arr1 true) (Some s_arrtype1) (ArrayExp s_arrtype2
                                                                      (IntExp 10)
                                                                      (IntExp 0))]
      (SeqExp E[VarExp (SimpleVar s_arr1)]).
End EX29.

Module EX30 <: EX.
  (* let
       type a = array of int
       type b = a
       var arr1 : a := b [10] of 0
     in
       arr1[2]
     end *)
  Definition s_arr1 := sy 20.
  Definition s_b := sy 21.
  Definition s_a := sy 22.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_a (ArrayTy Env.s_int);
                 Build_tydec s_b (NameTy s_a)];
        VarDec (Build_vardec s_arr1 true) (Some s_a) (ArrayExp s_b
                                                               (IntExp 10)
                                                               (IntExp 0))]
      (SeqExp E[VarExp (SubscriptVar (SimpleVar s_arr1) (IntExp 2))]).
End EX30.

Module EX31 <: EX.
  (* Error *)
  (* let
       var a : int := " "
     in
       a
     end *)
  Definition s_a := sy 20.

  Definition ex : exp :=
    LetExp
      D[VarDec (Build_vardec s_a true) (Some Env.s_int) (StringExp " ")]
      (SeqExp E[VarExp (SimpleVar s_a)]).
End EX31.

Module EX32 <: EX.
  (* Error *)
  (* let
       type arrayty = array of int
       var a := arrayty [10] of " "
     in
       0
     end *)
  Definition s_a := sy 20.
  Definition s_arrayty := sy 21.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_arrayty (ArrayTy Env.s_int)];
        VarDec (Build_vardec s_a true) None (ArrayExp s_arrayty
                                                      (IntExp 10)
                                                      (StringExp " "))]
      (SeqExp E[IntExp 0]).
End EX32.

Module EX33 <: EX.
  (* Error *)
  (* let
       var a := rectype {}
     in
       0
     end *)
  Definition s_rectype := sy 20.
  Definition s_a := sy 21.

  Definition ex : exp :=
    LetExp
      D[VarDec (Build_vardec s_a true) None (RecordExp E[] [] s_rectype)]
      (SeqExp E[IntExp 0]).
End EX33.

Module EX34 <: EX.
  (* Error *)
  (* let
       function g (a : int, b : string) : int = a
     in
       g("one", "two")
     end *)
  Definition s_b := sy 20.
  Definition s_a := sy 21.
  Definition s_g := sy 22.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_g [Build_formals (Build_vardec s_a true) Env.s_int;
                                       Build_formals (Build_vardec s_b true) Env.s_string]
                                  (Some Env.s_int)]
                    E[VarExp (SimpleVar s_a)]]
      (SeqExp E[AppExp s_g E[StringExp "one"; StringExp "two"]]).
End EX34.

Module EX35 <: EX.
  (* Error *)
  (* let
       function g (a : int, b : string) : int = a
     in
       g("one")
     end *)
  Definition s_b := sy 20.
  Definition s_a := sy 21.
  Definition s_g := sy 22.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_g [Build_formals (Build_vardec s_a true) Env.s_int;
                                       Build_formals (Build_vardec s_b true) Env.s_string]
                                  (Some Env.s_int)]
                    E[VarExp (SimpleVar s_a)]]
      (SeqExp E[AppExp s_g E[StringExp "one"]]).
End EX35.

Module EX36 <: EX.
  (* Error *)
  (* let
       function g (a : int, b : string) : int = a
     in
       g(3, "one", 5)
     end *)
  Definition s_b := sy 20.
  Definition s_a := sy 21.
  Definition s_g := sy 22.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_g [Build_formals (Build_vardec s_a true) Env.s_int;
                                       Build_formals (Build_vardec s_b true) Env.s_string]
                                  (Some Env.s_int)]
                    E[VarExp (SimpleVar s_a)]]
      (SeqExp E[AppExp s_g E[IntExp 3; StringExp "one"; IntExp 5]]).
End EX36.

Module EX37 <: EX.
  (* let
       var a := 0
       var a := " "
     in
       0
     end *)
  Definition s_a := sy 20.

  Definition ex : exp :=
    LetExp
      D[VarDec (Build_vardec s_a true) None (IntExp 0);
        VarDec (Build_vardec s_a true) None (StringExp " ")]
      (SeqExp E[IntExp 0]).
End EX37.

Module EX38 <: EX.
  (* Error *)
  (* let
       type a = int
       type a = string
     in
       0
     end *)
  Definition s_a := sy 20.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_a (NameTy Env.s_int);
                 Build_tydec s_a (NameTy Env.s_string)]]
      (SeqExp E[IntExp 0]).
End EX38.

Module EX39 <: EX.
  (* Error *)
  (* let
       function g(a : int) : int = a
       function g(a : int) : int = a
     in
       0
     end *)
  Definition s_a := sy 20.
  Definition s_g := sy 21.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_g [Build_formals (Build_vardec s_a true) Env.s_int]
                                  (Some Env.s_int);
                     Build_fundec s_g [Build_formals (Build_vardec s_a true) Env.s_int]
                                  (Some Env.s_int)]
                    E[VarExp (SimpleVar s_a); VarExp (SimpleVar s_a)]]
      (SeqExp E[IntExp 0]).
End EX39.

Module EX40 <: EX.
  (* Error *)
  (* let
       function g(a : int) = a
     in
       g(2)
     end *)
  Definition s_a := sy 20.
  Definition s_g := sy 21.

  Definition ex : exp :=
    LetExp
      D[FunctionDec [Build_fundec s_g [Build_formals (Build_vardec s_a true) Env.s_int]
                                  None]
                    E[VarExp (SimpleVar s_a)]]
      (SeqExp E[AppExp s_g E[IntExp 2]]).
End EX40.

Module EX41 <: EX.
  (* let
       type a = int
     in
       let
         type a = string
       in
         0
       end
     end *)
  Definition s_a := sy 20.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_a (NameTy Env.s_int)]]
      (SeqExp 
        E[LetExp
          D[TypeDec [Build_tydec s_a (NameTy Env.s_string)]]
          (SeqExp E[IntExp 0])]).
End EX41.

Module EX42 <: EX.
  (* let
       type arrtype1 = array of int
       type rectype1 = {name : string, address : string, id: int, age: int}
       type arrtype2 = array of rectype1
       type rectype2 = {name : string, dates: arrtype1}
       type arrtype3 = array of string
       var arr1 := arrtype1 [10] of 0
       var arr2 := arrtype2 [5] of rectype1 {name="aname", address="somewhere", id=0, age=0}}
       var arr3 : arrtype3 := arrtype3 [100] of ""
       var rec1 := rectype1 {name="Kapoios", address="Kapou", id=02432, age=44}
       var rec2 := rectype2 {name="Allos", dates= arrtype1 [3] of 1900}
     in
       arr1[0] := 1;
       arr1[9] := 3;
       arr2[3].name := "kati";
       arr2[1].age := 23;
       arr3[34] := "sfd";
       rec1.name := "sdf";
       rec2.dates[0] := 2323;
       rec2.dates[2] := 2323
     end *)
  Definition s_rec2 := sy 20.
  Definition s_rec1 := sy 21.
  Definition s_arr3 := sy 22.
  Definition s_arr2 := sy 23.
  Definition s_arr1 := sy 24.
  Definition s_arrtype3 := sy 25.
  Definition s_dates := sy 26.
  Definition s_rectype2 := sy 27.
  Definition s_arrtype2 := sy 28.
  Definition s_age := sy 29.
  Definition s_id := sy 30.
  Definition s_address := sy 31.
  Definition s_name := sy 32.
  Definition s_rectype1 := sy 33.
  Definition s_arrtype1 := sy 34.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_arrtype1 (ArrayTy Env.s_int);
                 Build_tydec s_rectype1 (RecordTy [Build_tfield s_name Env.s_string;
                                                   Build_tfield s_address Env.s_string;
                                                   Build_tfield s_id Env.s_int;
                                                   Build_tfield s_age Env.s_int]);
                 Build_tydec s_arrtype2 (ArrayTy s_rectype1);
                 Build_tydec s_rectype2 (RecordTy [Build_tfield s_name Env.s_string;
                                                   Build_tfield s_dates s_arrtype1]);
                 Build_tydec s_arrtype3 (ArrayTy Env.s_string)];
        VarDec (Build_vardec s_arr1 true) None (ArrayExp s_arrtype1
                                                         (IntExp 10)
                                                         (IntExp 0));
        VarDec (Build_vardec s_arr2 true) None (ArrayExp s_arrtype2
                                                         (IntExp 5)
                                                         (RecordExp E[StringExp "aname";
                                                                      StringExp "somewhere";
                                                                      IntExp 0;
                                                                      IntExp 0]
                                                                    [s_name;
                                                                     s_address;
                                                                     s_id;
                                                                     s_age]
                                                                    s_rectype1));
        VarDec (Build_vardec s_arr3 true) (Some s_arrtype3) (ArrayExp s_arrtype3
                                                                      (IntExp 100)
                                                                      (StringExp ""));
        VarDec (Build_vardec s_rec1 true) None (RecordExp E[StringExp "Kapoios";
                                                            StringExp "Kapou";
                                                            IntExp 2432;
                                                            IntExp 44]
                                                          [s_name;
                                                           s_address;
                                                           s_id;
                                                           s_age]
                                                          s_rectype1);
        VarDec (Build_vardec s_rec2 true) None (RecordExp E[StringExp "Allos";
                                                            ArrayExp s_arrtype1
                                                                     (IntExp 3)
                                                                     (IntExp 1900)]
                                                          [s_name;
                                                           s_dates]
                                                          s_rectype2)]
      (SeqExp E[AssignExp (SubscriptVar (SimpleVar s_arr1) (IntExp 0)) (IntExp 1);
                AssignExp (SubscriptVar (SimpleVar s_arr1) (IntExp 9)) (IntExp 3);
                AssignExp (FieldVar (SubscriptVar (SimpleVar s_arr2) (IntExp 3)) s_name) (StringExp "kati");
                AssignExp (FieldVar (SubscriptVar (SimpleVar s_arr2) (IntExp 1)) s_age) (IntExp 23);
                AssignExp (SubscriptVar (SimpleVar s_arr3) (IntExp 34)) (StringExp "sfd");
                AssignExp (FieldVar (SimpleVar s_rec1) s_name) (StringExp "sdf");
                AssignExp (SubscriptVar (FieldVar (SimpleVar s_rec2) s_dates) (IntExp 0)) (IntExp 2323);
                AssignExp (SubscriptVar (FieldVar (SimpleVar s_rec2) s_dates) (IntExp 2)) (IntExp 2323)]).
End EX42.

Module EX43 <: EX.
  (* Error *)
  (* let
       var a := ()
     in
       a + 3
     end *)
  Definition s_a := sy 20.

  Definition ex : exp :=
    LetExp
      D[VarDec (Build_vardec s_a true) None (SeqExp E[])]
      (SeqExp E[OpExp (VarExp (SimpleVar s_a)) PlusOp (IntExp 3)]).
End EX43.

Module EX44 <: EX.
  (* let
       type rectype = {name : string, id : int}
       var b : rectype := nil
     in
       b := nil
     end *)
  Definition s_b := sy 20.
  Definition s_id := sy 21.
  Definition s_name := sy 22.
  Definition s_rectype := sy 23.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_rectype (RecordTy [Build_tfield s_name Env.s_string;
                                                  Build_tfield s_id Env.s_int])];
        VarDec (Build_vardec s_b true) (Some s_rectype) (NilExp)]
      (SeqExp E[AssignExp (SimpleVar s_b) (NilExp)]).
End EX44.

Module EX45 <: EX.
  (* Error *)
  (* let
       type rectype = {name : string, id : int}
       var a := rectype nil
       var a := nil
     in
       a
     end *)
  Definition s_a := sy 20.
  Definition s_id := sy 21.
  Definition s_name := sy 22.
  Definition s_rectype := sy 23.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_rectype (RecordTy [Build_tfield s_name Env.s_string;
                                                  Build_tfield s_id Env.s_int])];
        VarDec (Build_vardec s_a true) None (OpExp (VarExp (SimpleVar s_rectype)) PlusOp (NilExp));
        VarDec (Build_vardec s_a true) None (NilExp)]
      (SeqExp E[VarExp (SimpleVar s_a)]).
End EX45.

Module EX46 <: EX.
  (* Error *)
  (* let
       type rectype = {name : string, id : int}
       var b : rectype := nil
     in
       nil = nil;
       b = nil;
       b <> nil
     end *)
  Definition s_b := sy 20.
  Definition s_id := sy 21.
  Definition s_name := sy 22.
  Definition s_rectype := sy 23.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_rectype (RecordTy [Build_tfield s_name Env.s_string;
                                                  Build_tfield s_id Env.s_int])];
        VarDec (Build_vardec s_b true) (Some s_rectype) (NilExp)]
      (SeqExp E[OpExp (NilExp) EqOp (NilExp);
                OpExp (VarExp (SimpleVar s_b)) EqOp (NilExp);
                OpExp (VarExp (SimpleVar s_b)) NeqOp (NilExp)]).
End EX46.

Module EX47 <: EX.
  (* Error *)
  (* let
       type a = int
       var d := 0
       type a = a
     in
       0
     end *)
  Definition s_d := sy 20.
  Definition s_a := sy 21.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_a (NameTy Env.s_int)];
        VarDec (Build_vardec s_d true) None (IntExp 0);
        TypeDec [Build_tydec s_a (NameTy s_a)]]
      (SeqExp E[IntExp 0]).
End EX47.

Module EX48 <: EX.
  (* let
     in
     end *)

Definition ex : exp :=
  LetExp
    D[]
    (SeqExp E[]).
End EX48.

Module EX49 <: EX.
  (* let
       type i = int
       var t := 0
       type a = b
       type b = c
       type c = i
     in
     end *)
  Definition s_c := sy 20.
  Definition s_b := sy 21.
  Definition s_a := sy 22.
  Definition s_t := sy 23.
  Definition s_i := sy 24.

  Definition ex : exp :=
    LetExp
      D[TypeDec [Build_tydec s_i (NameTy Env.s_int)];
        VarDec (Build_vardec s_t true) None (IntExp 0);
        TypeDec [Build_tydec s_a (NameTy s_b);
                 Build_tydec s_b (NameTy s_c);
                 Build_tydec s_c (NameTy s_i)]]
      (SeqExp E[]).
End EX49.
