(*string imports*)
Require Import Strings.String.
Require Import List.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.

(*some errors*)

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion num: nat >-> ErrorNat.
Coercion boolean: bool >-> ErrorBool.



(*Var Types*)
Inductive NNat :=
| nat_err : NNat
| nat_val : nat -> NNat.

Inductive BBool :=
| bool_err : BBool
| b_true : BBool
| b_false : BBool.

Inductive SString :=
|str_err : SString
|str_val : string -> SString.
(* A general type which includes all kind of types *)
Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | value_nat : NNat -> Result
  | value_bool : BBool -> Result
  | value_string : SString -> Result.


Scheme Equality for Result.

(* An environment which maps variable names (strings) to the Result type *)
Definition Env := string -> Result.

(* Initial environment *)
Definition env : Env := fun  x => err_undecl.
(*variables declared*)



(*arithmethic stuff*)
Inductive AExp :=
| avar : string -> AExp
| aint : NNat -> AExp  
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.

Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "A -' B" := (amin A B) (at level 60, right associativity).
Notation "a /' b" := (adiv a b) (at level 58, left associativity).
Notation "a %' b" := (amod a b) (at level 58, left associativity).


(*bool stuff*)
Inductive BExp :=
| bvar : Env -> BExp
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor  : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bdifferent : AExp -> AExp -> BExp
| bless_equal : AExp -> AExp -> BExp
| bgreater_equal : AExp -> AExp -> BExp
| bequal : AExp -> AExp -> BExp.

Notation "A <' B" := (blessthan A B) (at level 80).
Notation "A >' B" := (bgreaterthan A B) (at level 80).
Notation "A >=' B" := (bgreater_equal A B) (at level 80).
Notation "A <=' B" := (bless_equal A B) (at level 80).
Notation "A !=' B" := (bdifferent A B) (at level 80).
Notation "A =' B" := (bequal A B) (at level 80).
Infix "and'" := band (at level 82).
Infix "or'" := bor (at level 82).
Notation "!' A" := (bnot A) (at level 81).
(*string manipulations*)
Inductive STRexp :=
| s_var : Env -> STRexp
| s_str : SString -> STRexp
| s_concat: STRexp -> STRexp -> STRexp.

Notation "STR1 <--> STR2" := (s_concat STR1 STR2) (at level 53).

(**)
Inductive Exp :=
| e_Aexp : AExp -> Exp
| e_Bexp : BExp -> Exp
| e_STRexp : STRexp -> Exp.

(*pointer*)
Inductive Adress :=
| ad_var : Env -> Adress.


(*vector/pointers/types*)
Inductive Declaration :=
| decl_int_exp : string -> AExp -> Declaration
| decl_bool_exp : string -> BExp -> Declaration
| decl_string_exp : string -> STRexp -> Declaration
| decl_int : string -> Declaration
| decl_bool : string -> Declaration
| decl_string : string -> Declaration
| decl_struct: string -> list Declaration -> Declaration
| decl_vect_int : string -> nat -> Declaration
| decl_vect_bool : string -> nat -> Declaration
| decl_vect_string : string -> nat -> Declaration
| decl_vect_int_init : string -> nat -> list NNat -> Declaration
| decl_vect_bool_init : string -> nat -> list BBool -> Declaration
| decl_vect_string_init : string -> nat -> list SString -> Declaration
| decl_mat_int : string -> nat -> nat -> Declaration
| decl_mat_bool : string -> nat  -> nat -> Declaration
| decl_mat_string : string -> nat -> nat -> Declaration
| decl_mat_int_init : string -> nat -> nat -> list NNat -> list NNat -> Declaration
| decl_mat_bool_init : string -> nat -> nat -> list BBool -> list BBool -> Declaration
| decl_mat_string_init : string -> nat -> nat -> list SString -> list SString -> Declaration
| decl_pointer_int : string -> Declaration
| decl_pointer_bool : string -> Declaration
| decl_pointer_string : string -> Declaration
| decl_pointer_int_init : string -> Adress -> Declaration
| decl_pointer_bool_init : string -> Adress -> Declaration
| decl_pointer_string_init : string -> Adress -> Declaration.

Notation "'int' A " := (decl_int A)(at level 50).
Notation "'int' A --> V" := (decl_int_exp A  V)(at level 50).
Notation "'int*' A " := (decl_pointer_int A)(at level 50).
Notation "'int*' A --> AD" := (decl_pointer_int_init A AD) (at level 50).
Notation "'Bbool' B " := (decl_bool B)(at level 50).
Notation "'Bbool' B --> V" := (decl_bool_exp B  V)(at level 50).
Notation "'Bbool*' B --> AD" := (decl_pointer_bool_init B AD) (at level 50).
Notation "'Bbool*' B " := (decl_pointer_bool B)(at level 50).
Notation "'chars' S " := (decl_string S)(at level 50).
Notation "'chars' S --> V" := (decl_string_exp S  V)(at level 50).
Notation "'chars*' S --> AD" := (decl_pointer_string_init S AD) (at level 50).
Notation "'chars*' S |" := (decl_pointer_string S)(at level 50).
Notation "'struct'' S '{'' D1 ; D2 ; .. ; Dn '}''" := (decl_struct S (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) )(at level 50).
Notation "'int' V [ Nr ]" := ( decl_vect_int V Nr) (at level 50). 
Notation "'Bbool' V [ Nr ]" := ( decl_vect_bool V Nr) (at level 50). 
Notation "'chars' V [ Nr ]" := ( decl_vect_string V Nr) (at level 50). 
Notation "'int' V [ Nr ] --> '{' List '}'" := (decl_vect_int_init V Nr (List)) (at level 50).
Notation "'Bbool' V [ Nr ] --> '{'' List '}''" := (decl_vect_bool_init V Nr (List) ) (at level 50).
Notation "'chars' V [ Nr ] --> '{'' List '}''" := (decl_vect_string_init V Nr (List)) (at level 50).

Notation "'int' V [ Nr ][ Nr2 ] " := ( decl_mat_int V Nr Nr2) (at level 50). 
Notation "'Bbool' V [ Nr ][ Nr2 ]" := ( decl_mat_bool V Nr Nr2) (at level 50). 
Notation "'chars' V [ Nr ][ Nr2 ]" := ( decl_mat_string V Nr Nr2) (at level 50). 
(*Notation "'int' V [ Nr1 ][ Nr2 ] --> '{' L1 ; L2 ; .. ; Ln '}'" := (decl_mat_int_init V (List L1 ..(List L2 .. (List Ln nil)..) ..) .. ) (at level 50)*)


(*writing stuff*)
Inductive Stmt :=
| assignment : Env -> AExp -> Stmt
| while : BExp -> Stmt -> Stmt
| ifelse : BExp -> Stmt -> Stmt ->Stmt
| seq : Stmt -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 85).
Notation "S1 ;; S2" := (seq S1 S2) (at level 99).
Notation "WWhile( A ){ B }" := (while A B) (at level 85).
Notation "IF( A ){ B }ELSE{ C }" := (ifelse A B C) (at level 85).

(*functions*)
Inductive Fun :=
| decl_fun_int: Env -> list Declaration -> Stmt -> Fun
| decl_fun_bool: Env -> list Declaration -> Stmt -> Fun
| decl_fun_string: Env -> list Declaration -> Stmt -> Fun.

Notation "'chars A ( B1 , B2 , .. , Bn ){ C }" := (decl_fun_string A (cons B1 ( cons B2 .. (cons Bn nil) .. ) ) C) (at level 50).
Notation "'int' A ( B1 , B2 , .. , Bn ){ C }" := (decl_fun_int A (cons B1 ( cons B2 .. (cons Bn nil) .. ) ) C) (at level 50).
Notation "'Bbool' A ( B1 , B2 , .. , Bn ){ C }" := (decl_fun_bool A (cons B1 ( cons B2 .. (cons Bn nil) .. ) ) C) (at level 50).

(* Semantix *)


Definition get_nat (v : Result) : NNat :=
match v with
| value_nat n => n
| _ => nat_err
end.

Definition get_bool (v : Result) : BBool :=
match v with
| value_bool b => b 
| _ => bool_err
end.

Definition get_str (v : Result) : SString :=
match v with
| value_string s => s
| _ => str_err
end.

Coercion value_nat: NNat >-> Result.
Coercion value_bool: BBool >-> Result.
Coercion value_string : SString >-> Result.

Definition EnvS := string -> Result.



Definition update_value (env : Env)
           (x : string) (v : Result) : Env :=
  fun y =>
    if (string_dec y x)
    then v
    else (env y).

Definition update (env : Env)
           (x : string) : Env := (update_value env x err_undecl).


Definition add_nat (x y : NNat) : NNat :=
match x, y with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val x, nat_val y => nat_val (x + y)
end.

Definition mul_nat (x y : NNat) : NNat :=
match x, y with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val x, nat_val y => nat_val (x * y)
end.

Coercion nat_val : nat >-> NNat.


Definition div_nat (x y : NNat) : NNat :=
match x, y with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val x, nat_val y => Nat.div x y
end.

Definition mod_nat (x y : NNat) : NNat :=
match x, y with
| nat_err, _ => nat_err
| _ ,nat_err => nat_err
| nat_val x, nat_val y => Nat.modulo x y
end.

Fixpoint get_from_nat_vector (l : list NNat) (n : nat) : NNat :=
match n, l with
| O, x::l1 => x
| S m, nil => nat_err
| S m, x::l2 => (get_from_nat_vector l2 m)
| _, _ => nat_err
end.

Fixpoint get_from_bool_vector (l : list BBool) (n : nat) : BBool :=
match n, l with
| O, x::l1 => x
| S m, nil => bool_err
| S m, x::l2 => (get_from_bool_vector l2 m)
| _, _ => bool_err
end.

Fixpoint get_from_str_vector (l : list SString) (n : nat) : SString :=
match n, l with
| O, x::l1 => x
| S m, nil => str_err
| S m, x::l2 => (get_from_str_vector l2 m)
| _, _ => str_err
end.
Reserved Notation "A =[ S ]=> N" (at level 40).
(*Inductive aeval : AExp -> Env -> NNat -> Prop :=
| e_aconst : forall n sigma, aint n =[ sigma ]=> n 
| e_avar : forall v sigma, avar v =[ sigma ]=> (get_nat (sigma v))
| e_add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n =  add_nat i1 i2 ->
    a1 +' a2 =[sigma]=> n
| e_mul : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = mul_nat i1 i2 ->
    a1 *' a2 =[sigma]=> n
| e_sub : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n =  sub_nat i1 i2 ->
    a1 -' a2 =[sigma]=> n
| e_div : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n =  div_nat i1 i2 ->
    a1 /' a2 =[sigma]=> n
| e_mod : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n =  mod_nat i1 i2 ->
    a1 %' a2 =[sigma]=> n
| e_bool_to_nat : forall b sigma, a_bool_to_nat b =[ sigma ]=> conv_bool_nat b

| e_aget_vect_val : forall v1 v2 n sigma,
  v2 = (sigma v1) ->
  a_get_vect_val v1 n =[ sigma ]=> get_nat (get_element v2 n)

where "a =[ sigma ]=> n" := (aeval a sigma n).*)

Definition val_Bool (b : bool) : BBool :=
match b with
| true => b_true
| false => b_false
end.


Definition less_than(a1 a2 : NNat) : BBool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => val_Bool (Nat.ltb n1 n2)
end.


Definition less_equal_than(a1 a2 : NNat) : BBool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => val_Bool (Nat.leb n1 n2)
end.

Definition greater_than(a1 a2 : NNat) : BBool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => val_Bool (Nat.leb n2 n1)
end.

Definition greater_equal_than(a1 a2 : NNat) : BBool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => val_Bool (Nat.ltb n2 n1)
end.

Definition equality(a1 a2 : NNat) : BBool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => val_Bool (Nat.eqb n1 n2)
end.

Definition different(a1 a2 : NNat) : BBool :=
match a1, a2 with
| _, nat_err => bool_err
| nat_err, _ => bool_err
| nat_val n1, nat_val n2 => val_Bool (negb (Nat.eqb n1 n2))
end.

Reserved Notation "B ={ S }=> B'" (at level 60).
(*
Inductive beval : BExp -> Env -> BBool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> b_true
| e_false : forall sigma, bfalse ={ sigma }=> b_false

(*| e_b_var : forall v sigma, bvar v ={ sigma }=> get_bool (sigma v)*)

| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = less_than (get_nat i1) (get_nat i2) ->
    a1 <' a2 ={ sigma }=> b

| e_less_equal_than : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = less_equal_than (get_nat i1) (get_nat i2) ->
    a1 <=' a2 ={ sigma }=> b

| e_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = greater_than (get_nat i1) (get_nat i2) ->
    a1 <' a2 ={ sigma }=> b

| e_grater_equal_than : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = less_equal_than i1 i2->
    a1 <=' a2 ={ sigma }=> b

| e_nottrue : forall b sigma,
    b ={ sigma }=> b_true ->
    !' b ={ sigma }=> b_false

| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> b_true ->
    b2 ={ sigma }=> t ->
    b1 and' b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> b_false ->
    b1 and' b2 ={ sigma }=> b_false

| e_ortrue : forall b1 b2 sigma,
    b1 ={ sigma }=> b_true ->
    b1 or' b2 ={ sigma }=> b_true

| e_orfalse : forall b1 b2 sigma t,
    b1 ={ sigma }=> b_false ->
    b2 ={ sigma }=> t ->
    b1 or' b2 ={ sigma }=> t

| e_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = equality i1 i2 ->
    a1 =' a2 ={ sigma }=> b

| e_different : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = different i1 i2 ->
    a1 =' a2 ={ sigma }=> b

| e_nat_to_bool : forall a sigma,  b_nat_to_bool a ={ sigma }=> conv_nat_bool a

| e_bget_vect_val : forall v1 v2 n sigma,
  v2 = (sigma v1) ->
  b_get_vect_val v1 n ={ sigma }=> get_bool (get_element v2 n)

where "B ={ S }=> B'" := (beval B S B').*)
