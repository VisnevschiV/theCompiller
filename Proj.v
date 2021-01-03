(*string imports*)
Require Import Strings.String.
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

(* A general type which includes all kind of types *)
Inductive Result :=
  | err_undecl : Result
  | err_assign : Result
  | default : Result
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result.


Scheme Equality for Result.

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

(* An environment which maps variable names (strings) to the Result type *)
Definition Env := string -> Result.

(* Initial environment *)
Definition env : Env := fun  x => err_undecl.
(*variables declared*)



(*arithmethic stuff*)
Inductive AExp :=
| avar : Env -> AExp  
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.
Coercion avar : Env >-> AExp.

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
Notation "! A" := (bnot A) (at level 81).
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
| decl_int_exp : Env -> AExp -> Declaration
| decl_bool_exp : Env -> BExp -> Declaration
| decl_string_exp : Env -> STRexp -> Declaration
| decl_int : Env -> Declaration
| decl_bool : Env -> Declaration
| decl_string : Env -> Declaration
| decl_struct: Env -> list Declaration -> Declaration
| decl_vect_int : Env -> nat -> Declaration
| decl_vect_bool : Env -> nat -> Declaration
| decl_vect_string : Env -> nat -> Declaration
| decl_vect_int_init : Env -> nat -> list NNat -> Declaration
| decl_vect_bool_init : Env -> nat -> list BBool -> Declaration
| decl_vect_string_init : Env -> nat -> list SString -> Declaration
| decl_mat_int : Env -> nat -> nat -> Declaration
| decl_mat_bool : Env -> nat  -> nat -> Declaration
| decl_mat_string : Env -> nat -> nat -> Declaration
| decl_mat_int_init : Env -> nat -> nat -> list NNat -> list NNat -> Declaration
| decl_mat_bool_init : Env -> nat -> nat -> list BBool -> list BBool -> Declaration
| decl_mat_string_init : Env -> nat -> nat -> list SString -> list SString -> Declaration
| decl_pointer_int : Env -> Declaration
| decl_pointer_bool : Env -> Declaration
| decl_pointer_string : Env -> Declaration
| decl_pointer_int_init : Env -> Adress -> Declaration
| decl_pointer_bool_init : Env -> Adress -> Declaration
| decl_pointer_string_init : Env -> Adress -> Declaration.

Notation "'int' A " := (decl_int A)(at level 50).
Notation "'int' A --> V" := (decl_int_exp A  V)(at level 50).
Notation "'int*' A " := (decl_pointer_int A)(at level 50).
Notation "'int*' A --> AD" := (decl_pointer_int_init A AD) (at level 50).
Notation "'bool' B " := (decl_bool B)(at level 50).
Notation "'bool' B --> V" := (decl_bool_exp B  V)(at level 50).
Notation "'bool*' B --> AD" := (decl_pointer_bool_init B AD) (at level 50).
Notation "'bool*' B " := (decl_pointer_bool B)(at level 50).
Notation "'string' S " := (decl_string S)(at level 50).
Notation "'string' S --> V" := (decl_string_exp S  V)(at level 50).
Notation "'string*' S --> AD" := (decl_pointer_string_init S AD) (at level 50).
Notation "'string*' S |" := (decl_pointer_string S)(at level 50).
Notation "'struct'' S '{'' D1 ; D2 ; .. ; Dn '}''" := (decl_struct S (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) )(at level 50).
Notation "'int' V [ Nr ]" := ( decl_vect_int V Nr) (at level 50). 
Notation "'bool' V [ Nr ]" := ( decl_vect_bool V Nr) (at level 50). 
Notation "'string' V [ Nr ]" := ( decl_vect_string V Nr) (at level 50). 
Notation "'int' V [ Nr ] --> '{'' E1 , E2 , .. , En '}''" := (decl_vect_int_init V Nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'bool' V [ Nr ] --> '{'' E1 , E2 , .. , En '}''" := (decl_vect_bool_init V Nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'string' V [ Nr ] --> '{'' E1 , E2 , .. , En '}''" := (decl_vect_string_init V Nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).

Notation "'int' V [ Nr ][ Nr2 ] " := ( decl_vect_int V Nr Nr2) (at level 50). 
Notation "'bool' V [ Nr ][ Nr2 ]" := ( decl_vect_bool V Nr Nr2) (at level 50). 
Notation "'string' V [ Nr ][ Nr2 ]" := ( decl_vect_string V Nr Nr2) (at level 50). 


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

Notation "'string' A ( B1 , B2 , .. , Bn ){ C }" := (decl_fun_string A (cons B1 ( cons B2 .. (cons Bn nil) .. ) ) C) (at level 50).
Notation "'int' A ( B1 , B2 , .. , Bn ){ C }" := (decl_fun_int A (cons B1 ( cons B2 .. (cons Bn nil) .. ) ) C) (at level 50).
Notation "'bool' A ( B1 , B2 , .. , Bn ){ C }" := (decl_fun_bool A (cons B1 ( cons B2 .. (cons Bn nil) .. ) ) C) (at level 50).





