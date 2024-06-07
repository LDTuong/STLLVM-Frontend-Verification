(** ST-LLVM COMPILER VERIFICATION: Preliminaries *)


(* Imports *)

Set Warnings "-notation-overridden,-parsing".
Require Import ZArith.
Require Import Coq.Strings.String.
Open Scope string_scope. 



(* ########################################################################### *)
(** * UTILS *)


(* Ids / Variables *)

Inductive id : Type :=
  | Id : string -> id.

Definition concat (x : id) (y : id) : id :=
  match x,y with
  | Id s1 , Id s2 => Id (s1 ++ s2)
  end.

Definition eq_id x y :=
  match x,y with
  | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Fixpoint nat_to_id_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
            | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
            | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
            end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => nat_to_id_aux time' n' acc'
      end
  end.

Definition nat_to_id (n : nat) : id :=
  Id (nat_to_id_aux n n "").
  

(* Numbers *)

(* TODO: Bitvector representation *)
(* OPTIONAL: parametrized number representation *) 

Definition number := Z.
Global Open Scope Z_scope.
Check 0.

Definition zero := 0.
Definition eq := Z.eqb.
Definition le := Z.leb.

Inductive data_type : Type :=
  | Int : data_type
  | Bool : data_type.


(* Witness Extraction *)

Definition extract {A B C : Type} (P : A -> B -> C -> Prop) :
  (forall a b, { c : C | P a b c }) ->
  { f : A -> B -> C | forall a b, P a b (f a b) } :=
  fun g => exist (fun f => forall a b, P a b (f a b))
                 (fun a b => proj1_sig (g a b))
                 (fun a b => proj2_sig (g a b)).


(* Maps *)

Definition map (A:Type) := id -> A.
Definition empty_map {A:Type} (default:A) : map A :=
  (fun _ => default).
Definition update {A:Type} (m : map A) (x : id) (v : A) :=
  fun x' => if eq_id x x' then v else m x'.
Notation "m '[' x '->' v ']'" := 
  (update m x v) (at level 60, x,v at level 59).  

Definition state := map number.
Definition empty_state := empty_map zero.


(* Function Arguments as list of pairs *)

Inductive argument : Type :=
  | arg (x:id) (v:number).
Notation "x : v" := 
  (arg x v) (at level 100).
Notation "[ x1 ; .. ; xn ]" :=
  (cons x1 .. (cons xn nil) ..) (at level 60).

Fixpoint applyFuncArgs (st : state) (args: list argument) : state :=
  match args with
  | nil            =>  st
  | cons (x:v) xs  =>  applyFuncArgs (st[x -> v]) xs
  end.

Definition X     := Id "X".
Definition Y     := Id "Y".
Definition Z     := Id "Z".
Definition f     := Id "f".
Definition p     := Id "p".
Definition foo   := Id "foo".
Definition bar   := Id "bar".
Definition entry := Id "entry".
Definition main  := Id "main".



(* ########################################################################### *)
(** * ARITHMETIC/BOOLEAN EXPRESSIONS *)


(* Syntax *)

Inductive aExp : Type :=
  | ANum   : number -> aExp
  | AId    : id -> aExp
  | APlus  : aExp -> aExp -> aExp
  | AMinus : aExp -> aExp -> aExp
  | AMult  : aExp -> aExp -> aExp
  | ADiv   : aExp -> aExp -> aExp
  | AMod   : aExp -> aExp -> aExp.

Inductive bExp : Type :=
  | BVal : bool -> bExp
  | BEq  : aExp -> aExp -> bExp
  | BLe  : aExp -> aExp -> bExp
  | BNot : bExp -> bExp
  | BAnd : bExp -> bExp -> bExp. 


(* Denotational Semantics *)

Fixpoint aEval (st:state) (a:aExp) : number :=
  match a with
  | ANum n        =>  n
  | AId x         =>  st x
  | APlus a1 a2   =>  (aEval st a1)  +  (aEval st a2)
  | AMinus a1 a2  =>  (aEval st a1)  -  (aEval st a2)
  | AMult a1 a2   =>  (aEval st a1)  *  (aEval st a2)
  | ADiv a1 a2    =>  (aEval st a1)  /  (aEval st a2)
  | AMod a1 a2    =>  (aEval st a1) mod (aEval st a2)
  end.

Fixpoint bEval (st:state) (b:bExp) : bool :=
  match b with
  | BVal v          =>  v
  | BEq a1 a2       =>  eq (aEval st a1) (aEval st a2)
  | BLe a1 a2       =>  le (aEval st a1) (aEval st a2)
  | BNot exp        =>  negb (bEval st exp)
  | BAnd exp1 exp2  =>  andb (bEval st exp1) (bEval st exp2)
  end.


(* Operational Semantics *)

Inductive aEvalR : state -> aExp -> number -> Prop :=
  | E_ANum : forall st (n:number),
      aEvalR st (ANum n) n
  | E_Id : forall st (x:id),
      aEvalR st (AId x) (st x)
  | E_APlus : forall st a1 a2 n1 n2 n3,
      aEvalR st a1 n1 ->
      aEvalR st a2 n2 ->
      n1 + n2 = n3 ->
      aEvalR st (APlus a1 a2) n3
  | E_AMinus : forall st a1 a2 n1 n2 n3,
      aEvalR st a1 n1 ->
      aEvalR st a2 n2 ->
      n1 - n2 = n3 ->
      aEvalR st (AMinus a1 a2) n3
  | E_AMult : forall st a1 a2 n1 n2 n3,
      aEvalR st a1 n1 ->
      aEvalR st a2 n2 ->
      n1 * n2 = n3 ->
      aEvalR st (AMult a1 a2) n3
  | E_ADiv : forall st a1 a2 n1 n2 n3,
      aEvalR st a1 n1 ->
      aEvalR st a2 n2 ->
      (n2 > 0) ->
      (n2 * n3 = n1) ->
      aEvalR st (ADiv a1 a2) n3 
  | E_AMod : forall st a1 a2 n1 n2 r,
      aEvalR st a1 n1 ->
      aEvalR st a2 n2 ->
      (exists q, n1 = (n2 * q) + r) ->
      (r < n2) ->
      aEvalR st (AMod a1 a2) r.

Inductive bEvalR: state -> bExp -> bool -> Prop :=
  | E_BVal : forall st (b:bool),
      bEvalR st (BVal b) b
  | E_BEq : forall st a1 a2 n1 n2 b,
      aEvalR st a1 n1 ->
      aEvalR st a2 n2 ->
      eq n1 n2 = b ->
      bEvalR st (BEq a1 a2) b
  | E_BLe : forall st a1 a2 n1 n2 b,
      aEvalR st a1 n1 ->
      aEvalR st a2 n2 ->
      le n1 n2 = b ->
      bEvalR st (BLe a1 a2) b
  | E_BNot : forall st bExp bVal1 bVal2,
      bEvalR st bExp bVal1 ->
      negb bVal1 = bVal2 ->
      bEvalR st (BNot bExp) bVal2
  | E_BAnd : forall st bExp1 bExp2 bVal1 bVal2 bVal3,
      bEvalR st bExp1 bVal1 ->
      bEvalR st bExp2 bVal2 ->
      andb bVal1 bVal2 = bVal3 ->
      bEvalR st (BAnd bExp1 bExp2) bVal3.