(** ST-LLVM COMPILER VERIFICATION: LLVM-IR *)


(** * Imports *)

Set Warnings "-notation-overridden,-parsing".
Require Import ZArith.
Require Import Coq.Strings.String.
Open Scope string_scope. 

From STLLVM Require Import Prelims.



(* ########################################################################### *)
(** * SYNTAX *)


(** * (Branching) Instructions *)

Inductive LLVM_instr : Type :=
  | LLVM_Ass   : id -> aExp -> LLVM_instr
  | LLVM_Call  : id -> list argument -> LLVM_instr.
Notation "x '=' 'bop' v" := (LLVM_Ass x v) (at level 60).
Notation "'call' f ',' args" := (LLVM_Call f args) (at level 60).

Inductive LLVM_brnch : Type :=
  | LLVM_Br    : bExp -> id -> id -> LLVM_brnch
  | LLVM_Ret   : LLVM_brnch.
Notation "'br' exp ',' b1 ',' b2" := (LLVM_Br exp b1 b2) (at level 60).
Notation "'ret'"                  := LLVM_Ret.


(** * Basic Blocks *)

Inductive LLVM_bBlock : Type :=
  | LLVM_BBlock (name : id) (body : list LLVM_instr) (term : LLVM_brnch).
Notation "name ':' bBody ',' term" :=
  (LLVM_BBlock name bBody term) (at level 100, bBody,term at level 99).


(** * Functions *)

Inductive LLVM_function : Type :=
  | LLVM_Function (name : id) (body : list LLVM_bBlock).
Notation "'define' name ':=' fBody" :=
  (LLVM_Function name fBody) (at level 100, name,fBody at level 99).

Definition blockEnvr   := map LLVM_bBlock.
Definition empty_bEnvr := empty_map ((Id ""): nil, ret).

Fixpoint hasEntryBlock (fBody : list LLVM_bBlock) : bool :=
  match fBody with
  | nil                         =>  false
  | cons (name: bBody,term) bs  =>  if    eq_id name entry
                                    then  true
                                    else  hasEntryBlock bs
  end.

Definition funcHasEntryBlock (f:LLVM_function) : bool :=
  match f with
  | (define name := fBody) => hasEntryBlock fBody
  end.


(** * Modules *)

Inductive LLVM_module : Type :=
  | LLVM_Module (mBody : list LLVM_function). 

Definition funcEnvr       := map LLVM_function.
Definition empty_funcEnvr := empty_map (define (Id "") := nil).

Definition getFirstFunc (m : LLVM_module) : LLVM_function :=
  match m with
  | LLVM_Module (cons (define name := fBody) fs) => (define name := fBody)
  | _ => (define (Id "") := nil)
  end.



(* ########################################################################### *)
(** * SEMANTICS *)


(** * Instruction Execution *)

Definition instrExec (fEnvr:funcEnvr) (c:LLVM_instr) (st:state) : state :=
  match c with
  | LLVM_Ass x v      =>  st[x -> (aEval st v)]
  | LLVM_Call f args  =>  (applyFuncArgs st args) (*POSTPONED*)
  end.


(** * Block Execution *)

Fixpoint bodyExec (fEnvr:funcEnvr) (st:state) (bBody : list LLVM_instr) : state :=
  match bBody with 
  | nil        =>  st
  | cons c cs  =>  bodyExec fEnvr (instrExec fEnvr c st) cs
  end.

Definition branch (st : state) (t : LLVM_brnch) : id := 
  match t with
  | br exp,b1,b2  =>  if (bEval st exp) then b1 else b2
  | ret           =>  Id ""
  end.

Definition isBranching (t : LLVM_brnch) : bool := 
  match t with
  | br exp,b1,b2  =>  true
  | ret           =>  false
  end.

  
(** * Function Evaluation *)

Fixpoint fBodyToBEnvr_aux
  (envr : blockEnvr) (fBody : list LLVM_bBlock) : blockEnvr :=
  match fBody with
  | nil                         =>  envr
  | cons (name: bBody,term) bs  =>  fBodyToBEnvr_aux 
                                    (envr[name -> (name: bBody,term)])
                                    bs
  end.

Definition fBodyToBEnvr (fBody : list LLVM_bBlock) : blockEnvr :=
  fBodyToBEnvr_aux empty_bEnvr fBody.

Definition getBEnvrFromFunc (f:LLVM_function) : blockEnvr :=
  match f with
  | (define name := fBody) => fBodyToBEnvr fBody
  end.

Reserved Notation "fEnvr * bEnvr / < curr , st1 > 'LLVM=>' < next , st2 >"
  (at level 40, bEnvr,curr,next,st1,st2 at level 39).

Inductive LLVM_branchEval :
  funcEnvr -> blockEnvr -> id -> state -> id -> state -> Prop := 
      
  (* Branch case *)
  (*
  | E_LLVM_Br : forall fEnvr bEnvr st1 st2 bID1 bID2 name body term,
      bEnvr bID1 = (name: body,term) ->
      bodyExec fEnvr st1 body = st2 ->
      isBranching term = true ->
      branch st2 term = bID2 ->
      fEnvr * bEnvr / <bID1, st1> LLVM=> <bID2, st2> *)

  (* Unfold path *)
  | E_LLVM_Unfd : forall fEnvr bEnvr name body term bID1 bID2 bID3 st1 st2 st3,
      bEnvr bID1 = (name: body,term) ->
      bodyExec fEnvr st1 body = st2 ->
      isBranching term = true ->
      branch st2 term = bID2 ->      
      fEnvr * bEnvr / <bID2, st2> LLVM=> <bID3, st3> ->
      fEnvr * bEnvr / <bID1, st1> LLVM=> <bID3, st3>

  (* Return case *)
  | E_LLVM_Ret : forall fEnvr bEnvr st1 st2 bID name body term,
      bEnvr bID = (name: body,term) ->
      bodyExec fEnvr st1 body = st2 ->
      isBranching term = false ->
      fEnvr * bEnvr / <bID, st1> LLVM=> <bID, st2>

  where "fEnvr * bEnvr / < bID1 , st1 > 'LLVM=>' < bID2 , st2 >" := 
    (LLVM_branchEval fEnvr bEnvr bID1 st1 bID2 st2).

Reserved Notation "fEnvr // < f , st1 > 'LLVM=>' st2"
  (at level 40, f,st1,st2 at level 39).

Inductive LLVM_funcEval : 
  funcEnvr -> LLVM_function -> state -> state -> Prop :=

  | E_LLVM_Func : forall fEnvr f bID st1 st2,
      funcHasEntryBlock f = true ->
      fEnvr * (getBEnvrFromFunc f)  /  <entry, st1> LLVM=> <bID, st2> ->
      fEnvr                         // <f    , st1> LLVM=> st2

  where "fEnvr // < fID , st1 > 'LLVM=>' st2" := 
    (LLVM_funcEval fEnvr fID st1 st2).

  
(** * Module Evaluation *)

Fixpoint registerFuncsToEnvr 
  (envr : funcEnvr) (funcs : list LLVM_function) : funcEnvr :=
  match funcs with
  | nil                             =>  envr
  | cons (define name := fBody) bs  =>  registerFuncsToEnvr 
                                        (envr[name -> (define name := fBody)])
                                        bs
  end.

Definition getFuncEnvrFromModule (m:LLVM_module) : funcEnvr :=
  match m with
  | LLVM_Module mBody => registerFuncsToEnvr empty_funcEnvr mBody
  end.

Reserved Notation "< m , st1 > LLVM=> st2"
(at level 40, m,st1 at level 39).

Inductive LLVM_moduleEvalR : LLVM_module -> state -> state -> Prop :=
  | E_LLVM_Module : forall m fEnvr f st1 st2,
      getFuncEnvrFromModule m = fEnvr ->
      getFirstFunc m = f ->
      fEnvr // < f , st1 > LLVM=> st2 ->
      < m , st1 > LLVM=> st2
  where "< m , st1 > LLVM=> st2" :=
    (LLVM_moduleEvalR m st1 st2).



(* ########################################################################### *)
(** * EXAMPLES *)

Definition if_then  := Id "if_then".
Definition if_else  := Id "if_else".

Example ex_LLVM_Ret:
  empty_funcEnvr //
  <
    define foo := [
      entry: [
        X = bop (ANum 1)
      ],
      ret
    ]
    , empty_state 
  >
  LLVM=> (empty_state[X->1]).
Proof.
  apply E_LLVM_Func with entry;
  try reflexivity.
  apply E_LLVM_Ret with entry ([X = bop (ANum 1)]) ret;
  reflexivity.
Qed.

Example ex_LLVM_Unfd:
  empty_funcEnvr //
  < 
    define foo := [
      entry: 
        [X = bop (ANum 1)],
        br (BVal true),if_then,if_else;
      if_then:
        [Y = bop (ANum 2)],
        ret;
      if_else:
        [Z = bop (ANum 3)],
        ret
    ] 
    , empty_state
  > 
  LLVM=> (empty_state[X->1][Y->2]).
Proof.
  apply E_LLVM_Func with if_then;
  try reflexivity.
  apply E_LLVM_Unfd with
    entry
    ([X = bop (ANum 1)])
    (br (BVal true),if_then,if_else)                           
    if_then
    (empty_state[X->1]);
  try reflexivity.
  apply E_LLVM_Ret with if_then ([Y = bop (ANum 2)]) ret;
  reflexivity.
Qed.