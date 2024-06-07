(** ST-LLVM COMPILER VERIFICATION: Structured Text *)


(** * Imports *)

Set Warnings "-notation-overridden,-parsing".
Require Import ZArith.
Require Import Coq.Strings.String.
Open Scope string_scope. 

From STLLVM Require Import Prelims.



(* ########################################################################### *)
(** * SYNTAX *)


(** * Statements *)

Inductive ST_stmnt : Type :=
  | ST_Cont   : ST_stmnt
  | ST_Exit   : ST_stmnt
  | ST_Ass    : id -> aExp -> ST_stmnt
  | ST_Seq    : ST_stmnt -> ST_stmnt -> ST_stmnt
  | ST_If     : bExp -> ST_stmnt -> ST_stmnt -> ST_stmnt
  | ST_While  : bExp -> ST_stmnt -> ST_stmnt
  | ST_Repeat : bExp -> ST_stmnt -> ST_stmnt.
  (* | ST_FCall  : id -> list argument -> ST_stmnt *)
Notation "'CONTINUE'" :=
  ST_Cont.
Notation "'EXIT'" :=
  ST_Exit.
Notation "x '::=' v" :=
  (ST_Ass x v) (at level 60).
Notation "stmnt1 ;; stmnt2" :=
  (ST_Seq stmnt1 stmnt2) (at level 80, right associativity).
Notation "'IF' b 'THEN' stmnt1 'ELSE' stmnt2 'END_IF'" :=
  (ST_If b stmnt1 stmnt2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' stmnt 'END_WHILE'" :=
  (ST_While b stmnt) (at level 80, right associativity).
Notation "'REPEAT' stmnt 'UNTIL' b 'END_REPEAT'" :=
  (ST_Repeat b stmnt) (at level 80, right associativity).
(*
Notation "'FOR' x '::=' a1 'TO' a2 'BY' a3 'DO' stmnt 'END_FOR'" :=
  (ST_For x a1 a2 a3 stmnt) (at level 80, right associativity).
*)



(** * Function Blocks *)

Definition fBlockEnvr       := map ST_stmnt.
Definition empty_fBlockEnvr := empty_map ST_Cont.

Inductive ST_fBlock : Type :=
  | ST_FBlock (name:id) (stmnt:ST_stmnt).
Notation "'FUNCTION_BLOCK' name ':=' stmnt 'END_FUNCTION_BLOCK'" :=
  (ST_FBlock name stmnt) (at level 100, name,stmnt at level 99).

Fixpoint registerFBlocksToEnvr (envr : fBlockEnvr) (decl : list ST_fBlock) :=
  match decl with
  | nil                            =>  envr
  | cons (ST_FBlock name stmnt) fs  =>  registerFBlocksToEnvr
                                       (envr[name -> stmnt]) fs
  end.

Inductive ST_pBlock : Type := 
  | ST_Program (name:id) (stmnt:ST_stmnt).
Notation "'PROGRAM' name ':=' stmnt 'END_PROGRAM'" :=
  (ST_Program name stmnt) (at level 100, name,stmnt at level 99).



(* ########################################################################### *)
(** * SEMANTICS *)


Inductive breakFlag : Type :=
  | NormFlag : breakFlag
  | ContFlag : breakFlag
  | ExitFlag : breakFlag.

Reserved Notation "e / < stmnt , st1 > 'ST=>'  flag , st2"
  (at level 40, st1, flag, stmnt at level 39).


(** * Statement Execution *)

Inductive ST_stmntExec :
  fBlockEnvr -> ST_stmnt -> state -> breakFlag -> state -> Prop :=

  (* Continue *)
  | E_ST_Cont : forall envr st,
      envr / <CONTINUE , st> ST=> ContFlag , st

  (* Exit *)
  | E_ST_Exit : forall envr st,
      envr / <EXIT , st> ST=> ExitFlag , st

  (* Assignment *)
  | E_ST_Asgn : forall envr st v n x,
      aEval st v = n -> 
      envr / <(x ::= v), st> ST=> NormFlag , (st[x->n])

  (* Sequence *)
  | E_ST_SeqNorm : forall envr st1 st2 st3 stmnt1 stmnt2 flag,
      envr / < stmnt1             , st1 >  ST=>  NormFlag , st2  ->
      envr / < stmnt2             , st2 >  ST=>  flag     , st3  ->
      envr / < (stmnt1 ;; stmnt2) , st1 >  ST=>  flag     , st3
  | E_ST_SeqCont : forall envr st1 st2 stmnt1 stmnt2,
      envr / < stmnt1             , st1 >  ST=>  ContFlag , st2  ->
      envr / < (stmnt1 ;; stmnt2) , st1 >  ST=>  ContFlag , st2
  | E_ST_SeqExit : forall envr st1 st2 stmnt1 stmnt2,
      envr / < stmnt1             , st1 >  ST=>  ExitFlag , st2  ->
      envr / < (stmnt1 ;; stmnt2) , st1 >  ST=>  ExitFlag , st2

  (* If *)
  | E_ST_IfTrue : forall envr st1 st2 b stmnt1 stmnt2 flag,
      bEval st1 b = true ->
      envr / < stmnt1                  , st1 >  ST=>  flag , st2 ->
      envr / < (ST_If b stmnt1 stmnt2) , st1 >  ST=>  flag , st2
  | E_ST_IfFalse : forall envr st1 st2 b stmnt1 stmnt2 flag,
      bEval st1 b = false ->
      envr / < stmnt2                  , st1 >  ST=>  flag , st2 ->
      envr / < (ST_If b stmnt1 stmnt2) , st1 >  ST=>  flag , st2

  (* While *)
  | E_ST_WhileFalse: forall envr st b stmnt,
      bEval st b = false ->
      envr / < (ST_While b stmnt) , st >  ST=>  NormFlag , st
  | E_ST_WhileTrueNorm : forall envr st1 st2 st3 b stmnt,
      bEval st1 b = true ->
      envr / < stmnt              , st1 >  ST=>  NormFlag , st2  ->
      envr / < (ST_While b stmnt) , st2 >  ST=>  NormFlag , st3  ->
      envr / < (ST_While b stmnt) , st1 >  ST=>  NormFlag , st3
  | E_ST_WhileTrueCont : forall envr st1 st2 st3 b stmnt,
      bEval st1 b = true ->
      envr / < stmnt              , st1 >  ST=>  ContFlag , st2  ->
      envr / < (ST_While b stmnt) , st2 >  ST=>  NormFlag , st3  ->
      envr / < (ST_While b stmnt) , st1 >  ST=>  NormFlag , st3
  | E_ST_WhileTrueExit : forall envr st1 st2 b stmnt,
      bEval st1 b = true ->
      envr / < stmnt              , st1 >  ST=>  ExitFlag , st2  ->
      envr / < (ST_While b stmnt) , st1 >  ST=>  NormFlag , st2
  
  (* Repeat *)
  | E_ST_RepeatTrue: forall envr st1 st2 b stmnt flag,
      envr / < stmnt               , st1 >  ST=>  flag     , st2  ->
      bEval st2 b = true ->
      envr / < (ST_Repeat b stmnt) , st1 >  ST=>  NormFlag , st2
  | E_ST_RepeatFalseNorm : forall envr st1 st2 st3 b stmnt,
      envr / < stmnt               , st1 >  ST=>  NormFlag , st2  ->
      bEval st2 b = false ->
      envr / < (ST_Repeat b stmnt) , st2 >  ST=>  NormFlag , st3  ->
      envr / < (ST_Repeat b stmnt) , st1 >  ST=>  NormFlag , st3
  | E_ST_RepeatFalseCont : forall envr st1 st2 st3 b stmnt,
      envr / < stmnt               , st1 >  ST=>  ContFlag , st2  ->
      bEval st2 b = false ->
      envr / < (ST_Repeat b stmnt) , st2 >  ST=>  NormFlag , st3  ->
      envr / < (ST_Repeat b stmnt) , st1 >  ST=>  NormFlag , st3
  | E_ST_RepeatFalseExit : forall envr st1 st2 b stmnt,
      envr / < stmnt               , st1 >  ST=>  ExitFlag , st2  ->
      bEval st2 b = false ->
      envr / < (ST_Repeat b stmnt) , st1 >  ST=>  NormFlag , st2

  (* For *)
  (*  FOR x := v1 TO v2 BY v3 DO stmnt END_FOR 
      ~ 
      x := v1 ; WHILE x <= v2 DO (c ; x += v3) END_WHILE *)
  (*
  | E_ST_For : forall envr st1 st2 st3 x v1 v2 v3 stmnt,
      envr / < (x ::= v1) , st1 > ST=> NormFlag , st2 ->
      envr / < (ST_While (BLe (AId x) v2)
                         (c ;; (x ::= APlus (AId x) v3))) ,
               st2 >
             ST=> NormFlag , st3 ->
      envr / < (ST_For x v1 v2 v3 stmnt) , st1 > ST=> NormFlag , st3
  *)

  (* Function Call *)
  (*
  | E_ST_FCall : forall envr name args stmnt st1 st2 st3,
      envr name = stmnt ->
      applyFuncArgs st1 args = st2 ->
      envr / < stmnt                    , st2 >  ST=>  NormFlag , st3 ->
      envr / < (ST_FCall name args) , st1 >  ST=>  NormFlag , st3
  *)
  
  where "e / < stmnt , st1 > 'ST=>' flag , st2" :=
    (ST_stmntExec e stmnt st1 flag st2).

Fixpoint returnsFlag (st : state) (stmnt : ST_stmnt) : breakFlag :=
  match stmnt with
  | CONTINUE                  =>  ContFlag
  | EXIT                      =>  ExitFlag
  | stmnt1;;stmnt2            =>  let flag := (returnsFlag st stmnt1) in
                                  match flag with 
                                  | NormFlag  =>  returnsFlag st stmnt2 (*!!!*)
                                  | _         =>  flag 
                                  end
  | ST_If bexp stmnt1 stmnt2  =>  let b := (bEval st bexp) in 
                                  match b with
                                  | true  =>  returnsFlag st stmnt1
                                  | false =>  returnsFlag st stmnt2
                                  end
  | _                         =>  NormFlag
  end.


(** * Function Block Evaluation *)

Reserved Notation "envr // < f , st1 > 'ST=>' st2"
  (at level 40, f,st1 at level 39).

Inductive ST_fBlockExec : fBlockEnvr -> ST_fBlock -> state -> state -> Prop := 
  | E_ST_FuncBlock : forall envr name stmnt st1 st2,
      (exists flag, envr /  <stmnt, st1> ST=> flag, st2) ->
      envr // <(ST_FBlock name stmnt), st1> ST=> st2
  where "envr // < f , st1 > ST=> st2" :=
    (ST_fBlockExec envr f st1 st2).


(** * Program Evaluation *)

(*
Inductive ST_prgmEval : list ST_fBlock-> ST_fBlock -> state -> state -> Prop := 
  | E_ST_Program : forall envr decl name stmnt st1 st2,
      registerFBlocksToEnvr empty_fBlockEnvr decl = envr ->
      envr /  < stmnt                   , st1 > ST=> NormFlag , st2 ->
      decl // < (ST_Program name stmnt) , st1 > ST=> st2
  where "decl // < p , st1 > ST=> st2" :=
    (ST_prgmEval decl p st1 st2).
*)


(* ########################################################################### *)
(** * EXAMPLES *)

Example ex_E_ST_If: 
  empty_fBlockEnvr /
  <
    X ::= ANum 1 ;;
    IF BLe (AId X) (ANum 2)
      THEN Y ::= ANum 3
      ELSE Y ::= ANum 4
    END_IF
    ,
    empty_state
  >
  ST=>
  NormFlag , (empty_state [X->1] [Y->3]).
Proof.
  apply E_ST_SeqNorm with (empty_state[X->1]).
  - apply E_ST_Asgn. reflexivity.
  - apply E_ST_IfTrue. reflexivity.
    + apply E_ST_Asgn. reflexivity.
Qed.

Example ex_E_ST_While:
  empty_fBlockEnvr /
  <
    X ::= ANum 0;;
    WHILE BLe (AId X) (ANum 0) DO
      X ::= APlus (AId X) (ANum 1)
    END_WHILE
    ,
    empty_state
  >
  ST=>
  NormFlag , (empty_state [X->0] [X->1]).
Proof.
  apply E_ST_SeqNorm with (empty_state [X->0]).
  - apply E_ST_Asgn. reflexivity.
  - apply E_ST_WhileTrueNorm with (empty_state [X->0] [X->1]).
    + reflexivity.
    + apply E_ST_Asgn. reflexivity.
    + apply E_ST_WhileFalse. reflexivity.
Qed.

Example ex_E_ST_Repeat:
  empty_fBlockEnvr /
  <
    X ::= ANum 0;;
    REPEAT
      X ::= APlus (AId X) (ANum 1)
    UNTIL (BEq (AId X) (ANum 2))
    END_REPEAT
    ,
    empty_state
  >
  ST=>
  NormFlag , (empty_state [X->0][X->1][X->2]).
Proof.
  apply E_ST_SeqNorm with (empty_state [X->0]).
  - apply E_ST_Asgn. reflexivity.
  - apply E_ST_RepeatFalseNorm with (empty_state [X->0][X->1]).
    + apply E_ST_Asgn. reflexivity.
    + reflexivity.
    + apply E_ST_RepeatTrue with NormFlag.
      * apply E_ST_Asgn. reflexivity.
      * reflexivity.
Qed.

Example ex_E_ST_Cont:
  empty_fBlockEnvr /
  <
    X ::= ANum 0;;
    WHILE BLe (AId X) (ANum 0) DO
      X ::= (ANum 1);;
      CONTINUE;;
      X ::= (ANum 1337)
    END_WHILE
    ,
    empty_state
  >
  ST=>
  NormFlag , (empty_state [X->0][X->1]).
Proof.
  apply E_ST_SeqNorm with (empty_state [X->0]).
  - apply E_ST_Asgn. reflexivity.
  - apply E_ST_WhileTrueCont with (empty_state [X->0][X->1]).
    + reflexivity.
    + apply E_ST_SeqNorm with (empty_state [X->0][X->1]).
      * apply E_ST_Asgn. reflexivity.
      * apply E_ST_SeqCont. apply E_ST_Cont.
    + apply E_ST_WhileFalse. reflexivity.
Qed.

Example ex_E_ST_Exit:
  empty_fBlockEnvr /
  <
    X ::= ANum 0;;
    WHILE BLe (AId X) (ANum 1337) DO
      EXIT;;
      X ::= (ANum 1)
    END_WHILE
    ,
    empty_state
  >
  ST=>
  NormFlag , (empty_state [X->0]).
Proof.
  apply E_ST_SeqNorm with (empty_state [X->0]).
  - apply E_ST_Asgn. reflexivity.
  - apply E_ST_WhileTrueExit.
    + reflexivity.
    + apply E_ST_SeqExit. apply E_ST_Exit.
Qed.

Example ex_E_ST_Function:
  empty_fBlockEnvr //
  <
    FUNCTION_BLOCK f :=
      X ::= ANum 1
    END_FUNCTION_BLOCK
    ,
    empty_state
  >
  ST=>
  (empty_state[X->1]).
Proof.
  apply E_ST_FuncBlock.
  exists NormFlag.
  apply E_ST_Asgn.
  reflexivity.
Qed. 