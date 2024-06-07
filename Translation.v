(** ST-LLVM COMPILER VERIFICATION: Translation *)


(* Imports *)

Set Warnings "-notation-overridden,-parsing".
Require Import ZArith.
Require Import Coq.Strings.String.
Open Scope string_scope. 

From STLLVM Require Import Prelims.
From STLLVM Require Import ST.
From STLLVM Require Import LLVM.



(* ########################################################################### *)
(** * TRANSLATION *)


(** * Auxiliary functions *)

Definition addInstr 
  (i:LLVM_instr) (body : list LLVM_bBlock) : list LLVM_bBlock :=
  match body with
  | nil => nil
  | cons parent bs =>
    match parent with
    | name: bBody,term => cons (name: (bBody ++ cons i nil),term) bs
    end
  end.

Definition setBr 
  (t : LLVM_brnch) (body : list LLVM_bBlock) : list LLVM_bBlock :=
  match body with
  | nil => nil
  | cons parent bs =>
    match parent with
    | name: bBody,term => cons (name: bBody,t) bs
    end
  end.

Definition getBlockName (b : LLVM_bBlock) : id :=
  match b with
  | name: body,term => name
  end.

Fixpoint reverse (l : list LLVM_bBlock) : list LLVM_bBlock :=
  match l with
  | nil       => nil
  | cons b bs => reverse bs ++ (cons b nil)
  end.


(** * Statement Translation *)

Definition if_then  := Id "if_then".
Definition if_else  := Id "if_else".
Definition if_merge := Id "if_merge".
Definition wh_head  := Id "while_head".
Definition wh_body  := Id "while_body".
Definition wh_end   := Id "while_end".
Definition rp_head  := Id "repeat_head".
Definition rp_end   := Id "repeat_end".

Inductive loopScope :=
  | scope (lHead lEnd:id).
Definition empty_scope := scope (Id "") (Id "").
Definition scope_is_empty (sc:loopScope) :=
  match sc with
  | scope h e => andb (eq_id h (Id "")) (eq_id e (Id ""))
  end.

Fixpoint translateStmnt 
  (sc:loopScope)    (* Current while/repeat header and end blocks *)
  (n:nat)           (* Number appended to block names for unique block names *)
  (flag:breakFlag)  (* Flag for handling CONTINUE/EXIT behavior *)
  (st:ST_stmnt)
  (body : list LLVM_bBlock) :
  (list LLVM_bBlock) * nat * breakFlag :=

  match sc, n, body with
  | (scope loopHead loopEnd), n, nil              => (body, n, NormFlag)
  | (scope loopHead loopEnd), n, (cons parent bs) =>

    match st with

    (* Continue *)
    | ST_Cont =>
      if    scope_is_empty sc
      then  (setBr ret body, n, ContFlag)
      else  (setBr (br (BVal true),loopHead,loopHead) body, n, ContFlag)

    (* Exit *)
    | ST_Exit =>
      if    scope_is_empty sc
      then  (setBr ret body, n, ExitFlag)
      else  (setBr (br (BVal true),loopEnd,loopEnd) body, n, ExitFlag)

    (* Assignment *)
    | ST_Ass x v =>
      (addInstr (x = bop v) body, n, flag)

    (* Sequence *)
    | ST_Seq c1 c2 =>
      let '(b,m,f) := translateStmnt sc n flag c1 body in
      match f with
      | NormFlag  =>  translateStmnt sc m f c2 b                  
      | _         =>  (b, m, f)
      end

    (* If *)
    | ST_If b c1 c2 =>  

      (* Fresh block names *)
      let m1   := S n in
      let if_t := concat if_then  (nat_to_id m1) in
      let if_f := concat if_else  (nat_to_id m1) in
      let if_m := concat if_merge (nat_to_id m1) in

      (* Create new blocks *)
      let body_h  := setBr (br b,if_t,if_f) body in
      let block_t := if_t:  nil, ret in
      let block_f := if_f:  nil, ret in
      let block_m := if_m: nil, ret in

      (* Compute subgraph for then-case *)
      let '(graph_t, m2, flag_t) :=
        translateStmnt sc m1 flag c1 (cons block_t body_h) in
      let body_t := 
        match flag_t with
        | NormFlag => setBr (br (BVal true), if_m, if_m) graph_t
        | _        => graph_t
        end in

      (* Compute subgraph for else-case *)
      let '(graph_f, m3, flag_f) :=
        translateStmnt sc m2 flag c2 (cons block_f body_t) in
      let body_f :=
        match flag_f with
        | NormFlag => setBr (br (BVal true), if_m, if_m) graph_f
        | _        => graph_f
        end in

      (cons block_m body_f, m3, NormFlag)  

    (* While *)
    | ST_While b c =>
      
      (* Fresh block names *)
      let m1   := S n in
      let wh_h := concat wh_head (nat_to_id m1) in
      let wh_t := concat wh_body (nat_to_id m1) in
      let wh_f := concat wh_end  (nat_to_id m1) in

      (* Create new blocks *)
      let block_h  := wh_h:  nil, br b,wh_t,wh_f in
      let block_t  := wh_t:  nil, ret in
      let block_f  := wh_f:  nil, ret in
      let body_h := 
        cons block_h (setBr (br (BVal true),wh_h,wh_h) body) in

      (* Update current loop scope *)
      let newScope := scope wh_h wh_f in

      (* Creat subgraph for while-body *)
      let '(graph, m2, flag_t) :=
        translateStmnt newScope m1 flag c (cons block_t body_h) in
      let body_t := 
        match flag_t with
        | NormFlag => setBr (br (BVal true),wh_h,wh_h) graph
        | _        => graph
        end in

      (cons block_f body_t, m2, NormFlag)

    (* Repeat *)
    | ST_Repeat b c =>

      (* Fresh block names *)
      let m1   := S n in
      let rp_f := concat rp_head (nat_to_id m1) in
      let rp_t := concat rp_end  (nat_to_id m1) in

      (* Update current loop scope *)
      let newScope := scope rp_f rp_t in

      (* Create new blocks *)
      let body_h  := setBr (br (BVal true),rp_f,rp_f) body in
      let block_f := rp_f: nil, ret in
      let block_t := rp_t: nil, ret in

      (* Creat subgraph for repeat-body *)
      let '(graph, m2, flag_t) :=
        translateStmnt newScope m1 flag c (cons block_f body_h) in
      let body_f :=
        match flag_t with
        | NormFlag => setBr (br b,rp_t,rp_f) graph
        | _        => graph
        end in

      (cons block_t body_f, m2, NormFlag)
    
    (* For *)
    (* | ST_For x v1 v2 v3 c => body *)

    (* Function Call *)
    (* | ST_FCall f args => body *)

    end
  end.


(** * Function Block Translation *)

Definition translateStmntToFuncBody (stmnt : ST_stmnt) : (list LLVM_bBlock) :=
  let '(res,n,flag) := 
    translateStmnt empty_scope 0%nat NormFlag stmnt ([entry: nil,ret])
  in reverse res.
Notation "'T' [ stmnt ]" := (translateStmntToFuncBody stmnt).
  
Definition translateFuncBlock (fb : ST_fBlock) : LLVM_function :=
  match fb with
  | ST_FBlock name stmnt => 
      define name := (translateStmntToFuncBody stmnt)
  end.
Notation "'T_f' [ fb ]" := (translateFuncBlock fb).



(* ########################################################################### *)
(** * EMBEDDING SUB-TRANSLATIONS *)

(** TODO: Justify these properties by how the translation CFG is constructed. *)


(* Sequence *)

Axiom tl_embed_seq_norm: 
  forall fEnvr stmnt1 stmnt2 bID st1 st3, exists bID' st2,
  returnsFlag st1 stmnt1 = NormFlag ->
  (fEnvr * fBodyToBEnvr T[stmnt1] / <entry, st1> LLVM=> <bID', st2> /\
  fEnvr * fBodyToBEnvr T[stmnt2] / <entry, st2> LLVM=> <bID, st3> <->
  fEnvr * fBodyToBEnvr T[stmnt1;;stmnt2] / <entry, st1> LLVM=> <bID, st3>).

Axiom tl_embed_seq_cont: 
  forall fEnvr stmnt1 stmnt2 bID st1 st2,
  returnsFlag st1 stmnt1 = ContFlag ->
  (fEnvr * fBodyToBEnvr T[stmnt1] / <entry, st1> LLVM=> <bID, st2> <->
  fEnvr * fBodyToBEnvr T[stmnt1;;stmnt2] / <entry, st1> LLVM=> <bID, st2>).

Axiom tl_embed_seq_exit: 
  forall fEnvr stmnt1 stmnt2 bID st1 st2,
  returnsFlag st1 stmnt1 = ExitFlag ->
  (fEnvr * fBodyToBEnvr T[stmnt1] / <entry, st1> LLVM=> <bID, st2> <->
  fEnvr * fBodyToBEnvr T[stmnt1;;stmnt2] / <entry, st1> LLVM=> <bID, st2>).


(* If *)

Axiom tl_embed_if_t: forall fEnvr b stmnt1 stmnt2 bID st1 st2,
  bEval st1 b = true ->
  (fEnvr * fBodyToBEnvr T[stmnt1] / <entry , st1> LLVM=> <bID, st2> <->
  fEnvr * fBodyToBEnvr T[ST_If b stmnt1 stmnt2] /
  <entry, st1> LLVM=> <bID, st2>).

Axiom tl_embed_if_f: forall fEnvr b stmnt1 stmnt2 bID st1 st2,
  bEval st1 b = false ->
  (fEnvr * fBodyToBEnvr T[stmnt2] / <entry , st1> LLVM=> <bID, st2> <->
  fEnvr * fBodyToBEnvr T[ST_If b stmnt1 stmnt2] /
  <entry, st1> LLVM=> <bID, st2>).


(* While*)

Reserved Notation "fEnvr * bEnvr / < curr , st1 > 'WH=>' < next , st2 >"
  (at level 40, bEnvr,curr,next,st1,st2 at level 39).

Inductive whileChain : 
  funcEnvr -> blockEnvr -> id -> state -> id -> state -> Prop :=

  | tl_embed_wh_f : forall fEnvr b stmnt st,
      fEnvr * fBodyToBEnvr T[ST_While b stmnt] /
      <wh_head, st> WH=> <wh_end, st>

  | tl_embed_wh_t: forall fEnvr b stmnt st1 st2 st3,
      fEnvr * fBodyToBEnvr T[stmnt] / <wh_head, st1> WH=> <wh_head, st2> ->
      fEnvr * fBodyToBEnvr T[ST_While b stmnt] /
      <wh_head, st2> WH=> <wh_end, st3> ->
      fEnvr * fBodyToBEnvr T[ST_While b stmnt] /
      <wh_head, st1> WH=> <wh_end, st3>
  
  where "fEnvr * bEnvr / < bID1 , st1 > 'WH=>' < bID2 , st2 >" := 
    (whileChain fEnvr bEnvr bID1 st1 bID2 st2).

Axiom tl_embed_wh_entry: forall fEnvr b stmnt st,
  fEnvr * fBodyToBEnvr T[ST_While b stmnt] / <entry, st> LLVM=> <wh_head, st>.
  
Axiom tl_embed_wh_iter: forall fEnvr stmnt bID st1 st2,
  fEnvr * fBodyToBEnvr T[stmnt] / <entry  , st1> LLVM=> <bID    , st2> ->
  fEnvr * fBodyToBEnvr T[stmnt] / <wh_head, st1> WH=>   <wh_head, st2>.

Axiom tl_embed_wh: forall fEnvr b stmnt st1 st2,
  (fEnvr*fBodyToBEnvr T[ST_While b stmnt] / <entry  , st1> LLVM=> <wh_head, st1> /\
  fEnvr*fBodyToBEnvr T[ST_While b stmnt] / <wh_head, st1> WH=>   <wh_end , st2>) ->
  fEnvr*fBodyToBEnvr T[ST_While b stmnt] / <entry  , st1> LLVM=> <wh_end , st2>.


(* Repeat *)

Axiom tl_embed_rp_iter: forall fEnvr stmnt bID st1 st2,
  fEnvr * fBodyToBEnvr T[stmnt] / <entry  , st1> LLVM=> <bID    , st2> ->
  fEnvr * fBodyToBEnvr T[stmnt] / <rp_head, st1> LLVM=> <rp_head, st2>.

Axiom tl_embed_rp_t: forall fEnvr b stmnt st1 st2,
  bEval st1 b = true ->
  fEnvr * fBodyToBEnvr T[stmnt] / <rp_head, st1> LLVM=> <rp_head, st2> ->
  fEnvr * fBodyToBEnvr T[ST_Repeat b stmnt] / <rp_head, st1> LLVM=> <rp_end, st2>.

Axiom tl_embed_rp_f: forall fEnvr b stmnt st1 st2 st3,
  bEval st1 b = false ->
  fEnvr * fBodyToBEnvr T[stmnt] / <rp_head, st1> LLVM=> <rp_head, st2> ->
  fEnvr * fBodyToBEnvr T[ST_Repeat b stmnt] /
  <rp_head, st2> LLVM=> <rp_end, st3> ->
  fEnvr * fBodyToBEnvr T[ST_Repeat b stmnt] /
  <rp_head, st1> LLVM=> <rp_end, st3>.

Axiom tl_embed_rp_entry: forall fEnvr b stmnt st,
  fEnvr * fBodyToBEnvr T[ST_Repeat b stmnt] / <entry, st> LLVM=> <rp_head, st>.

Axiom tl_embed_rp: forall fEnvr b stmnt st1 st2,
  fEnvr * fBodyToBEnvr T[ST_Repeat b stmnt] /
  <entry, st1> LLVM=> <rp_head, st1> ->
  fEnvr * fBodyToBEnvr T[ST_Repeat b stmnt] /
  <rp_head, st1> LLVM=> <rp_end, st2> ->
  fEnvr * fBodyToBEnvr T[ST_Repeat b stmnt] /
  <entry, st1> LLVM=> <rp_end, st2>.



(* ########################################################################### *)
(** * EXAMPLES *)

Example ex_TL_If:
  T_f [ FUNCTION_BLOCK foo :=
        IF BVal true THEN
          X ::= ANum 1
        ELSE
          Y ::= ANum 2
        END_IF
      END_FUNCTION_BLOCK ]
  =
  define foo := [
    Id "entry" :
    nil,
    br BVal true, Id "if_then1", Id "if_else1";

    Id "if_then1" :
    [Id "X" = bop ANum 1],
    br BVal true, Id "if_merge1", Id "if_merge1";

    Id "if_else1" :
    [Id "Y" = bop ANum 2],
    br BVal true, Id "if_merge1", Id "if_merge1";

    Id "if_merge1" :
    nil, ret
  ].
Proof. reflexivity. Qed.

Example ex_TL_While:
  T_f [ FUNCTION_BLOCK foo :=
        X ::= ANum 0;;
        WHILE BLe (AId X) (ANum 0) DO
          X ::= APlus (AId X) (ANum 1)
        END_WHILE
      END_FUNCTION_BLOCK ]
  =
  define Id "foo" := [
    Id "entry" :
    [X = bop ANum 0],
    br BVal true, Id "while_head1", Id "while_head1";

    Id "while_head1" :
    nil,
    br BLe (AId (Id "X")) (ANum 0), Id "while_body1", Id "while_end1";

    Id "while_body1" : 
    [Id "X" = bop APlus (AId (Id "X")) (ANum 1)],
    br BVal true, Id "while_head1", Id "while_head1"; 
    
    Id "while_end1" :
    nil, ret
  ].
Proof. reflexivity. Qed.

Example ex_TL_Repeat:
  T_f [ FUNCTION_BLOCK foo :=
        X ::= (ANum 0);;
        REPEAT
          X ::= APlus (AId X) (ANum 1)
        UNTIL
          BLe (AId X) (ANum 2)
        END_REPEAT
      END_FUNCTION_BLOCK ]
  =
  define Id "foo" := [
    Id "entry" :
    [X = bop ANum 0],
    br BVal true, Id "repeat_head1", Id "repeat_head1";

    Id "repeat_head1" :
    [Id "X" = bop APlus (AId (Id "X")) (ANum 1)],
    br BLe (AId (Id "X")) (ANum 2), Id "repeat_end1", Id "repeat_head1";

    Id "repeat_end1" :
    nil, ret
  ].
Proof. reflexivity. Qed.

Example ex_TL_complete:
  T_f [ FUNCTION_BLOCK foo :=
        X ::= ANum 0;;
        WHILE BLe (AId X) (ANum 2) DO
          Y ::= ANum 0;;      
          REPEAT
            IF (BEq (ANum 1) (ANum 1)) THEN
              Y ::= APlus (AId Y) (ANum 1)
            ELSE
              EXIT;;
              Y ::= ANum 1234
            END_IF
          UNTIL 
            BEq (AId Y) (ANum 2)
          END_REPEAT;;
          X ::= APlus (AId X) (ANum 1);;
          CONTINUE;;
          Z ::= ANum 1337
        END_WHILE;;      
        Z ::= ANum 42;;
        Y ::= ANum 0
      END_FUNCTION_BLOCK ]
  =
  define Id "foo" := [
    Id "entry" :
    [Id "X" = bop ANum 0],
    br BVal true, Id "while_head1", Id "while_head1";

    Id "while_head1" :
    nil,
    br BLe (AId (Id "X")) (ANum 2), Id "while_body1", Id "while_end1";

    Id "while_body1" :
    [Id "Y" = bop ANum 0],
    br BVal true, Id "repeat_head2", Id "repeat_head2";

    Id "repeat_head2" :
    nil,
    br BEq (ANum 1) (ANum 1), Id "if_then3", Id "if_else3";

    Id "if_then3" :
    [Id "Y" = bop APlus (AId (Id "Y")) (ANum 1)],
    br BVal true, Id "if_merge3", Id "if_merge3";

    Id "if_else3" :
    nil,
    br BVal true, Id "repeat_end2", Id "repeat_end2";

    Id "if_merge3" :
    nil,
    br BEq (AId (Id "Y")) (ANum 2), Id "repeat_end2", Id "repeat_head2";

    Id "repeat_end2" :
    [Id "X" = bop APlus (AId (Id "X")) (ANum 1)],
    br BVal true, Id "while_head1", Id "while_head1";

    Id "while_end1" :
    [Id "Z" = bop ANum 42; Id "Y" = bop ANum 0],
    ret
  ].
Proof. reflexivity. Qed.