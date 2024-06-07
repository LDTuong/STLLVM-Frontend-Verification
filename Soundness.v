(** ST-LLVM COMPILER VERIFICATION: Soundness of Translation*)


(** * Imports *)

Set Warnings "-notation-overridden,-parsing".
Require Import ZArith.
Require Import Coq.Strings.String.
Open Scope string_scope. 

From STLLVM Require Import Prelims.
From STLLVM Require Import ST.
From STLLVM Require Import LLVM.
From STLLVM Require Import Translation.



(* ########################################################################### *)
(** * PRELIMINARIES *)


(** * Auxiliary Definitions *)

Ltac invert H    := inversion H; subst.
Ltac backtrack H := invert H; try reflexivity.

Lemma specifyFlag: forall fbEnvr st1 st2 stmnt flag,
  flag = returnsFlag st1 stmnt ->
  (exists f, fbEnvr / < stmnt, st1 > ST=> f, st2) ->
  fbEnvr / < stmnt, st1 > ST=> flag, st2.
Proof. Admitted.


(** * Soundness of Translation *)

Definition exec_impl
  (fBody : list LLVM_bBlock) (stmnt : ST_stmnt) :=
  forall fEnvr fbEnvr st1 st2 bID,
    fEnvr * fBodyToBEnvr fBody / <entry, st1> LLVM=> <bID, st2> ->
    (exists flag, fbEnvr / <stmnt, st1> ST=> flag, st2).  

Definition execF_impl
  (f_llvm : LLVM_function) (f_st : ST_fBlock) :=
  forall st1 st2,
    empty_funcEnvr   // < f_llvm, st1 > LLVM=> st2 ->
    empty_fBlockEnvr // < f_st  , st1 > ST=>   st2.

Definition snd_tl (stmnt : ST_stmnt) :=
  exec_impl (T [stmnt]) stmnt.



(* ########################################################################### *)
(** * CONGRUENCE OF TRANSLATION SOUNDNESS *)


(* Sequence *)

Lemma snd_cngr_seq: forall stmnt1 stmnt2,
  snd_tl stmnt1 ->
  snd_tl stmnt2 ->
  snd_tl (stmnt1;;stmnt2).
Proof.
  intros stmnt1 stmnt2 cngr1 cngr2 fEnvr fbEnvr st1 st2 bID H.

  (* Case distinction on breakFlag when executing stmnt1 *)
  remember (returnsFlag st1 stmnt1) as flag.
  destruct flag.

  - (* flag = NormFlag *)
    destruct tl_embed_seq_norm with fEnvr stmnt1 stmnt2 bID st1 st2
    as [bID' embed].
    destruct embed as [st' embed]. destruct embed.
    rewrite Heqflag. reflexivity.
    destruct H1. apply H.
    pose proof (cngr1 fEnvr fbEnvr st1 st' bID' H1).
    destruct cngr2 with fEnvr fbEnvr st' st2 bID. apply H2.
    eexists.
    apply E_ST_SeqNorm with st'.
    + pose proof (specifyFlag fbEnvr st1 st' stmnt1 NormFlag Heqflag H3).
      apply H5.
    + apply H4.

  - (* flag = ContFlag *)
    destruct tl_embed_seq_cont with fEnvr stmnt1 stmnt2 bID st1 st2.
    rewrite Heqflag. reflexivity.
    pose proof (H1 H).
    pose proof (cngr1 fEnvr fbEnvr st1 st2 bID H2).
    eexists.
    apply E_ST_SeqCont.
    pose proof (specifyFlag fbEnvr st1 st2 stmnt1 ContFlag Heqflag H3).
    apply H4.

  - (* flag = ExitFlag *)
    destruct tl_embed_seq_exit with fEnvr stmnt1 stmnt2 bID st1 st2.
    rewrite Heqflag. reflexivity.
    pose proof (H1 H).
    pose proof (cngr1 fEnvr fbEnvr st1 st2 bID H2).
    eexists.
    apply E_ST_SeqExit.
    pose proof (specifyFlag fbEnvr st1 st2 stmnt1 ExitFlag Heqflag H3).
    apply H4.
Qed.


(* If *)

Lemma snd_cngr_if: forall b stmnt1 stmnt2,
  snd_tl stmnt1 ->
  snd_tl stmnt2 ->
  snd_tl (ST_If b stmnt1 stmnt2).
Proof.
  intros bexp stmnt1 stmnt2 cngr1 cngr2 fEnvr fbEnvr st1 st2 bID H.

  (* Case distinction on evaluation of bexp *)
  remember (bEval st1 bexp) as b.
  destruct b.

  - (* b = true *)
    apply tl_embed_if_t in H.
    + destruct cngr1 with fEnvr fbEnvr st1 st2 bID. apply H.
      eexists. apply E_ST_IfTrue.
      * rewrite Heqb. reflexivity.
      * apply H0.
    + rewrite Heqb. reflexivity.

  - (* b = false *)
    apply tl_embed_if_f in H.
    + destruct cngr2 with fEnvr fbEnvr st1 st2 bID. apply H.
      eexists. apply E_ST_IfFalse.
      * rewrite Heqb. reflexivity.
      * apply H0.
    + rewrite Heqb. reflexivity.
Qed.


(* While *)

Lemma snd_cngr_wh: forall b stmnt,
  snd_tl stmnt ->
  snd_tl (ST_While b stmnt).
Proof.
  intros bexp stmnt cngr fEnvr fbEnvr st1 st2 bID H.
  unfold snd_tl, exec_impl in cngr.
  replace bID with wh_end in H.
  destruct tl_embed_wh with fEnvr bexp stmnt st1 st2.
  Admitted.
  (**
  - apply tl_embed_wh_entry.
  - remember (bEval st1 bexp) as b.
    destruct b.
    + apply tl_embed_wh_t with (st2:=st2).
      * apply tl_embed_wh_iter with wh_end.
        destruct cngr with fEnvr fbEnvr st1 st2 wh_end. apply H.
  subst.
    apply IHl.
    
  - admit.
  - admit.
  -
  remember (ST_While b stmnt) as stmnt_wh.
  induction H; inversion Heqstmnt_wh.
  - apply wh_t_ex with st2. 
  Admitted.*)


(* Repeat *)

Lemma snd_cngr_rp: forall b stmnt,
  snd_tl stmnt ->
  snd_tl (ST_Repeat b stmnt).
Proof.
  intros b stmnt cngr st1 st2 b_fin H.
  Admitted.  



(* ########################################################################### *)
(** * PROOF OF SOUNDNESS *)

(** * Soundness of Statement Translation *)

Theorem transl_snd_stmnt: forall (stmnt : ST_stmnt),
  exec_impl (T [stmnt]) stmnt.
Proof.

  (* Proof: By structural induction over statements in ST. *)
  intros; induction stmnt.

  (** * Base Cases *)
  
  - (* Continue *)
    exists ContFlag.
    replace st2 with st1.
    apply E_ST_Cont.
    invert H. invert H0. invert H2.
    backtrack H0.

  - (* Exit *)
    exists ExitFlag.
    replace st2 with st1.
    apply E_ST_Exit.
    invert H. invert H0. invert H2.
    backtrack H0.

  - (* Assignment *)
    exists NormFlag.
    replace st2 with (st1[i -> (aEval st1 a)]).
    apply E_ST_Asgn; reflexivity.
    invert H. invert H0. invert H2.
    backtrack H0.

  (** * Induction Steps *)

  - (* Sequence *)
    apply snd_cngr_seq; assumption.
  - (* If *)
    apply snd_cngr_if; assumption.
  - (* While*)
    apply snd_cngr_wh; assumption.
  - (* Repeat *)
    apply snd_cngr_rp; assumption.

Qed.


(* Soundness of Function Block Translation *)

Theorem transl_snd_fb: forall (fb:ST_fBlock),
  execF_impl (translateFuncBlock fb) fb.
Proof. Admitted.



(* ########################################################################### *)
(** * MINOR PROOFS *)


(** * Assignent *)

Definition ex_Ass :=
  FUNCTION_BLOCK foo :=
    X ::= ANum 0
  END_FUNCTION_BLOCK.
Example ex_transl_sound_ass:
  execF_impl (translateFuncBlock ex_Ass) ex_Ass.
Proof.
  intros st1 st2 H.

  (* Handle ST eval *)
  replace st2 with (st1[X -> 0]).
  apply E_ST_FuncBlock; exists NormFlag.
  apply E_ST_Asgn.
  reflexivity.

  (* Handle LLVM eval *)
  invert H.   (* Unfold function *)
  invert H1.  (* Unfold entry block *)
  invert H2.  (* Fetch entry block body *)
  invert H4.  (* exfalso *)
  backtrack H2.
Qed.


(** * Sequence *)

Definition ex_Seq :=
  FUNCTION_BLOCK foo :=
    X ::= ANum 1;;
    Y ::= ANum 2;;
    Z ::= ANum 3
  END_FUNCTION_BLOCK.  
Example ex_transl_sound_seq:
  execF_impl (translateFuncBlock ex_Seq) ex_Seq.
Proof.
  intros st1 st2 H.

  (* Handle ST eval *)
  replace st2 with (st1[X->1][Y->2][Z->3]).
  apply E_ST_FuncBlock; exists NormFlag.
  apply E_ST_SeqNorm with (st1[X->1]).
  apply E_ST_Asgn. reflexivity.
  apply E_ST_SeqNorm with (st1[X->1][Y->2]).
  apply E_ST_Asgn. reflexivity.
  apply E_ST_Asgn. reflexivity.

  (* Handle LLVM eval *)
  invert H.
  invert H1.
  invert H2.
  invert H4.
  backtrack H2.
Qed.


(** * If *)

Definition ex_If :=
  FUNCTION_BLOCK foo :=
    X ::= ANum 1 ;;
    IF BLe (AId X) (ANum 2)
      THEN Y ::= ANum 3
      ELSE Z ::= ANum 4
    END_IF
  END_FUNCTION_BLOCK. 

Example ex_transl_sound_if:
  execF_impl (translateFuncBlock ex_If) ex_If.
Proof. 
  (* Handle ST eval *)
  intros st1 st2 H.
  replace st2 with (st1[X->1][Y->3]).
  apply E_ST_FuncBlock; exists NormFlag.
  apply E_ST_SeqNorm with (st1[X->1]).
  apply E_ST_Asgn. reflexivity.
  apply E_ST_IfTrue. reflexivity.
  apply E_ST_Asgn. reflexivity. 
  
  (* Handle LLVM eval *)

  (* Unfold branching *)
  invert H.   (* Unfold function *)
  invert H1.  (* Unfold entry block *)
  invert H2.  
  invert H6.  (* Unfold if_then block *)
  invert H3.
  invert H9.  (* Unfold if_merge block *)
  invert H5.
  invert H10. (* exfalso *)

  (* Backtrack evaluation *)
  backtrack H5.
  backtrack H3.
  backtrack H2.
  backtrack H4.
Qed.


(** * Assignent *)

Definition ex_While :=
  FUNCTION_BLOCK foo :=
    X ::= ANum 0;;
    WHILE BLe (AId X) (ANum 0) DO
      X ::= APlus (AId X) (ANum 1)
    END_WHILE
  END_FUNCTION_BLOCK.
Example ex_transl_sound_while:
  execF_impl (translateFuncBlock ex_While) ex_While.
Proof. 
  intros st1 st2 H.

  (* Handle ST eval *)
  replace st2 with (st1[X->0][X->1]).
  apply E_ST_FuncBlock; exists NormFlag.
  apply E_ST_SeqNorm with (st1[X->0]).
  apply E_ST_Asgn. reflexivity.
  apply E_ST_WhileTrueNorm with (st1[X->0][X->1]). reflexivity.
  apply E_ST_Asgn. reflexivity.
  apply E_ST_WhileFalse; reflexivity.
  
  (* Handle LLVM eval *)

  (* Unfold branching *)
  invert H.   (* Unfold function *)
  invert H1.  (* Unfold entry block *)
  invert H2.  
  invert H6.  (* Unfold while_head block *)
  invert H3.
  invert H9.  (* Unfold while_body block *)
  invert H5.
  invert H12. (* Unfold while_head block again *)
  invert H8.
  invert H15. (* Unfold while_end block *)
  invert H11.
  invert H16. (* exfalso *)

  (* Backtrack evaluation *)
  backtrack H11. 
  backtrack H8.
  backtrack H5.
  backtrack H3.
  backtrack H7.
  backtrack H2.
  backtrack H4.
Qed.

Definition ex_Repeat :=
  FUNCTION_BLOCK foo :=
    X ::= ANum 0;;
    REPEAT
      X ::= APlus (AId X) (ANum 1)
    UNTIL (BEq (AId X) (ANum 2))
    END_REPEAT
  END_FUNCTION_BLOCK.
Example ex_transl_sound_repeat:
  execF_impl (translateFuncBlock ex_Repeat) ex_Repeat.
Proof.
  intros st1 st2 H.
  replace st2 with (st1[X->0][X->1][X->2]).

  - (* Handle ST eval *)
    apply E_ST_FuncBlock; exists NormFlag.
    apply E_ST_SeqNorm with (st1[X->0]).
    apply E_ST_Asgn. reflexivity.
    apply E_ST_RepeatFalseNorm with (st1[X->0][X->1]).
    apply E_ST_Asgn. reflexivity.
    reflexivity.
    apply E_ST_RepeatTrue with NormFlag.
    + apply E_ST_Asgn. reflexivity.
    + reflexivity.

  - (* Handle LLVM eval *)
    invert H. (* Unfold function *)
    invert H1.
      (* Unfold entry block *)
      invert H2.
      invert H6.
      invert H3.
        (* Unfold repeat_head block *)
        invert H9.
        invert H5.
        invert H12.
          (* Unfold repeat_end block *)
          invert H8.
          invert H13. (* ret = true *) 
          backtrack H8.
        backtrack H5.
      backtrack H3.
      backtrack H7.
      backtrack H2.
      backtrack H4.
Qed.

Definition ex_Cont :=
  FUNCTION_BLOCK foo :=
    X ::= ANum 0;;
    WHILE BLe (AId X) (ANum 0) DO
      X ::= (ANum 1);;
      CONTINUE;;
      X ::= (ANum 1337)
    END_WHILE
  END_FUNCTION_BLOCK.  
Example ex_transl_sound_cont:
  execF_impl (translateFuncBlock ex_Cont) ex_Cont.
Proof.
  intros st1 st2 H.
  replace st2 with (st1[X->0][X->1]).

  - (* Handle ST eval *)
    apply E_ST_FuncBlock; exists NormFlag.
    apply E_ST_SeqNorm with (st1[X->0]).
    apply E_ST_Asgn. reflexivity.
    apply E_ST_WhileTrueCont with (st1[X->0][X->1]). reflexivity.
    apply E_ST_SeqNorm with (st1[X->0][X->1]).
    apply E_ST_Asgn. reflexivity.
    apply E_ST_SeqCont. apply E_ST_Cont.
    apply E_ST_WhileFalse. reflexivity.

  - (* Handle LLVM eval *)
    invert H.

    (* Unfold entry block *)
    invert H1. {
      invert H2.
      (* Unfold while_head block *)
      invert H6. {
        invert H3.
        (* Unfold while_body block *)
        invert H9. {
          invert H5.
          (* Unfold while_head block *)
          invert H12. {
            invert H8.
            (* Unfold while_end block *)
            invert H15. {
              invert H11.
              (* ret is the magic word *)
              invert H16.
            }            
            backtrack H11; reflexivity.
          }     
          backtrack H8; reflexivity.
        }
        backtrack H5; reflexivity.
      }
      backtrack H3.
      backtrack H7.
    }
    
    backtrack H2.
    backtrack H4.

Qed.

Definition ex_Exit :=
  FUNCTION_BLOCK foo :=
    X ::= ANum 0;;
    WHILE BLe (AId X) (ANum 1337) DO
      EXIT;;
      X ::= (ANum 1)
    END_WHILE
  END_FUNCTION_BLOCK.  
Example ex_transl_sound_exit:
  execF_impl (translateFuncBlock ex_Exit) ex_Exit.
Proof.
  intros st1 st2 H.
  replace st2 with (st1[X->0]).

  (* Handle ST eval *)
  apply E_ST_FuncBlock; exists NormFlag.
  apply E_ST_SeqNorm with (st1[X->0]).
  apply E_ST_Asgn. reflexivity.
  apply E_ST_WhileTrueExit. reflexivity.
  apply E_ST_SeqExit.
  apply E_ST_Exit.

  (* Handle LLVM eval *)
  invert H.
  invert H1.
  invert H2.
    invert H6.
    invert H3.
      invert H9.
      invert H5.
        invert H12.
        invert H8.
          invert H13.
        backtrack H8.
      backtrack H5.
    backtrack H3.
  backtrack H2.
Qed.
