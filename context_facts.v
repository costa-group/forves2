Require Import List.
Import ListNotations.
Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.
 
Require Import FORVES2.octagon.
Import Octagon.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.symbolic_state_eval.
Import SymbolicStateEval.

Require Import FORVES2.stack_operation_instructions.
Import StackOpInstrs.


Require Import FORVES2.symbolic_execution_soundness.
Import SymbolicExecutionSoundness.

Module ContextFacts.


  Lemma chk_eq_wrt_ctx_snd:
    forall ctx sv1 sv2,
      chk_eq_wrt_ctx ctx sv1 sv2 = true ->
      forall model mem strg exts maxidx sb ops,
        is_model (ctx_cs ctx) model = true ->
        exists v,
          eval_sstack_val sv1 model mem strg exts maxidx sb ops = Some v /\
            eval_sstack_val sv2 model mem strg exts maxidx sb ops = Some v.
  Proof.
    intros ctx sv1 sv2 H_chkr model mem strg exts maxidx sb ops H_is_model.
    destruct ctx as [cs [chkr H_chkr_snd]].
    simpl in H_is_model.
    
    destruct sv1 as [val1 | var1 | fvar1 ] eqn:E_sv1;
      destruct sv2 as [val2 | var2 | fvar2 ] eqn:E_sv2;
      try discriminate.

    (* val1 = val2 *)
    + unfold chk_eq_wrt_ctx in H_chkr.
      unfold sstack_val_to_cliteral in H_chkr.
      simpl in H_chkr.
      pose proof (H_chkr_snd cs (C_EQ (C_VAL (wordToN val1)) (C_VAL (wordToN val2))) H_chkr) as H_chkr_snd.
      unfold is_model in H_is_model.
      unfold imply in H_chkr_snd.
      pose proof (H_chkr_snd model H_is_model) as H_chkr_snd.
      unfold satisfies_single_constraint in H_chkr_snd.
      unfold cliteral_to_nat in H_chkr_snd.

      pose proof (eval_sstack_val_Val val1 model mem strg exts maxidx sb ops) as H_eval_val1. 
      pose proof (eval_sstack_val_Val val2 model mem strg exts maxidx sb ops) as H_eval_val2.


      rewrite N.eqb_eq in H_chkr_snd.
      apply wordToN_inj in H_chkr_snd.
      
      rewrite H_eval_val1.
      rewrite H_eval_val2.

      exists val1.
      rewrite H_chkr_snd.

      split; try reflexivity.

    (* val = var *)
    + unfold chk_eq_wrt_ctx in H_chkr.
      unfold sstack_val_to_cliteral in H_chkr.
      simpl in H_chkr.
      pose proof (H_chkr_snd cs (C_EQ (C_VAL (wordToN val1)) (C_VAR var2)) H_chkr) as H_chkr_snd.
      unfold is_model in H_is_model.
      unfold imply in H_chkr_snd.
      
      pose proof (H_chkr_snd model H_is_model) as H_chkr_snd.
      unfold satisfies_single_constraint in H_chkr_snd.
      unfold cliteral_to_nat in H_chkr_snd.

      pose proof (eval_sstack_val_Val val1 model mem strg exts maxidx sb ops) as H_eval_val1. 
      pose proof (eval_sstack_val_InVar var2 model mem strg exts maxidx sb ops) as H_eval_var2.

      rewrite N.eqb_eq in H_chkr_snd.
      apply wordToN_inj in H_chkr_snd.
      
      rewrite H_eval_val1.
      rewrite H_eval_var2.

      exists val1.
      rewrite H_chkr_snd.

      split; try reflexivity.

    (* var = val *)
    + unfold chk_eq_wrt_ctx in H_chkr.
      unfold sstack_val_to_cliteral in H_chkr.
      simpl in H_chkr.
      pose proof (H_chkr_snd cs (C_EQ (C_VAR var1) (C_VAL (wordToN val2))) H_chkr) as H_chkr_snd.
      unfold is_model in H_is_model.
      unfold imply in H_chkr_snd.
      
      pose proof (H_chkr_snd model H_is_model) as H_chkr_snd.
      unfold satisfies_single_constraint in H_chkr_snd.
      unfold cliteral_to_nat in H_chkr_snd.

      pose proof (eval_sstack_val_InVar var1 model mem strg exts maxidx sb ops) as H_eval_var1. 
      pose proof (eval_sstack_val_Val val2 model mem strg exts maxidx sb ops) as H_eval_val2.

      rewrite N.eqb_eq in H_chkr_snd.
      apply wordToN_inj in H_chkr_snd.
      
      rewrite H_eval_var1.
      rewrite H_eval_val2.

      exists val2.
      rewrite H_chkr_snd.

      split; try reflexivity.

    (* var = var *)
    + unfold chk_eq_wrt_ctx in H_chkr.
      unfold sstack_val_to_cliteral in H_chkr.
      simpl in H_chkr.
      pose proof (H_chkr_snd cs (C_EQ (C_VAR var1) (C_VAR var2)) H_chkr) as H_chkr_snd.
      unfold is_model in H_is_model.
      unfold imply in H_chkr_snd.
      
      pose proof (H_chkr_snd model H_is_model) as H_chkr_snd.
      unfold satisfies_single_constraint in H_chkr_snd.
      unfold cliteral_to_nat in H_chkr_snd.

      pose proof (eval_sstack_val_InVar var1 model mem strg exts maxidx sb ops) as H_eval_var1. 
      pose proof (eval_sstack_val_InVar var2 model mem strg exts maxidx sb ops) as H_eval_var2.

      rewrite N.eqb_eq in H_chkr_snd.
      apply wordToN_inj in H_chkr_snd.
      
      rewrite H_eval_var1.
      rewrite H_eval_var2.

      exists (model var1).
      rewrite H_chkr_snd.

      split; try reflexivity.
Qed.



    
  Lemma chk_lt_wrt_ctx_snd:
    forall ctx sv1 sv2,
      chk_lt_wrt_ctx ctx sv1 sv2 = true ->
      forall model mem strg exts maxidx sb ops,
        is_model (ctx_cs ctx) model = true ->
        exists v1 v2,
          eval_sstack_val sv1 model mem strg exts maxidx sb ops = Some v1 /\
            eval_sstack_val sv2 model mem strg exts maxidx sb ops = Some v2 /\
            wlt v1 v2.
    intros ctx sv1 sv2 H_chkr model mem strg exts maxidx sb ops H_is_model.
    destruct ctx as [cs [chkr H_chkr_snd]].
    simpl in H_is_model.
    
    destruct sv1 as [val1 | var1 | fvar1 ] eqn:E_sv1;
      destruct sv2 as [val2 | var2 | fvar2 ] eqn:E_sv2;
      try discriminate.

    (* val1 = val2 *)
    + unfold chk_lt_wrt_ctx in H_chkr.
      unfold sstack_val_to_cliteral in H_chkr.
      simpl in H_chkr.
      pose proof (H_chkr_snd cs (C_LT (C_VAL (wordToN val1)) (C_VAL (wordToN val2))) H_chkr) as H_chkr_snd.
      unfold is_model in H_is_model.
      unfold imply in H_chkr_snd.
      pose proof (H_chkr_snd model H_is_model) as H_chkr_snd.
      unfold satisfies_single_constraint in H_chkr_snd.
      unfold cliteral_to_nat in H_chkr_snd.

      pose proof (eval_sstack_val_Val val1 model mem strg exts maxidx sb ops) as H_eval_val1. 
      pose proof (eval_sstack_val_Val val2 model mem strg exts maxidx sb ops) as H_eval_val2.


      rewrite N.ltb_lt in H_chkr_snd.
      
      rewrite H_eval_val1.
      rewrite H_eval_val2.

      exists val1.
      exists val2.
      repeat split; try reflexivity.

      apply lt_wlt.

      apply Nlt_out in H_chkr_snd.

      repeat rewrite wordToN_to_nat in H_chkr_snd.
      apply H_chkr_snd.

    (* val = var *)
    + unfold chk_lt_wrt_ctx in H_chkr.
      unfold sstack_val_to_cliteral in H_chkr.
      simpl in H_chkr.
      pose proof (H_chkr_snd cs (C_LT (C_VAL (wordToN val1)) (C_VAR var2)) H_chkr) as H_chkr_snd.
      unfold is_model in H_is_model.
      unfold imply in H_chkr_snd.
      pose proof (H_chkr_snd model H_is_model) as H_chkr_snd.
      unfold satisfies_single_constraint in H_chkr_snd.
      unfold cliteral_to_nat in H_chkr_snd.

      pose proof (eval_sstack_val_Val val1 model mem strg exts maxidx sb ops) as H_eval_val1. 
      pose proof (eval_sstack_val_InVar var2 model mem strg exts maxidx sb ops) as H_eval_var2.


      rewrite N.ltb_lt in H_chkr_snd.
      
      rewrite H_eval_val1.
      rewrite H_eval_var2.

      exists val1.
      exists (model var2).
      repeat split; try reflexivity.

      apply lt_wlt.

      apply Nlt_out in H_chkr_snd.

      repeat rewrite wordToN_to_nat in H_chkr_snd.
      apply H_chkr_snd.
      
    (* var = val *)
    + unfold chk_lt_wrt_ctx in H_chkr.
      unfold sstack_val_to_cliteral in H_chkr.
      simpl in H_chkr.
      pose proof (H_chkr_snd cs (C_LT (C_VAR var1) (C_VAL (wordToN val2))) H_chkr) as H_chkr_snd.
      unfold is_model in H_is_model.
      unfold imply in H_chkr_snd.
      pose proof (H_chkr_snd model H_is_model) as H_chkr_snd.
      unfold satisfies_single_constraint in H_chkr_snd.
      unfold cliteral_to_nat in H_chkr_snd.

      pose proof (eval_sstack_val_InVar var1 model mem strg exts maxidx sb ops) as H_eval_var1.
      pose proof (eval_sstack_val_Val val2 model mem strg exts maxidx sb ops) as H_eval_val2. 


      rewrite N.ltb_lt in H_chkr_snd.
      
      rewrite H_eval_var1.
      rewrite H_eval_val2.

      exists (model var1).
      exists val2.
      repeat split; try reflexivity.

      apply lt_wlt.

      apply Nlt_out in H_chkr_snd.

      repeat rewrite wordToN_to_nat in H_chkr_snd.
      apply H_chkr_snd.

    (* var = var *)
    + unfold chk_lt_wrt_ctx in H_chkr.
      unfold sstack_val_to_cliteral in H_chkr.
      simpl in H_chkr.
      pose proof (H_chkr_snd cs (C_LT (C_VAR var1) (C_VAR var2)) H_chkr) as H_chkr_snd.
      unfold is_model in H_is_model.
      unfold imply in H_chkr_snd.
      pose proof (H_chkr_snd model H_is_model) as H_chkr_snd.
      unfold satisfies_single_constraint in H_chkr_snd.
      unfold cliteral_to_nat in H_chkr_snd.

      pose proof (eval_sstack_val_InVar var1 model mem strg exts maxidx sb ops) as H_eval_var1.
      pose proof (eval_sstack_val_InVar var2 model mem strg exts maxidx sb ops) as H_eval_var2. 


      rewrite N.ltb_lt in H_chkr_snd.
      
      rewrite H_eval_var1.
      rewrite H_eval_var2.

      exists (model var1).
      exists (model var2).
      repeat split; try reflexivity.

      apply lt_wlt.

      apply Nlt_out in H_chkr_snd.

      repeat rewrite wordToN_to_nat in H_chkr_snd.
      apply H_chkr_snd.
Qed.

  Lemma chk_newq_wrt_ctx_snd:
    forall ctx sv1 sv2,
      chk_neq_wrt_ctx ctx sv1 sv2 = true ->
      forall model mem strg exts maxidx sb ops,
        is_model (ctx_cs ctx) model = true ->
        exists v1 v2,
          eval_sstack_val sv1 model mem strg exts maxidx sb ops = Some v1 /\
            eval_sstack_val sv2 model mem strg exts maxidx sb ops = Some v2 /\
            weqb v1 v2 = false.
  Proof.
    intros ctx sv1 sv2 H_imp_chkr model mem strg exts maxidx sb ops H_is_model.
    unfold chk_neq_wrt_ctx in H_imp_chkr.
    apply Bool.orb_true_iff in H_imp_chkr.
    destruct H_imp_chkr as [H_imp_chkr | H_imp_chkr].
    + pose proof (chk_lt_wrt_ctx_snd ctx sv1 sv2 H_imp_chkr model mem strg exts maxidx sb ops H_is_model) as H_chk_lt_wrt_ctx_snd.
      destruct H_chk_lt_wrt_ctx_snd as [v1' [v2' [ H_eval_sv1 [H_eval_sv2 H_wlt_v1'_v2']]]].
      exists v1'.
      exists v2'.
      rewrite H_eval_sv1.
      rewrite H_eval_sv2.
      repeat split; try reflexivity.
      apply weqb_ne.
      intuition.
      rewrite H in H_wlt_v1'_v2'.
      unfold wlt in H_wlt_v1'_v2'.
      intuition.
    + pose proof (chk_lt_wrt_ctx_snd ctx sv2 sv1 H_imp_chkr model mem strg exts maxidx sb ops H_is_model) as H_chk_lt_wrt_ctx_snd.
      destruct H_chk_lt_wrt_ctx_snd as [v2' [v1' [ H_eval_sv2 [H_eval_sv1 H_wlt_v2'_v1']]]].
      exists v1'.
      exists v2'.
      rewrite H_eval_sv1.
      rewrite H_eval_sv2.
      repeat split; try reflexivity.
      apply weqb_ne.
      intuition.
      rewrite H in H_wlt_v2'_v1'.
      unfold wlt in H_wlt_v2'_v1'.
      intuition.
Qed.
  
End ContextFacts.
