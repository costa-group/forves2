Require Import List.
Import ListNotations.
Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.
 
Require Import FORVES2.octagon.
Import Octagon.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.symbolic_state_eval.
Import SymbolicStateEval.



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
    Admitted.
End ContextFacts.
