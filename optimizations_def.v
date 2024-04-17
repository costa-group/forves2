Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.
Require Import PeanoNat.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.symbolic_state_eval.
Import SymbolicStateEval.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.execution_state.
Import ExecutionState.

Require Import FORVES2.stack_operation_instructions.
Import StackOpInstrs.

Require Import FORVES2.program.
Import Program.

Require Import FORVES2.symbolic_state_cmp_impl.
Import SymbolicStateCmpImpl.

Require Import FORVES2.symbolic_state_eval_facts.
Import SymbolicStateEvalFacts.

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.misc.
Import Misc.

Require Import FORVES2.eval_common.
Import EvalCommon.

Require Import FORVES2.optimizations_common.
Import Optimizations_Common.

Require Import FORVES2.concrete_interpreter.
Import ConcreteInterpreter.

Require Import FORVES2.constraints.
Import Constraints.

Require Import List.
Import ListNotations.


Module Optimizations_Def.

Import Coq.Arith.EqNat.


(* Definitions *)

Definition optim := constraints -> sstate -> sstate*bool.

Definition optim_snd (opt: optim) : Prop :=
  forall (ctx: constraints) (sst: sstate) (sst': sstate) (b: bool),
    is_sat ctx ->
    valid_sstate sst evm_stack_opm ->
    opt ctx sst = (sst', b) ->
    (valid_sstate sst' evm_stack_opm /\
       (*get_instk_height_sst sst = get_instk_height_sst sst' /\*)
       forall (model: assignment) (mem: memory) (strg: storage) (exts: externals)
              (st': state),
         is_model ctx model = true ->
         eval_sstate sst model mem strg exts evm_stack_opm = Some st' ->
         eval_sstate sst' model mem strg exts evm_stack_opm = Some st').


(*
Definition optim_snd' (opt: optim) : Prop :=
  forall (ctx: constraints) (sst: sstate) (sst': sstate) (b: bool),
    is_sat ctx ->
    valid_sstate sst evm_stack_opm ->
    opt sst = (sst', b) ->
    (valid_sstate sst' evm_stack_opm /\
       get_instk_height_sst sst = get_instk_height_sst sst' /\
       forall (model mem strg exts: state),
         is_model ctx model ->
         exists st'
         eval_sstate sst model mem strg exts evm_stack_opm = Some st' /\
         eval_sstate sst' model mem strg exts evm_stack_opm = Some st').
*)


(* sb2 preserves all the successful evaluations of sstack_val in sb1 wrt. ctx *)
Definition preserv_sbindings (sb1 sb2: sbindings) (maxidx: nat) 
  (ops: stack_op_instr_map) (ctx: constraints): Prop :=
valid_bindings maxidx sb1 ops /\
valid_bindings maxidx sb2 ops /\
forall (sv : sstack_val) (model : assignment) (mem: memory) (strg: storage) 
  (ext: externals) (v: EVMWord),
  is_model ctx model = true ->
  eval_sstack_val sv model mem strg ext maxidx sb1 ops = Some v ->
  eval_sstack_val sv model mem strg ext maxidx sb2 ops = Some v.
  
(* Type of a function that optimizes a single smap_value *)
Definition opt_smap_value_type := 
  smap_value ->            (* val *)
  sstack_val_cmp_t ->      (* fcmp *) 
  sbindings ->             (* sb *)
  nat ->                   (* maxid *) 
  (*nat ->                   (* instk_height *)*)
  constraints ->           (* ctx *)
  stack_op_instr_map ->    (* ops *)
  smap_value*bool.         (* (val', flag) *)

Definition opt_smapv_valid_snd (opt: opt_smap_value_type) :=
forall (ctx: constraints) (maxidx: nat) (fcmp: sstack_val_cmp_t) (sb: sbindings) 
  (val val': smap_value) (flag: bool),
safe_sstack_val_cmp fcmp ->
is_sat ctx ->
valid_smap_value maxidx evm_stack_opm val ->
valid_bindings maxidx sb evm_stack_opm ->
opt val fcmp sb maxidx ctx evm_stack_opm = (val', flag) ->
valid_smap_value maxidx evm_stack_opm val'.

(* 'opt' is sound if optimizing the head in a valid bindings (idx,val)::sb 
   results in a valid bindings (idx,val')::sb that preserves evaluations *)
Definition opt_sbinding_snd (opt: opt_smap_value_type) :=
forall (val val': smap_value) (fcmp: sstack_val_cmp_t) (sb: sbindings) 
  (maxidx: nat) (ctx: constraints) (idx: nat) (flag: bool),
safe_sstack_val_cmp fcmp ->
valid_bindings maxidx ((idx,val)::sb) evm_stack_opm ->
is_sat ctx ->
opt val fcmp sb idx ctx evm_stack_opm = (val', flag) ->
  valid_bindings maxidx ((idx,val')::sb) evm_stack_opm /\
  forall model mem strg ext v,
    is_model ctx model = true ->
    eval_sstack_val (FreshVar idx) model mem strg ext maxidx ((idx,val)::sb) 
       evm_stack_opm = Some v -> 
    eval_sstack_val (FreshVar idx) model mem strg ext maxidx ((idx,val')::sb) 
       evm_stack_opm = Some v.

(* Applies smap value optimization to the first suitable entry in sbindings *)
Fixpoint optimize_first_sbindings (opt_sbinding: opt_smap_value_type) 
  (ctx: constraints) (fcmp: sstack_val_cmp_t) (sb: sbindings)
    : sbindings*bool :=
match sb with
| [] => (sb,false)
| (n,val)::rs => 
    match opt_sbinding val fcmp rs n ctx evm_stack_opm with
    | (val', true) => ((n,val')::rs, true)
    | (val', false) => 
        match (optimize_first_sbindings opt_sbinding ctx fcmp rs) with 
        | (rs', flag) => ((n,val)::rs', flag)
        end
    end
end.

Definition optimize_first_sstate (opt: opt_smap_value_type) 
  (fcmp: sstack_val_cmp_t) (ctx: constraints) (sst: sstate)
  : sstate*bool :=
match sst with 
| SymExState sstk smem sstg sctx (SymMap maxid bindings) =>
    match optimize_first_sbindings opt ctx fcmp bindings with
    | (bindings', flag) => 
        (SymExState sstk smem sstg sctx (SymMap maxid bindings'),
         flag)
    end
end.






(* Lemmas *)
 
(* sb2 preserves all the successful evaluations of sstack in sb1 wrt. ctx *)
Lemma preserv_sbindings_sstack: 
forall (sb1 sb2: sbindings) (maxidx: nat) (ops: stack_op_instr_map) 
  (ctx: constraints), 
preserv_sbindings sb1 sb2 maxidx ops ctx -> 
  forall (sstk: sstack) (stk: stack) (mem: memory) 
    (strg: storage) (model: assignment) (ext: externals),
  is_model ctx model = true ->
  eval_sstack sstk maxidx sb1 model mem strg ext ops = Some stk ->
  eval_sstack sstk maxidx sb2 model mem strg ext ops = Some stk.
Proof.
intros sb1 sb2 maxidx ops ctx Hpreserv sstk.
revert sb1 sb2 maxidx ops ctx Hpreserv.
induction sstk as [|sval r IH].
- intuition.
- intros sb1 sb2 maxid ops ctx Hpreserv 
    stk mem strg model ext Hismodel Heval.
  unfold preserv_sbindings in Hpreserv.
  unfold eval_sstack in Heval.
  unfold map_option in Heval.
  destruct (eval_sstack_val sval model mem strg ext maxid sb1 ops) as
    [v|] eqn: eq_eval_sval; try discriminate.
  rewrite <- map_option_ho in Heval.
  assert (Hpreserv_copy := Hpreserv).
  destruct Hpreserv as [Hvalid_sb1 [Hvalid_sb2 Hpreserv]].
  pose proof (Hpreserv sval model mem strg ext v Hismodel eq_eval_sval)
    as Heval_sval_sb2.
  rewrite <- eval_sstack_def in Heval.
  destruct (eval_sstack r maxid sb1 model mem strg ext ops) as [rs_val|]
    eqn: eq_eval_rs; try discriminate.
  apply IH with (sb2:=sb2)(ctx:=ctx) in eq_eval_rs as 
    Heval_r_sb2; try assumption.
  unfold eval_sstack.
  unfold map_option.
  rewrite -> Heval_sval_sb2.
  rewrite <- map_option_ho.
  rewrite <- eval_sstack_def.
  rewrite -> Heval_r_sb2.
  assumption.
Qed.


(* is_model can be removed as a premise if given *)
Lemma preserv_bindings_model: forall ctx model maxidx mem strg ext n sb1 sb2 ops,
(forall (sv : sstack_val) (v : EVMWord),
           is_model ctx model = true ->
           eval_sstack_val' maxidx sv model mem strg ext n sb1 ops = Some v ->
           eval_sstack_val' maxidx sv model mem strg ext n sb2 ops = Some v) ->
is_model ctx model = true  ->
(forall (sv : sstack_val) (v : EVMWord),
         eval_sstack_val' maxidx sv model mem strg ext n sb1 ops = Some v ->
         eval_sstack_val' maxidx sv model mem strg ext n sb2 ops = Some v).
Proof.
auto.
Qed.

(* is_model can be removed as a premise if given *)
Lemma preserv_bindings_model': forall ctx model mem strg ext n sb1 sb2 ops,
(forall (sv : sstack_val) (v : EVMWord),
           is_model ctx model = true ->
           eval_sstack_val sv model mem strg ext n sb1 ops = Some v ->
           eval_sstack_val sv model mem strg ext n sb2 ops = Some v) ->
is_model ctx model = true  ->
(forall (sv : sstack_val) (v : EVMWord),
         eval_sstack_val sv model mem strg ext n sb1 ops = Some v ->
         eval_sstack_val sv model mem strg ext n sb2 ops = Some v).
Proof.
auto.
Qed.

Lemma preserv_sbindings_ext: forall (sb1 sb2: sbindings)
  (maxidx: nat) (ops: stack_op_instr_map) (n: nat) (smapv: smap_value)
  (ctx: constraints),
maxidx = S n ->
valid_smap_value n ops smapv ->
preserv_sbindings sb1 sb2 n ops ctx ->
preserv_sbindings ((n,smapv)::sb1) ((n,smapv)::sb2) maxidx ops ctx.
Proof.
intros sb1 sb2 maxidx ops n smapv ctx Hmaxidx Hvalid Hpreserv.
unfold preserv_sbindings in Hpreserv.
destruct Hpreserv as [Hvalid_sb1 [Hvalid_sb2 Hpreserv]].
unfold preserv_sbindings.
split.
- simpl. intuition. 
- split. 
  + simpl. intuition.
  + unfold eval_sstack_val in Hpreserv. 
    unfold eval_sstack_val.
    intros sv model mem strg ext v Hismodel Heval.
    destruct sv as [val|var|fvar] eqn: eq_sv.
    * unfold eval_sstack_val. simpl.
      unfold eval_sstack_val in Heval. simpl in Heval.
      assumption.
    * unfold eval_sstack_val. simpl.
      unfold eval_sstack_val in Heval. simpl in Heval.
      assumption.
    * destruct (n =? fvar) eqn: eq_fvar_n.
      -- destruct smapv as [basicv|tagv|label args|offset smem|key sstrg|
           offset size smem] eqn: eq_smapv.
         ++ (* SymBasicVal basicv *)
            destruct basicv as [val'|var'|fvar'] eqn: eq_basicv.
            ** simpl in Heval. rewrite -> eq_fvar_n in Heval.
               simpl. rewrite -> eq_fvar_n. 
               assumption.
            ** simpl in Heval. rewrite -> eq_fvar_n in Heval.
               simpl. rewrite -> eq_fvar_n. 
               assumption.
            ** rewrite -> PeanoNat.Nat.eqb_eq in eq_fvar_n.
               rewrite -> eq_fvar_n in Heval.
               rewrite <- eval_sstack_val'_freshvar in Heval.
               rewrite -> eq_fvar_n.
               rewrite <- eval_sstack_val'_freshvar.
               pose proof (eval'_then_valid_sstack_value maxidx 
                 (FreshVar fvar') model mem strg ext maxidx sb1 ops v
                 n Heval Hvalid_sb1) as Hvalid_stk_val_fv.
               assert (S n > n) as maxidx_gt_nm; try intuition.
               pose proof (eval_sstack_val'_succ (S n)
                 (FreshVar fvar') model mem strg ext n sb1 ops
                 Hvalid_stk_val_fv Hvalid_sb1 maxidx_gt_nm) as eval'_fvar'.
               destruct eval'_fvar' as [v' eval'_fvar'].
               rewrite -> eval'_maxidx_indep_eq with (m:=n) in Heval.
               pose proof (eval_sstack_val'_preserved_when_depth_extended
                 (S n) n sb1 (FreshVar fvar') v' model mem strg ext ops
                 eval'_fvar') as eval'_fvar'_succ.
               rewrite <- Hmaxidx in eval'_fvar'_succ.
               rewrite -> Heval in eval'_fvar'_succ.
               injection eval'_fvar'_succ as eq_v'.
               rewrite <- eq_v' in eval'_fvar'.
               pose proof (Hpreserv (FreshVar fvar') model mem strg ext v Hismodel
                 eval'_fvar') as eval'_fvar'_sb2.
               rewrite -> Hmaxidx.
               apply eval_sstack_val'_preserved_when_depth_extended.
               rewrite -> eval'_maxidx_indep_eq with (m:=S n) in eval'_fvar'_sb2.
               assumption.
         ++ (* SymPUSHTAG tagv *)
            simpl in Heval. rewrite -> eq_fvar_n in Heval.
            simpl. rewrite -> eq_fvar_n.
            assumption.
         ++ (* SymOp label args *)
            rewrite <- Hmaxidx in Hpreserv.
            simpl in Heval. rewrite -> eq_fvar_n in Heval.
            simpl. rewrite -> eq_fvar_n.
            destruct (ops label) as [nargs f H_comm H_ctx_ind].
            destruct (length args =? nargs); try discriminate.
            destruct (map_option
              (fun sv' : sstack_val =>
                 eval_sstack_val' maxidx sv' model mem strg ext n sb1 ops) args)
              as [vargs|] eqn: Hmapo; try discriminate.
            rewrite <- Heval.
            specialize Hpreserv with (model:=model)(mem:=mem)(strg:=strg)(ext:=ext).
            pose proof (preserv_bindings_model ctx model maxidx mem strg ext n 
              sb1 sb2 ops Hpreserv Hismodel) as Hpreserv'.
            pose proof (map_option_sstack maxidx model mem strg ext n sb1 sb2 
              ops args vargs Hmapo Hpreserv') as eq_mapo'.
            rewrite -> eq_mapo'.
            reflexivity.
         ++ (* SymMLOAD offset smem *)
            rewrite <- Hmaxidx in Hpreserv.
            simpl in Heval. rewrite -> eq_fvar_n in Heval.
            simpl. rewrite -> eq_fvar_n.
            destruct (map_option (instantiate_memory_update
              (fun sv : sstack_val =>
                 eval_sstack_val' maxidx sv model mem strg ext n sb1 ops)) smem)
              as [mem_updates|] eqn: Hmapo; try discriminate.
            specialize Hpreserv with (model:=model)(mem:=mem)(strg:=strg)(ext:=ext).
            pose proof (preserv_bindings_model ctx model maxidx mem strg ext n 
              sb1 sb2 ops Hpreserv Hismodel) as Hpreserv'.
            pose proof (map_option_inst_mem_update maxidx model mem strg ext n 
              sb1 sb2 ops smem mem_updates Hmapo Hpreserv') as eq_mapo'.
            rewrite -> eq_mapo'.
            destruct (eval_sstack_val' maxidx offset model mem strg ext n sb1 ops)
              as [offsetv|] eqn: eq_eval_offset; try discriminate.
            pose proof (Hpreserv offset offsetv Hismodel eq_eval_offset) as eq_eval_offset'.
            rewrite ->  eq_eval_offset'.
            assumption.
         ++ (* SymSLOAD key sstrg *)
            rewrite <- Hmaxidx in Hpreserv.
            simpl in Heval. rewrite -> eq_fvar_n in Heval.
            simpl. rewrite -> eq_fvar_n.
            destruct (map_option (instantiate_storage_update
              (fun sv : sstack_val =>
                eval_sstack_val' maxidx sv model mem strg ext n sb1 ops)) sstrg)
              as [strg_updates|] eqn: Hmapo; try discriminate.
            specialize Hpreserv with (model:=model)(mem:=mem)(strg:=strg)(ext:=ext).
            pose proof (preserv_bindings_model ctx model maxidx mem strg ext n 
              sb1 sb2 ops Hpreserv Hismodel) as Hpreserv'.
            pose proof (map_option_inst_strg_update maxidx model mem strg ext n 
              sb1 sb2 ops sstrg strg_updates Hmapo Hpreserv') as eq_mapo'.
            rewrite -> eq_mapo'.
            destruct (eval_sstack_val' maxidx key model mem strg ext n sb1 ops)
              as [keyv|] eqn: eq_eval_key; try discriminate.
            pose proof (Hpreserv key keyv Hismodel eq_eval_key) as eq_eval_key'.
            rewrite ->  eq_eval_key'.
            assumption.
         ++ (* SymSHA3 offset size smem *)
            rewrite <- Hmaxidx in Hpreserv.
            simpl in Heval. rewrite -> eq_fvar_n in Heval.
            simpl. rewrite -> eq_fvar_n.
            destruct (map_option (instantiate_memory_update
              (fun sv : sstack_val =>
                eval_sstack_val' maxidx sv model mem strg ext n sb1 ops)) smem)
              as [mem_updates|] eqn: Hmapo; try discriminate.
            specialize Hpreserv with (model:=model)(mem:=mem)(strg:=strg)(ext:=ext).
            pose proof (preserv_bindings_model ctx model maxidx mem strg ext n 
              sb1 sb2 ops Hpreserv Hismodel) as Hpreserv'.
            pose proof (map_option_inst_mem_update maxidx model mem strg ext n 
              sb1 sb2 ops smem mem_updates Hmapo Hpreserv') as eq_mapo'.
            rewrite -> eq_mapo'.
            destruct (eval_sstack_val' maxidx offset model mem strg ext n sb1 ops)
              as [offsetv|] eqn: eq_eval_offset; try discriminate.
            pose proof (Hpreserv offset offsetv Hismodel eq_eval_offset) as eq_eval_offset'.
            rewrite ->  eq_eval_offset'.
            destruct (eval_sstack_val' maxidx size model mem strg ext n sb1 ops)
              as [sizev|] eqn: eq_eval_size; try discriminate.
            pose proof (Hpreserv size sizev Hismodel eq_eval_size) as eq_eval_size'.
            rewrite ->  eq_eval_size'.
            assumption.
      -- rewrite -> eval_sstack_val'_diff with (b:=n) in Heval; try assumption.
         rewrite -> eval_sstack_val'_diff with (b:=n); try assumption.
         pose proof (eval'_then_valid_sstack_value maxidx 
           (FreshVar fvar) model mem strg ext n sb1 ops v
           n Heval Hvalid_sb1) as Hvalid_stk_val_fv.
         assert (S n > n) as maxidx_gt_nm; try intuition.
         pose proof (eval_sstack_val'_succ (S n)
           (FreshVar fvar) model mem strg ext n sb1 ops
           Hvalid_stk_val_fv Hvalid_sb1 maxidx_gt_nm) as eval'_fvar.
         destruct eval'_fvar as [v' eval'_fvar].
         pose proof (eval_sstack_val'_preserved_when_depth_extended
           (S n) n sb1 (FreshVar fvar) v' model mem strg ext ops
           eval'_fvar) as eval'_fvar_succ.
         rewrite <- Hmaxidx in eval'_fvar_succ.
         rewrite -> Heval in eval'_fvar_succ.
         injection eval'_fvar_succ as eq_v'.
         rewrite <- eq_v' in eval'_fvar.
         pose proof (Hpreserv (FreshVar fvar) model mem strg ext v Hismodel
           eval'_fvar) as eval'_fvar_sb2.
         rewrite -> Hmaxidx.
         apply eval_sstack_val'_preserved_when_depth_extended.
         assumption.
Qed.


(* sb2 preserves all the successful evaluations of smem in sb1 *)  
Lemma preserv_sbindings_smemory:
forall (sb1 sb2: sbindings) (maxidx: nat) (ops: stack_op_instr_map) (ctx: constraints), 
preserv_sbindings sb1 sb2 maxidx ops ctx -> 
  forall (smem: smemory) (model: assignment) (mem mem': memory) 
    (strg: storage) (ext: externals),
  is_model ctx model = true ->
  eval_smemory smem maxidx sb1 model mem strg ext ops = Some mem' ->
  eval_smemory smem maxidx sb2 model mem strg ext ops = Some mem'.
Proof.
intros sb1 sb2 maxidx ops ctx Hpreserv smem model
  mem mem' strg ext Hismodel Heval_mem.
unfold eval_smemory. unfold eval_smemory in Heval_mem.
unfold eval_sstack_val in Hpreserv.
unfold eval_sstack_val in Heval_mem.
unfold eval_sstack_val.
destruct (map_option
                (instantiate_memory_update
                   (fun sv : sstack_val =>
                    eval_sstack_val' (S maxidx) sv model mem strg ext maxidx
                      sb1 ops)) smem) as [updates|] eqn: eq_mapo;
  try discriminate.
injection Heval_mem as eq_mem'.
rewrite <- eq_mem'.
destruct Hpreserv as [Hvalid_sb1 [Hvalid_sb2 Hpreserv]].
specialize Hpreserv with (model:=model)(mem:=mem)(strg:=strg)(ext:=ext).
pose proof (preserv_bindings_model' ctx model mem strg ext maxidx 
            sb1 sb2 ops Hpreserv Hismodel) as Hpreserv'.
unfold eval_sstack_val in Hpreserv'.
pose proof (map_option_inst_mem_update (S maxidx) model mem strg ext maxidx
  sb1 sb2 ops smem updates eq_mapo Hpreserv') as eq_mapo2.
rewrite -> eq_mapo2.
reflexivity.
Qed.


(* sb2 preserves all the successful evaluations of sstorage in sb1 *)
Lemma preserv_sbindings_sstorage:
forall (sb1 sb2: sbindings) (maxidx: nat)
  (ops: stack_op_instr_map) (ctx: constraints), 
preserv_sbindings sb1 sb2 maxidx ops ctx -> 
  forall (sstrg: sstorage) (model: assignment) (mem: memory) (strg strg': storage) (ext: externals),
  is_model ctx model = true ->
  eval_sstorage sstrg maxidx sb1 model mem strg ext ops = Some strg' ->
  eval_sstorage sstrg maxidx sb2 model mem strg ext ops = Some strg'.
Proof.
intros sb1 sb2 maxidx ops ctx Hpreserv sstrg model
  mem strg strg' ext Hismodel Heval_sstrg.
unfold eval_sstorage. unfold eval_sstorage in Heval_sstrg.
unfold eval_sstack_val in Hpreserv.
unfold eval_sstack_val in Heval_sstrg.
unfold eval_sstack_val.
destruct (map_option
                  (instantiate_storage_update
                     (fun sv : sstack_val =>
                      eval_sstack_val' (S maxidx) sv model mem strg ext
                        maxidx sb1 ops)) sstrg) as [updates|] eqn: eq_mapo;
  try discriminate.
injection Heval_sstrg as eq_strg'.
rewrite <- eq_strg'.
destruct Hpreserv as [Hvalid_sb1 [Hvalid_sb2 Hpreserv]].

specialize Hpreserv with (model:=model)(mem:=mem)(strg:=strg)(ext:=ext).
pose proof (preserv_bindings_model' ctx model mem strg ext maxidx 
            sb1 sb2 ops Hpreserv Hismodel) as Hpreserv'.
unfold eval_sstack_val in Hpreserv'.
pose proof (map_option_inst_strg_update (S maxidx) model mem strg ext maxidx
  sb1 sb2 ops sstrg updates eq_mapo Hpreserv') as eq_mapo2.
rewrite -> eq_mapo2.
reflexivity.
Qed.


(* Changing a preseving sbinding in a sstate preserves successful 
   evaluations *)
Lemma preserv_sbindings_sstate :
forall (sb1 sb2: sbindings) (maxidx: nat) (ops: stack_op_instr_map) 
  (ctx: constraints), 
preserv_sbindings sb1 sb2 maxidx ops ctx ->
valid_bindings maxidx sb1 ops -> 
valid_bindings maxidx sb2 ops -> 
  forall (model: assignment) (st': state) (sstk: sstack) (smem: smemory) 
  (sstrg: sstorage) (sexts : sexternals) (mem: memory) (strg: storage)
  (ext: externals),
    is_model ctx model = true -> 
    eval_sstate (SymExState sstk smem sstrg sexts  
      (SymMap maxidx sb1)) model mem strg ext ops = Some st' -> 
    eval_sstate (SymExState sstk smem sstrg sexts 
      (SymMap maxidx sb2)) model mem strg ext ops = Some st'.
Proof.
intros sb1 sb2 maxidx ops ctx Hpr_sbind Hvalid1 Hvalid2 model st'
  sstk smem sstrg sexts mem strg ext Hismodel Heval_sstate_sb1.
unfold eval_sstate in Heval_sstate_sb1.
simpl in Heval_sstate_sb1.
unfold eval_sstate. simpl.
destruct (eval_sstack sstk maxidx sb1 model mem strg ext ops) eqn: eq_eval_sstack; 
  try discriminate.
apply preserv_sbindings_sstack with (sb2:=sb2)(ctx:=ctx) in 
  eq_eval_sstack; try assumption.
rewrite -> eq_eval_sstack.
destruct (eval_smemory smem maxidx sb1 model mem strg ext ops) eqn: eq_eval_smemory;
  try discriminate.
apply preserv_sbindings_smemory with (sb2:=sb2)(ctx:=ctx) in 
  eq_eval_smemory; try assumption.
rewrite -> eq_eval_smemory.
destruct (eval_sstorage sstrg maxidx sb1 model mem strg ext ops) eqn: eq_eval_sstorage;
  try discriminate.
apply preserv_sbindings_sstorage with (sb2:=sb2)(ctx:=ctx) in 
  eq_eval_sstorage; try assumption.
rewrite -> eq_eval_sstorage.
intuition.
Qed.


(* Fixed to evm_stack_opm *)
Lemma valid_smap_value_opt_sbinding_snd: forall (opt: opt_smap_value_type) ctx 
  val fcmp sb idx val' flag maxidx,
opt val fcmp sb idx ctx evm_stack_opm = (val', flag) ->
is_sat ctx ->
opt_sbinding_snd opt ->
safe_sstack_val_cmp fcmp ->
valid_bindings maxidx ((idx, val) :: sb) evm_stack_opm ->
valid_smap_value idx evm_stack_opm val'.
Proof.
intros opt ctx val fcmp sb idx val' flag maxidx Hopt Hissat Hopt_snd 
  Hsafe_fcmp Hvalid.
unfold opt_sbinding_snd in Hopt_snd.
pose proof (Hopt_snd val val' fcmp sb maxidx ctx idx flag
  Hsafe_fcmp Hvalid Hissat Hopt) as Hopt'.
destruct Hopt' as [Hvalid' _].
unfold valid_bindings in Hvalid'.
destruct Hvalid' as [_ [Hvalid_smap _]].
assumption.
Qed.


(* Fixed to evm_stack_opm *)
Lemma optimize_first_valid: forall (opt: opt_smap_value_type) (ctx: constraints)
  (fcmp: sstack_val_cmp_t) (sb sb': sbindings) (maxid: nat) 
  (flag: bool),
safe_sstack_val_cmp fcmp ->
opt_sbinding_snd opt ->
valid_bindings maxid sb evm_stack_opm ->
is_sat ctx ->
optimize_first_sbindings opt ctx fcmp sb = (sb', flag) ->
valid_bindings maxid sb' evm_stack_opm.
Proof.
intros opt ctx fcmp sb. revert opt ctx fcmp.
induction sb as [| h rsb IH].
- intros opt ctx fcmp sb' maxid flag Hsafe_fcmp Hopt_snd Hvalid_sb
  Hissat Hoptimize_first.
  simpl in Hoptimize_first.
  injection Hoptimize_first as eq_sb' _.
  rewrite <- eq_sb'.
  intuition.
- intros opt ctx fcmp sb' maxid flag Hsafe_fcmp Hopt_snd Hvalid_sb
  Hissat Hoptimize_first.
  assert (Hvalid_sb_copy := Hvalid_sb).
  unfold valid_bindings in Hvalid_sb.
  destruct h as [idx value] eqn: eq_h.
  destruct Hvalid_sb as [Hmaxid [Hvalid_smap_value Hvalid_bindings_rsb]].
  fold valid_bindings in Hvalid_bindings_rsb.
  simpl in Hoptimize_first.
  destruct (opt value fcmp rsb idx ctx evm_stack_opm) as [val' b]
    eqn: eq_opt_value.
  destruct b eqn: eq_b.
  + injection Hoptimize_first as eq_sb' eq_flag.
    rewrite <- eq_sb'. simpl.
    split; try assumption.
    split.
    * unfold opt_sbinding_snd in Hopt_snd.
      pose proof (Hopt_snd value val' fcmp rsb maxid ctx idx true
      Hsafe_fcmp Hvalid_sb_copy Hissat eq_opt_value) as Hsnd_value.
      destruct Hsnd_value as [Hvalid_value _].
      unfold valid_bindings in Hvalid_value.
      intuition.
    * unfold opt_sbinding_snd in Hopt_snd.
      pose proof (Hopt_snd value val' fcmp rsb maxid ctx idx true
      Hsafe_fcmp Hvalid_sb_copy Hissat eq_opt_value) as Hsnd_value.
      destruct Hsnd_value as [Hvalid_value _].
      unfold valid_bindings in Hvalid_value.
      intuition.
  + destruct (optimize_first_sbindings opt ctx fcmp rsb) 
      as [rs' flag'] eqn: eq_optimize_rsb.
    injection Hoptimize_first as eq_sb' eq_flag.
    rewrite <- eq_sb'. simpl.
    split; try assumption.
    split; try assumption.
    apply IH with (opt:=opt)(fcmp:=fcmp)(flag:=flag')(ctx:=ctx); try assumption.
Qed.


(* If opt is sound when optimizing the first entry in the bindings, then 
   the optimize_first_sbindings will preserve the bindings *)
Lemma opt_sbinding_preserves: 
forall (opt: opt_smap_value_type) (fcmp: sstack_val_cmp_t) (sb sb': sbindings) 
  (maxid: nat) (ctx: constraints) (flag: bool),
safe_sstack_val_cmp fcmp ->
opt_sbinding_snd opt ->
valid_bindings maxid sb evm_stack_opm ->
is_sat ctx -> 
optimize_first_sbindings opt ctx fcmp sb = (sb', flag) ->
preserv_sbindings sb sb' maxid evm_stack_opm ctx.
Proof.
intros opt fcmp sb. revert opt fcmp.
induction sb as [|h rsb IH].
- intros opt fcmp sb' maxid ctx flag Hfcmp_snd Hopt_sbinding_snd 
    Hvalid Hissat Hoptimize_first_sbindings.
  simpl in Hoptimize_first_sbindings.
  injection Hoptimize_first_sbindings as eq_sb' _.
  rewrite <- eq_sb'.
  unfold preserv_sbindings. intuition.
- intros opt fcmp sb' maxid ctx flag Hfcmp_snd Hopt_sbinding_snd 
    Hvalid Hissat Hoptimize_first_sbindings.
  destruct h as [n smapv] eqn: eq_h.
  assert (Hoptimize_first_sbindings_copy := Hoptimize_first_sbindings).
  assert (Hvalid_copy := Hvalid).
  unfold optimize_first_sbindings in Hoptimize_first_sbindings.
  destruct (opt smapv fcmp rsb n ctx evm_stack_opm) as [val' b] 
    eqn: eq_opt_val.
  unfold preserv_sbindings.
  split; try assumption.
  split.
  * (* valid_bindings instk_height maxid sb' evm_stack_opm *)
    apply optimize_first_valid with (opt:=opt)(fcmp:=fcmp)
      (sb:=h::rsb)(flag:=flag)(ctx:=ctx); try intuition.
    + rewrite -> eq_h. assumption.
    + rewrite -> eq_h. assumption.
  * destruct b eqn: eq_b.
    + (* Optimized first entry in sbindings *)
      injection Hoptimize_first_sbindings as eq_sb' eq_flag'.
      rewrite <- eq_sb'.
      unfold preserv_sbindings.
      
      intros sv model mem strg ext v Hlen Heval_sb.
      unfold opt_sbinding_snd in Hopt_sbinding_snd.
      destruct sv as [val|var|fvar] eqn: eq_sv; try intuition.
      unfold eval_sstack_val in Heval_sb.
      destruct (n =? fvar) eqn: eq_n_fvar.
      -- apply Nat.eqb_eq in eq_n_fvar.
         rewrite <- eq_n_fvar in Heval_sb.
         unfold eval_sstack_val in Hopt_sbinding_snd.
         pose proof (Hopt_sbinding_snd smapv val' fcmp rsb maxid ctx 
           n true Hfcmp_snd Hvalid Hissat eq_opt_val) as Hopt_sbinding_snd'.
         destruct Hopt_sbinding_snd' as [_ Hpreserv_ext].
         pose proof (Hpreserv_ext model mem strg ext v Hlen Heval_sb).
         unfold eval_sstack_val. rewrite <- eq_n_fvar.
         assumption.
      -- unfold eval_sstack_val. 
         rewrite -> eval_sstack_val'_diff with (b:=maxid); try assumption.
         rewrite -> eval_sstack_val'_diff with (b:=maxid) in Heval_sb; 
           try assumption.
   + (* Optimized the tail of the sbindings *)
      fold optimize_first_sbindings in Hoptimize_first_sbindings.
      destruct (optimize_first_sbindings opt ctx fcmp rsb) as
        [rs' flag'] eqn: eq_optimize_first_rs.
      injection Hoptimize_first_sbindings as eq_sb' eq_flag.
      rewrite <- eq_sb'.
      unfold valid_bindings in Hvalid.
      destruct Hvalid as [eq_maxid_n [Hvalid_smap Hvalid_rsb]].
      fold valid_bindings in Hvalid_rsb.
      pose proof (IH opt fcmp rs' n ctx flag' Hfcmp_snd
        Hopt_sbinding_snd Hvalid_rsb Hissat eq_optimize_first_rs) 
        as Hpreserv_rs.
      apply preserv_sbindings_ext; try intuition.
Qed.


(* Fixed to evm_stack_opm *)
Lemma optimize_first_sstate_valid: forall (opt: opt_smap_value_type) 
  (fcmp: sstack_val_cmp_t) (sst sst': sstate) (ctx: constraints)
  (flag: bool),
valid_sstate sst evm_stack_opm ->
opt_sbinding_snd opt ->
safe_sstack_val_cmp fcmp ->
is_sat ctx ->
optimize_first_sstate opt fcmp ctx sst = (sst', flag) ->
valid_sstate sst' evm_stack_opm.
Proof.
intros opt fcmp sst sst' ctx flag Hvalid Hopt Hsafe_cmp Hissat Hopt_first.
unfold valid_sstate in Hvalid.
destruct sst. destruct sm. simpl in Hvalid.
destruct Hvalid as [Hvalid_smap [Hvalid_sstack [Hvalid_smemory Hvalid_sstorage]]].
unfold optimize_first_sstate in Hopt_first.
destruct (optimize_first_sbindings opt ctx fcmp bindings) as
  [bindings' flag'] eqn: eq_optim_first.
injection Hopt_first as eq_sst' eq_flag'.
rewrite <- eq_sst'.
unfold valid_sstate. simpl.
split.
- unfold valid_smap in Hvalid_smap.
  pose proof (optimize_first_valid opt ctx fcmp bindings bindings' maxid 
    flag' Hsafe_cmp Hopt Hvalid_smap Hissat eq_optim_first).
  assumption.
- split; try split; try assumption.
Qed.

Lemma optimize_first_sstate_preserv: forall (opt: opt_smap_value_type) 
  (fcmp: sstack_val_cmp_t) (sst sst': sstate) (ctx: constraints) 
  (flag: bool),
valid_sstate sst evm_stack_opm ->
opt_sbinding_snd opt ->
safe_sstack_val_cmp fcmp ->
is_sat ctx ->
optimize_first_sstate opt fcmp ctx sst = (sst', flag) ->
 (*get_instk_height_sst sst = get_instk_height_sst sst' /\*)
 forall (model : assignment) (mem : memory) (strg : storage) 
     (exts : externals) (st': state), 
   is_model ctx model = true ->
   eval_sstate sst  model mem strg exts evm_stack_opm = Some st' ->
   eval_sstate sst' model mem strg exts evm_stack_opm = Some st'.
Proof.
intros opt fcmp sst sst' ctx flag Hvalid Hopt Hsafe_cmp Hissat Hopt_first.
destruct sst. destruct sm. 
unfold optimize_first_sstate in Hopt_first.
destruct (optimize_first_sbindings opt ctx fcmp bindings)
  as [bindings' flag'] eqn: eq_optim_first.
injection Hopt_first as eq_sst' eq_flag.
rewrite <- eq_sst'. simpl.
intros model mem strg exts st' Hismodel Heval_sst.
(*split; try reflexivity.
intros st st' Heval_sst.*)
unfold eval_sstate in Heval_sst.
simpl in Heval_sst.
(*destruct (instk_height =? length (get_stack_st st)) eqn: eq_instk;
  try discriminate.*)
destruct (eval_sstack sstk maxid bindings model mem strg exts evm_stack_opm)
  as [s|] eqn: eq_eval_sstack; try discriminate.
destruct (eval_smemory smem maxid bindings model mem strg exts evm_stack_opm)
  as [m|] eqn: eq_eval_smem; try discriminate.
destruct (eval_sstorage sstg maxid bindings model mem strg exts evm_stack_opm)
  as [strg'|] eqn: eq_eval_strg; try discriminate.
unfold eval_sstate. simpl. (*rewrite -> eq_instk.*)
simpl in Hvalid.
unfold valid_sstate in Hvalid. simpl in Hvalid.
destruct Hvalid as [Hvalid_smap [Hvalid_sstack [Hvalid_smem Hvalid_strg]]].
unfold valid_smap in Hvalid_smap.
pose proof (opt_sbinding_preserves opt fcmp bindings bindings' maxid 
  ctx flag' Hsafe_cmp Hopt Hvalid_smap Hissat eq_optim_first)
  as Hpreservs_bind_bind'.
(*apply PeanoNat.Nat.eqb_eq in eq_instk.*)
pose proof (preserv_sbindings_sstack bindings bindings' maxid evm_stack_opm
  ctx Hpreservs_bind_bind' sstk s mem strg model exts Hismodel
  eq_eval_sstack) as eq_eval_sstack'.
rewrite -> eq_eval_sstack'.
pose proof (preserv_sbindings_smemory bindings bindings' maxid evm_stack_opm ctx
  Hpreservs_bind_bind' smem model mem m strg exts Hismodel eq_eval_smem)
  as eq_eval_smem'.
rewrite -> eq_eval_smem'.
pose proof (preserv_sbindings_sstorage bindings bindings' maxid evm_stack_opm
  ctx Hpreservs_bind_bind' sstg model mem strg strg' exts Hismodel eq_eval_strg)
  as eq_eval_strg'.
rewrite -> eq_eval_strg'.
assumption.
Qed.

(*
Lemma instk_height_optimize_sst: forall opt fcmp sst sst' flag,
optimize_first_sstate opt fcmp sst = (sst', flag) ->
get_instk_height_sst sst = get_instk_height_sst sst'.
Proof.
intros opt fcmp sst sst' flag Hoptim.
unfold optimize_first_sstate in Hoptim.
destruct sst eqn: eq_sst. destruct sm eqn: eq_sm.
destruct (optimize_first_sbindings opt fcmp bindings instk_height) 
  as [bindings' flag'] eqn: eq_optim_first.
injection Hoptim as eq_sst' eq_flag.
rewrite <- eq_sst'.
reflexivity.
Qed.
*)


Lemma optimize_first_snd_opt_snd: forall opt fcmp,
safe_sstack_val_cmp fcmp ->
opt_sbinding_snd opt ->
optim_snd (optimize_first_sstate opt fcmp).
Proof.
intros opt fcmp Hsafe_fcmp Hopt_snd.
unfold optim_snd. intros ctx sst sst' b Hissat Hvalid_sst Hoptim.
split.
- apply optimize_first_sstate_valid with (opt:=opt)
  (fcmp:=fcmp)(sst:=sst)(flag:=b)(ctx:=ctx); try assumption.
- intros model mem strg exts st' Hismodel Heval.
  pose proof (optimize_first_sstate_preserv opt fcmp sst sst' ctx b Hvalid_sst
      Hopt_snd Hsafe_fcmp Hissat Hoptim) as Hpreserv.
  apply Hpreserv; try assumption.
Qed.


Lemma valid_bindings_snd_opt: forall maxidx n ctx val sb opt fcmp 
  val' flag,
valid_bindings maxidx ((n, val) :: sb) evm_stack_opm ->
opt_smapv_valid_snd opt ->
safe_sstack_val_cmp fcmp ->
is_sat ctx ->
opt val fcmp sb n ctx evm_stack_opm = (val', flag) ->
valid_bindings maxidx ((n, val') :: sb) evm_stack_opm.
Proof.
intros maxidx n ctx val sb opt fcmp val' flag.
intros Hvalid Hopt_smapv_snd Hfcmp His_sat Hopt.
unfold opt_smapv_valid_snd in Hopt_smapv_snd.
unfold valid_bindings in Hvalid.
unfold valid_bindings.
destruct Hvalid as [Hmaxidx [Hvalid_smapv_val Hvalid_sb]].
fold valid_bindings in Hvalid_sb.
pose proof (Hopt_smapv_snd ctx n fcmp sb val val' flag
  Hfcmp His_sat Hvalid_smapv_val Hvalid_sb Hopt) as Hvalid_smapv_val'.
split; try split; try assumption.
Qed.





(* Pipeline of sound optimizations *)

Inductive opt_entry :=
| OpEntry (opt: opt_smap_value_type) (H_snd: opt_sbinding_snd opt).

Definition opt_pipeline := list opt_entry.



(************************************************************************ 
   Optimization strategies using optimization pipelines opt_entries and
   optimizations pipelines
*************************************************************************)

(* Applies the optimization once in the first possible place inside
   the bindings
*)
Definition optimize_first_opt_entry_sbindings (opt_entry: opt_entry)
  (ctx: constraints) (fcmp: sstack_val_cmp_t) (sb: sbindings)
    : sbindings*bool :=
match opt_entry with
| OpEntry opt_sbinding Hopt_snd => 
    optimize_first_sbindings opt_sbinding ctx fcmp sb
end.


(* Applies the optimization once in the first possible place inside
   the bindings __of the sstate__
*)
Definition optimize_first_opt_entry_sstate (opt_e: opt_entry) 
  (fcmp: sstack_val_cmp_t) (ctx: constraints) (sst: sstate) : sstate*bool :=
match opt_e with
| OpEntry opt Hopt_snd =>
  optimize_first_sstate opt fcmp ctx sst
end.


(* Applies the optimization at most n times in a sstate, stops as soon as it
   does not change the sstate *)
Fixpoint apply_opt_n_times (opt_e: opt_entry) (fcmp: sstack_val_cmp_t) 
  (n: nat) (ctx: constraints) (sst: sstate) : sstate*bool :=
match n with
| 0 => (sst, false) 
| S n' => 
    match optimize_first_opt_entry_sstate opt_e fcmp ctx sst with
    | (sst', true) => 
        match apply_opt_n_times opt_e fcmp n' ctx sst' with
        | (sst'', b) => (sst'', true) 
        end
    | (sst', false) => (sst', false)
    end
end.
(* Improvement: extra parameter as flag accumulator for final recursion, 
     if needed for efficiency *)


(* Applies the pipeline in order in a sstate, applying n times each 
   optimization and continuing with the next one *)
Fixpoint apply_opt_n_times_pipeline_once (pipe: opt_pipeline) 
  (fcmp: sstack_val_cmp_t) (n: nat) (ctx: constraints) (sst: sstate) : sstate*bool :=
match pipe with
| [] => (sst, false) 
| opt_e::rp => 
    match apply_opt_n_times opt_e fcmp n ctx sst with
    | (sst', flag1) => 
        match apply_opt_n_times_pipeline_once rp fcmp n ctx sst' with
        | (sst'', flag2) => (sst'', orb flag1 flag2)
        end
    end
end.


(* Applies (apply_opt_n_times_pipeline n) at most k times in a sstate, stops 
   as soon as it does not change the sstate *)
Fixpoint apply_opt_n_times_pipeline_k (pipe: opt_pipeline)
  (fcmp: sstack_val_cmp_t) (n k: nat) (ctx: constraints) 
  (sst: sstate) : sstate*bool :=
match k with
| 0 => (sst, false) 
| S k' => 
    match apply_opt_n_times_pipeline_once pipe fcmp n ctx sst with
    | (sst', true) => 
        match apply_opt_n_times_pipeline_k pipe fcmp n k' ctx sst' with
        | (sst'', b) => (sst'', true) 
        end
    | (sst', false) => (sst', false)
    end
end.
(* Improvement: extra parameter as flag accumulator for final recursion, 
     if needed for efficiency *)



Lemma optimize_first_opt_entry_sstate_snd: forall opt_e fcmp,
safe_sstack_val_cmp fcmp ->
optim_snd (optimize_first_opt_entry_sstate opt_e fcmp).
Proof.
intros opt_e fcmp Hsafe_fcmp.
unfold optim_snd. intros ctx sst sst' b Hissat Hvalid Hoptim_first.
unfold optimize_first_opt_entry_sstate in Hoptim_first.
destruct opt_e as [opt Hopt_snd] eqn: eq_opt_e.
split.
- pose proof (optimize_first_sstate_valid opt fcmp sst sst' ctx b Hvalid
    Hopt_snd Hsafe_fcmp Hissat Hoptim_first).
  assumption.
- apply optimize_first_sstate_preserv with (opt:=opt)(fcmp:=fcmp)(flag:=b);
  try assumption.
Qed.


Lemma apply_opt_n_times_snd: forall opt_e fcmp n,
safe_sstack_val_cmp fcmp ->
optim_snd (apply_opt_n_times opt_e fcmp n).
Proof.
intros opt_e fcmp n. revert opt_e fcmp.
induction n as [| n' IH].
- intros opt_e fcmp Hsafe_cmp.
  unfold optim_snd.
  intros ctx sst sst' b Hissat Hvalid Happly.
  simpl in Happly. injection Happly as eq_sst' _.
  rewrite <- eq_sst'.
  split; try assumption.
  intuition.
- intros opt_e fcmp Hsafe_cmp.
  unfold optim_snd.
  intros ctx sst sst' b Hissat Hvalid Happly.
  simpl in Happly. 
  destruct (optimize_first_opt_entry_sstate opt_e fcmp ctx sst) 
    as [sst1 flag] eqn: eq_optim.
  destruct flag eqn: eq_flag.
  + destruct (apply_opt_n_times opt_e fcmp n' ctx sst1) as [sst2 flag2] 
      eqn: eq_apply_n'.
    injection Happly as eq_sst' _.
    rewrite <- eq_sst'.
    pose proof (optimize_first_opt_entry_sstate_snd opt_e fcmp Hsafe_cmp)
      as Hoptim_snd.
    unfold optim_snd in Hoptim_snd.
    pose proof (Hoptim_snd ctx sst sst1 true Hissat Hvalid eq_optim) as Hone.
    destruct Hone as [Hvalid1 Heval].
    pose proof (IH opt_e fcmp Hsafe_cmp) as IHn'.
    unfold optim_snd in IHn'.
    pose proof (IHn' ctx sst1 sst2 flag2 Hissat Hvalid1 eq_apply_n') as HIHn'.
    destruct HIHn' as [Hvalid' Heval'].
    split; try assumption.
    intros model mem strg exts st' Hismodel Heval_st. 
    apply Heval'; try assumption.
    intuition.
  + injection Happly as eq_sst' _.
    rewrite <- eq_sst'.
    pose proof (optimize_first_opt_entry_sstate_snd opt_e fcmp Hsafe_cmp)
      as Hoptim_snd.
    unfold optim_snd in Hoptim_snd.
    pose proof (Hoptim_snd ctx sst sst1 false Hissat Hvalid eq_optim) as Hone.
    destruct Hone as [Hvalid1 Heval].
    split; try assumption.
Qed.


Lemma apply_opt_n_times_pipeline_once_snd: forall pipe fcmp n,
safe_sstack_val_cmp fcmp ->
optim_snd (apply_opt_n_times_pipeline_once pipe fcmp n).
Proof.
induction pipe as [| opt_e rp IH].
- intros fcmp n Hsafe_cmp.
  unfold optim_snd.
  intros ctx sst sst' b Hissat Hvalid Happly.
  simpl in Happly. injection Happly as eq_sst' _.
  rewrite <- eq_sst'.
  split; try assumption.
  auto.
- intros fcmp n Hsafe_cmp.
  unfold optim_snd.
  intros ctx sst sst' b Hissat Hvalid Happly.
  simpl in Happly. 
  destruct (apply_opt_n_times opt_e fcmp n ctx sst) 
    as [sst1 flag1] eqn: eq_optim_h.
  destruct (apply_opt_n_times_pipeline_once rp fcmp n ctx sst1) as [sst2 flag2] 
    eqn: eq_optim_rp.
  injection Happly as eq_sst' _.
  rewrite <- eq_sst'.
  pose proof (apply_opt_n_times_snd opt_e fcmp n Hsafe_cmp) as Hoptim_snd_h.
  unfold optim_snd in Hoptim_snd_h.
  pose proof (Hoptim_snd_h ctx sst sst1 flag1 Hissat Hvalid eq_optim_h) as Hoptim_snd_h.
  destruct Hoptim_snd_h as [Hvalid1 Heval1].
  pose proof (IH fcmp n Hsafe_cmp) as IH.
  unfold optim_snd in IH.
  pose proof (IH ctx sst1 sst2 flag2 Hissat Hvalid1 eq_optim_rp) as IH.
  intuition.
Qed.


Lemma apply_opt_n_times_pipeline_k_snd: forall pipe fcmp n k,
safe_sstack_val_cmp fcmp ->
optim_snd (apply_opt_n_times_pipeline_k pipe fcmp n k).
Proof.
intros pipe fcmp n k. revert pipe fcmp n.
induction k as [| k' IH].
- intros pipe fcmp Hsafe_cmp n.
  unfold optim_snd.
  intros ctx sst sst' b Hissat Hvalid Happly.
  simpl in Happly. injection Happly as eq_sst' _.
  rewrite <- eq_sst'.
  split; try assumption.
  auto.
- intros pipe fcmp n Hsafe_cmp.
  unfold optim_snd.
  intros ctx sst sst' b Hissat Hvalid Happly.
  simpl in Happly. 
  destruct (apply_opt_n_times_pipeline_once pipe fcmp n ctx sst) 
    as [sst1 flag1] eqn: eq_optim.
  destruct flag1 eqn: eq_flag1.
  + destruct (apply_opt_n_times_pipeline_k pipe fcmp n k' ctx sst1) as [sst2 flag2] 
      eqn: eq_apply_n'.
    injection Happly as eq_sst' _.
    rewrite <- eq_sst'.
    pose proof (apply_opt_n_times_pipeline_once_snd pipe fcmp n Hsafe_cmp)
      as Hoptim_snd.
    unfold optim_snd in Hoptim_snd.
    pose proof (Hoptim_snd ctx sst sst1 true Hissat Hvalid eq_optim) as Hone.
    destruct Hone as [Hvalid1 Heval1].
    pose proof (IH pipe fcmp n Hsafe_cmp) as IH.
    unfold optim_snd in IH.
    pose proof (IH ctx sst1 sst2 flag2 Hissat Hvalid1 eq_apply_n') as IH.
    destruct IH as [Hvalid' Heval'].
    split; try assumption.
    auto.
  + injection Happly as eq_sst' _.
    rewrite <- eq_sst'.
    pose proof (apply_opt_n_times_pipeline_once_snd pipe fcmp n Hsafe_cmp)
      as Hoptim_snd.
    unfold optim_snd in Hoptim_snd.
    pose proof (Hoptim_snd ctx sst sst1 false Hissat Hvalid eq_optim) as Hone.
    destruct Hone as [Hvalid1 Heval].
    auto.
Qed.



End Optimizations_Def.
