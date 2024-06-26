Require Import Arith. 
Require Import Nat.
Require Import Bool.
Require Import bbv.Word.
Require Import Coq.NArith.NArith.
Require Import List.
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.program.
Import Program.

Require Import FORVES2.execution_state.
Import ExecutionState.

Require Import FORVES2.stack_operation_instructions.
Import StackOpInstrs.

Require Import FORVES2.misc.
Import Misc.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.constraints.
Import Constraints.


Module ValidSymbolicState.


Definition valid_sstack_value (maxidx: nat) (value : sstack_val) : Prop :=
  match value with
  | Val _ => True
  | InVar _ => True
  | FreshVar idx => idx < maxidx
  end.

(* All the FreshVar in the sstack are less than maxidx *)
Fixpoint valid_sstack (maxidx: nat) (sstk : sstack) : Prop :=
  match sstk with
  | [] => True
  | sv::sstk' => valid_sstack_value maxidx sv /\ valid_sstack maxidx sstk'
  end.

Definition valid_smemory_update (maxidx: nat) (u : memory_update sstack_val) : Prop :=
  match u with
  | U_MSTORE _ offset value | U_MSTORE8 _ offset value => valid_sstack_value maxidx offset /\ valid_sstack_value maxidx value
  end.

Fixpoint valid_smemory (maxidx: nat) (smem : smemory) : Prop :=
  match smem with
  | [] => True
  | u::smem' => valid_smemory_update maxidx u /\ valid_smemory maxidx smem'
  end.

Definition valid_sstorage_update (maxidx: nat) (u : storage_update sstack_val) : Prop :=
  match u with
  | U_SSTORE _ offset value => valid_sstack_value maxidx offset /\ valid_sstack_value maxidx value
  end.

Fixpoint valid_sstorage (maxidx: nat) (sstrg : sstorage) : Prop :=
  match sstrg with
  | [] => True
  | u::sstrg' => valid_sstorage_update maxidx u /\ valid_sstorage maxidx sstrg'
  end.

Definition valid_stack_op_instr (maxidx: nat) (ops: stack_op_instr_map) (label: stack_op_instr) (args: list sstack_val): Prop :=
  match (ops label) with
  | OpImp nargs _ _ _ => length args = nargs /\  valid_sstack maxidx args
  end.

Definition valid_smap_value (maxidx: nat) (ops: stack_op_instr_map) (value: smap_value) : Prop :=
  match value with
  | SymBasicVal v => valid_sstack_value maxidx v
  | SymMETAPUSH _ _ => True
  | SymOp label args => valid_stack_op_instr maxidx ops label args 
  | SymMLOAD offset smem => valid_sstack_value maxidx offset /\ valid_smemory maxidx smem
  | SymSLOAD key sstrg => valid_sstack_value maxidx key /\ valid_sstorage maxidx sstrg
  | SymSHA3 offset size smem => valid_sstack_value maxidx offset /\ valid_sstack_value maxidx size /\ valid_smemory maxidx smem
  end.

(* all keys defined *)
Fixpoint valid_bindings (maxid: nat) (sb: sbindings) (ops: stack_op_instr_map): Prop :=
  match sb with
  | [] => maxid = 0
  | (idx,value)::sb' => maxid = (S idx) /\ valid_smap_value idx ops value /\ valid_bindings idx sb' ops
  end.

Definition valid_smap (maxidx: nat) (sb: sbindings) (ops: stack_op_instr_map): Prop :=
  valid_bindings maxidx sb ops.


Definition valid_sstate (sst: sstate) (ops: stack_op_instr_map): Prop :=
  let sstk := get_stack_sst sst in
  let smem := get_memory_sst sst in
  let sstrg := get_storage_sst sst in
  let m := get_smap_sst sst in
  let maxidx := get_maxidx_smap m in
  let sb := get_bindings_smap m in
    valid_smap maxidx sb ops /\ 
    valid_sstack maxidx sstk /\
    valid_smemory maxidx smem /\
    valid_sstorage maxidx sstrg.


(* Valid state checker *)

Definition chk_valid_sstack_value (maxidx: nat) (value : sstack_val) : bool :=
  match value with
  | Val _ => true
  | InVar _ => true
  | FreshVar idx => idx <? maxidx
  end.

(* All the FreshVar in the sstack are less than maxidx *)
Fixpoint chk_valid_sstack (maxidx: nat) (sstk : sstack) : bool :=
  match sstk with
  | [] => true
  | sv::sstk' => chk_valid_sstack_value maxidx sv && chk_valid_sstack maxidx sstk'
  end.

Definition chk_valid_smemory_update (maxidx: nat) (u : memory_update sstack_val) : bool :=
  match u with
  | U_MSTORE _ offset value | U_MSTORE8 _ offset value => chk_valid_sstack_value maxidx offset && chk_valid_sstack_value maxidx value
  end.

Fixpoint chk_valid_smemory (maxidx: nat) (smem : smemory) : bool :=
  match smem with
  | [] => true
  | u::smem' => chk_valid_smemory_update maxidx u && chk_valid_smemory maxidx smem'
  end.

Definition chk_valid_sstorage_update (maxidx: nat) (u : storage_update sstack_val) : bool :=
  match u with
  | U_SSTORE _ offset value => chk_valid_sstack_value maxidx offset && chk_valid_sstack_value maxidx value
  end.

Fixpoint chk_valid_sstorage (maxidx: nat) (sstrg : sstorage) : bool :=
  match sstrg with
  | [] => true
  | u::sstrg' => chk_valid_sstorage_update maxidx u && chk_valid_sstorage maxidx sstrg'
  end.

Definition chk_valid_stack_op_instr (maxidx: nat) (ops: stack_op_instr_map) (label: stack_op_instr) (args: list sstack_val): bool :=
  match (ops label) with
  | OpImp nargs _ _ _ => (length args =? nargs) &&  chk_valid_sstack maxidx args
  end.

Definition chk_valid_smap_value (maxidx: nat) (ops: stack_op_instr_map) (value: smap_value) : bool :=
  match value with
  | SymBasicVal v => chk_valid_sstack_value maxidx v
  | SymMETAPUSH _ _ => true
  | SymOp label args => chk_valid_stack_op_instr maxidx ops label args 
  | SymMLOAD offset smem => chk_valid_sstack_value maxidx offset && chk_valid_smemory maxidx smem
  | SymSLOAD key sstrg => chk_valid_sstack_value maxidx key && chk_valid_sstorage maxidx sstrg
  | SymSHA3 offset size smem => chk_valid_sstack_value maxidx offset && chk_valid_sstack_value maxidx size && chk_valid_smemory maxidx smem
  end.

Fixpoint chk_valid_bindings (maxid: nat) (sb: sbindings) (ops: stack_op_instr_map): bool :=
  match sb with
  | [] => maxid =? 0
  | (idx,value)::sb' => (maxid =? (S idx)) && chk_valid_smap_value idx ops value && chk_valid_bindings idx sb' ops
  end.

Definition chk_valid_smap (maxidx: nat) (sb: sbindings) (ops: stack_op_instr_map): bool :=
  chk_valid_bindings maxidx sb ops.


Definition chk_valid_sstate (sst: sstate) (ops: stack_op_instr_map): bool :=
  let sstk := get_stack_sst sst in
  let smem := get_memory_sst sst in
  let sstrg := get_storage_sst sst in
  let m := get_smap_sst sst in
  let maxidx := get_maxidx_smap m in
  let sb := get_bindings_smap m in
    chk_valid_smap maxidx sb ops && 
    chk_valid_sstack maxidx sstk &&
    chk_valid_smemory maxidx smem &&
    chk_valid_sstorage maxidx sstrg.


Lemma chk_valid_sstack_value_snd:
  forall maxidx sv,
    chk_valid_sstack_value maxidx sv = true -> valid_sstack_value maxidx sv.
Proof.
  intros maxidx sv H_chk.
  unfold chk_valid_sstack_value in H_chk.
  unfold valid_sstack_value.

  destruct sv; try apply I.
  rewrite <- Nat.ltb_lt.
  apply H_chk.
Qed.

Lemma chk_valid_smemory_update_snd:
  forall maxidx u,
    chk_valid_smemory_update maxidx u = true -> valid_smemory_update maxidx u.
Proof.
  intros maxidx u H_chk.
  destruct u as [soffset svalue | soffset svalue].
  + simpl in H_chk.
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_soffset H_chk_svalue].
    apply chk_valid_sstack_value_snd in H_chk_soffset.
    apply chk_valid_sstack_value_snd in H_chk_svalue.

    unfold valid_smemory_update.
    split; auto.
  + simpl in H_chk.
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_soffset H_chk_svalue].
    apply chk_valid_sstack_value_snd in H_chk_soffset.
    apply chk_valid_sstack_value_snd in H_chk_svalue.

    unfold valid_smemory_update.
    split; auto.
Qed.

Lemma chk_valid_sstorage_update_snd:
  forall maxidx u,
    chk_valid_sstorage_update maxidx u = true -> valid_sstorage_update maxidx u.
Proof.
  intros maxidx u H_chk.
  destruct u as [skey svalue].
  simpl in H_chk.
  apply andb_prop in H_chk.
  destruct H_chk as [H_chk_skey H_chk_svalue].
  apply chk_valid_sstack_value_snd in H_chk_skey.
  apply chk_valid_sstack_value_snd in H_chk_svalue.

  unfold valid_sstorage_update.
  split; auto.
Qed.

Lemma chk_valid_smemory_snd:
  forall maxidx smem,
    chk_valid_smemory maxidx smem = true -> valid_smemory maxidx smem.
Proof.
  intros maxidx.
  induction smem as [|u smem' IHsmem'].
  + intros H_chk.
    simpl.
    apply I.
  + intros H_chk.
    simpl in H_chk.
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_u H_chk_smem'].
    apply IHsmem' in H_chk_smem'.
    apply chk_valid_smemory_update_snd in H_chk_u.
    unfold valid_smemory.
    fold valid_smemory.
    split; auto.
Qed.
    
Lemma chk_valid_sstorage_snd:
  forall maxidx sstrg,
    chk_valid_sstorage maxidx sstrg = true -> valid_sstorage maxidx sstrg.
Proof.
  intros maxidx.
  induction sstrg as [|u sstrg' IHsstrg'].
  + intros H_chk.
    simpl.
    apply I.
  + intros H_chk.
    simpl in H_chk.
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_u H_chk_sstrg'].
    apply IHsstrg' in H_chk_sstrg'.
    apply chk_valid_sstorage_update_snd in H_chk_u.
    unfold valid_sstorage.
    fold valid_sstorage.
    split; auto.
Qed.

Lemma chk_valid_sstack_snd:
  forall maxidx sstk,
    chk_valid_sstack maxidx sstk = true -> valid_sstack maxidx sstk.
Proof.
  intros maxidx.
  induction sstk as [|sv sstk' IHsstk'].
  + intros H_chk.
    simpl.
    apply I.
  + intros H_chk.
    simpl in H_chk.
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_sv H_chk_sstk'].
    apply IHsstk' in H_chk_sstk'.
    apply chk_valid_sstack_value_snd in H_chk_sv.
    unfold valid_sstack.
    fold valid_sstack.
    split; auto.
Qed.


Lemma chk_valid_stack_op_instr_snd:
  forall maxidx ops label args,
    chk_valid_stack_op_instr maxidx ops label args = true -> valid_stack_op_instr maxidx ops label args.
Proof.
  intros maxidx ops label args H_chk.
  unfold chk_valid_stack_op_instr in H_chk.
  unfold valid_stack_op_instr.
  destruct (ops label).
  apply andb_prop in H_chk.
  destruct H_chk as [H_chk_len H_chk_args].
  rewrite Nat.eqb_eq in H_chk_len.
  apply chk_valid_sstack_snd in H_chk_args.
  split; auto.
Qed.
  

Lemma chk_valid_smap_value_snd:
  forall maxidx ops value,
     chk_valid_smap_value maxidx ops value = true -> valid_smap_value maxidx ops value.
Proof.
  intros maxidx ops value H_chk.
  destruct value.
  + simpl in H_chk.
    simpl.
    apply chk_valid_sstack_value_snd in H_chk.
    apply H_chk.
  + simpl.
    apply I.
  + simpl in H_chk.
    apply chk_valid_stack_op_instr_snd in H_chk.
    simpl.
    apply H_chk.
  + simpl in H_chk.
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_offset H_chk_smem].
    apply chk_valid_sstack_value_snd in H_chk_offset.
    apply chk_valid_smemory_snd in H_chk_smem.
    simpl.
    split; auto.
  + simpl in H_chk.
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_key H_chk_sstrg].
    apply chk_valid_sstack_value_snd in H_chk_key.
    apply chk_valid_sstorage_snd in H_chk_sstrg.
    simpl.
    split; auto.
  + simpl in H_chk.
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk H_chk_smem].
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_offset H_chk_size].
    apply chk_valid_sstack_value_snd in H_chk_offset.
    apply chk_valid_sstack_value_snd in H_chk_size.
    apply chk_valid_smemory_snd in H_chk_smem.
    simpl.
    split; auto.
Qed.
       
Lemma chk_valid_bindings_snd:
  forall maxidx sb ops,
    chk_valid_bindings maxidx sb ops = true -> valid_bindings maxidx sb ops.
Proof.
  intros maxidx sb ops.
  revert maxidx.
  revert sb.
  
  induction sb as [|b sb' IHsb'].
  + intros maxidx H_chk.
    simpl.
    destruct maxidx as [| maxidx'].
    ++ reflexivity.
    ++ simpl in H_chk.
       discriminate.
  + intros maxidx H_chk.
    simpl in H_chk.
    destruct b as [idx value].
    apply andb_prop in H_chk.
    destruct H_chk as [H_chk H_chk_sb'].

    apply andb_prop in H_chk.
    destruct H_chk as [H_chk_maxidx H_chk_value].

    apply chk_valid_smap_value_snd in H_chk_value.
    apply IHsb' in H_chk_sb'.
    rewrite Nat.eqb_eq in H_chk_maxidx.
    simpl.
    split; auto.
Qed.

Lemma chk_valid_smap_snd:
  forall maxidx sb ops,
    chk_valid_smap maxidx sb ops = true -> valid_smap maxidx sb ops.
Proof.
  apply chk_valid_bindings_snd.
Qed.


Lemma chk_valid_sstate_snd:
  forall sst ops,
    chk_valid_sstate sst ops = true -> valid_sstate sst ops.
Proof.
  intros sst ops H_chk_valid_sst.
  unfold chk_valid_sstate in H_chk_valid_sst.

  apply andb_prop in H_chk_valid_sst.
  destruct H_chk_valid_sst as [H_chk_valid_sst H_chk_valid_sstrorage].
  apply chk_valid_sstorage_snd in H_chk_valid_sstrorage.
    
  apply andb_prop in H_chk_valid_sst.
  destruct H_chk_valid_sst as [H_chk_valid_sst H_chk_valid_smemory].
  apply chk_valid_smemory_snd in H_chk_valid_smemory.
  
  apply andb_prop in H_chk_valid_sst.
  destruct H_chk_valid_sst as [H_chk_valid_smap H_chk_valid_sstack].
  apply chk_valid_sstack_snd in H_chk_valid_sstack.

  apply chk_valid_smap_snd in H_chk_valid_smap.

  unfold valid_sstate.

  split; try auto.
Qed.

(*Lemma fresh_var_gt_map_maxidx_S:
  forall sb maxidx,
    fresh_var_gt_map maxidx sb ->
    fresh_var_gt_map (S maxidx) sb.
Proof.
  induction sb as [|v sb' IHsm'].
  - auto.
  - intros.
    unfold fresh_var_gt_map in H.
    fold fresh_var_gt_map in H.
    destruct v as [k kvalue].
    destruct H.
    unfold fresh_var_gt_map.
    fold fresh_var_gt_map.
    split.
    + auto.
    + apply IHsm'.
      apply H0.
Qed.*)


Lemma valid_sstack_app:
  forall maxidx l1 l2,
    valid_sstack maxidx l1 ->
    valid_sstack maxidx l2 ->
    valid_sstack maxidx (l1++l2).
Proof.
  intros maxidx.
  induction l1 as [|sv l1' IHl1'].
  - intros l2 H_l1 H_l2.
    simpl.
    apply H_l2.
  - intros l2 H_l1 H_l2.
    simpl in H_l1.
    destruct H_l1 as [H_l1_0 H_l1_1].
    simpl.
    split.
    + apply H_l1_0.
    + apply IHl1'.
      * apply H_l1_1.
      * apply H_l2.
Qed.

Lemma valid_sstack_app1:
  forall maxidx l1 l2,
    valid_sstack maxidx (l1++l2) ->
    valid_sstack maxidx l1 /\
    valid_sstack maxidx l2.
Proof.
  intros maxidx.
  induction l1 as [|sv l1' IHl1'].
  - intros l2 H_l1_l2.
    simpl.
    simpl in H_l1_l2.
    split.
    + apply I.
    + apply H_l1_l2.
  - intros l2 H_l1_l2.
    simpl in H_l1_l2.
    destruct H_l1_l2 as [H_sv H_l1'_l2].
    simpl.
    pose proof (IHl1' l2 H_l1'_l2) as [IHl1'_0 IHl1'_1].
    split.
    + split.
      * apply H_sv.
      * apply IHl1'_0.
    + apply IHl1'_1.
Qed.

Lemma valid_sstack_value_S_maxidx:
  forall maxidx sv,
    valid_sstack_value maxidx sv ->
    valid_sstack_value (S maxidx) sv.
Proof.
  intros maxidx sv H_valid_sv.
  destruct sv; simpl; try auto.
Qed.

(*
(* TODO: This lemma becomes obsolete after removing instk_height *)
Lemma valid_sstack_value_S_instk_height:
  forall maxidx sv,
    valid_sstack_value maxidx sv ->
    valid_sstack_value  maxidx sv.
Proof.
  intros maxidx sv H_valid_sv.
  destruct sv; simpl; try auto.
Qed.
 *)

Lemma valid_sstack_S_maxidx:
  forall maxidx l,
    valid_sstack maxidx l ->
    valid_sstack (S maxidx) l.
Proof.
  intros maxidx.
  induction l as [|sv l' IHl'].
  - intuition.
  - simpl.
    intros H_l.
    destruct H_l as [H_l_0 H_l_1].
    split.
    + apply valid_sstack_value_S_maxidx. apply H_l_0.
    + apply IHl'. apply H_l_1.
Qed.


Lemma add_to_smap_valid_smap:
  forall idx m m' smv ops,
    valid_smap (get_maxidx_smap m) (get_bindings_smap m) ops ->
    valid_smap_value (get_maxidx_smap m) ops smv ->
    add_to_smap m smv = (idx, m') ->
    valid_smap (get_maxidx_smap m') (get_bindings_smap m') ops.
Proof. 
  intros idx m m' smv ops H_valid_m H_valid_smv H_add.

  destruct m as [maxidx sb] eqn:E_m.
  destruct m' as [maxidx' sb'] eqn:E_m'.
  
  unfold valid_smap in H_valid_m.

  assert(H_add' :=  H_add).
  simpl in H_add'.
  injection H_add' as H_maxidx H_maxidx' H_sb'.  

  unfold valid_smap.

  rewrite <- H_sb'.
  simpl.
  split.

  * intuition.
  * simpl in H_valid_smv.
    split.
        
    ** apply H_valid_smv.
    ** simpl in H_valid_m.
       apply H_valid_m.
Qed. 

Lemma add_to_smap_valid_sstack:
  forall idx m m' smv sstk ops,
    valid_sstack (get_maxidx_smap m) sstk ->
    valid_smap_value (get_maxidx_smap m) ops smv ->
    add_to_smap m smv = (idx, m') ->
    valid_sstack (get_maxidx_smap m') sstk.
Proof.
  intros idx m m' smv sstk ops H_valid_sstk H_valid_smv H_add_to_map.
  destruct m as [maxid sb] eqn:E_m.
  destruct m' as [maxid' sb'] eqn:E_m'.
  assert (H_add_to_map' := H_add_to_map).
  unfold add_to_smap in H_add_to_map'.
  injection H_add_to_map' as H_maxid H_maxid' H_sb'.
  simpl.
  simpl in H_valid_sstk.
  simpl in H_valid_smv.
  rewrite <- H_maxid'.
  apply valid_sstack_S_maxidx.
  apply H_valid_sstk.
Qed.

Lemma add_to_smap_valid_sstack_value:
  forall idx m m' smv sv ops,
    valid_sstack_value (get_maxidx_smap m) sv ->
    valid_smap_value (get_maxidx_smap m) ops smv ->
    add_to_smap m smv = (idx, m') ->
    valid_sstack_value (get_maxidx_smap m') sv.
Proof.
  intros idx m m' smv sv ops H_valid_sv H_valid_smv H_add_to_smap.
  destruct m as [maxid sb] eqn:E_m.
  destruct m' as [maxid' sb'] eqn:E_m'.
  simpl.
  simpl in H_valid_sv. 
  simpl in H_valid_smv.
  simpl in H_add_to_smap.
  injection H_add_to_smap as H_maxidx H_maxidx' H_sb'.
  rewrite <-  H_maxidx'.
  apply valid_sstack_value_S_maxidx.
  apply H_valid_sv.
Qed.

(*
Lemma valid_sbinings_S_maxidx:
  forall instk_height maxidx ops u sb,
    valid_bindings instk_height maxidx (u::sb) ops ->
    valid_bindings instk_height (S maxidx) (u::sb) ops.
Proof.
  intros instk_height maxidx ops u sb.
  revert sb.
  induction sb as [|x sb' IHsb'].
  - intros H_maxidx.
    destruct u.
    simpl in H_maxidx.
    destruct maxidx; try discriminate.
    simpl.
 *)

Lemma valid_smemory_update_S_maxidx:
  forall maxidx u,
    valid_smemory_update maxidx u ->
    valid_smemory_update (S maxidx) u.
Proof.
  intros maxidx u H_valid_u.
  destruct u as [offset value|offset value].
  - simpl.
    simpl in H_valid_u.
    destruct H_valid_u as [H_valid_u_0 H_valid_u_1].
    split.
    + apply valid_sstack_value_S_maxidx.
      apply H_valid_u_0.
    + apply valid_sstack_value_S_maxidx.
      apply H_valid_u_1.
  - simpl.
    simpl in H_valid_u.
    destruct H_valid_u as [H_valid_u_0 H_valid_u_1].
    split.
    + apply valid_sstack_value_S_maxidx.
      apply H_valid_u_0.
    + apply valid_sstack_value_S_maxidx.
      apply H_valid_u_1.
Qed.

Lemma valid_smemory_S_maxidx:
  forall maxidx smem,
    valid_smemory maxidx smem ->
    valid_smemory (S maxidx) smem.
Proof.
  intros maxidx.
  induction smem as [|u smem' IHsmem'].
  - auto.
  - simpl.
    intro H_valid_smem.
    destruct H_valid_smem as [H_valid_smem_0 H_valid_smem_1].
    split.
    + apply valid_smemory_update_S_maxidx.
      apply H_valid_smem_0.
    + apply IHsmem'.
      apply H_valid_smem_1.
Qed.

Lemma valid_sstorage_update_S_maxidx:
  forall maxidx u,
    valid_sstorage_update maxidx u ->
    valid_sstorage_update (S maxidx) u.
Proof.
  intros maxidx u H_valid_u.
  destruct u as [offset value].
  simpl.
  simpl in H_valid_u.
  destruct H_valid_u as [H_valid_u_0 H_valid_u_1].
  split.
  + apply valid_sstack_value_S_maxidx.
    apply H_valid_u_0.
  + apply valid_sstack_value_S_maxidx.
    apply H_valid_u_1.
Qed.

Lemma valid_sstorage_S_maxidx:
  forall maxidx sstrg,
    valid_sstorage maxidx sstrg ->
    valid_sstorage (S maxidx) sstrg.
Proof.
  intros maxidx.
  induction sstrg as [|u sstrg' IHsstrg'].
  - auto.
  - simpl.
    intro H_valid_sstrg.
    destruct H_valid_sstrg as [H_valid_sstrg_0 H_valid_sstrg_1].
    split.
    + apply valid_sstorage_update_S_maxidx.
      apply H_valid_sstrg_0.
    + apply IHsstrg'.
      apply H_valid_sstrg_1.
Qed.

Lemma add_to_smap_valid_smemory:
  forall idx m m' smv smem ops,
    valid_smemory (get_maxidx_smap m) smem ->
    valid_smap_value (get_maxidx_smap m) ops smv ->
    add_to_smap m smv = (idx, m') ->
    valid_smemory (get_maxidx_smap m') smem.
Proof.
  intros idx m m' smv smem ops H_valid_smem H_valid_smv H_add_to_map.
  destruct m as [maxid sb] eqn:E_m.
  destruct m' as [maxid' sb'] eqn:E_m'.
  assert (H_add_to_map' := H_add_to_map).
  unfold add_to_smap in H_add_to_map'.
  injection H_add_to_map' as H_maxid H_maxid' H_sb'.
  rewrite <- H_sb'.
  simpl.
  rewrite <- H_maxid'.
  apply valid_smemory_S_maxidx.
  simpl in H_valid_smem.
  apply H_valid_smem.
Qed.

Lemma add_to_smap_valid_sstorage:
  forall idx m m' smv sstrg ops,
    valid_sstorage (get_maxidx_smap m) sstrg ->
    valid_smap_value (get_maxidx_smap m) ops smv ->
    add_to_smap m smv = (idx, m') ->
    valid_sstorage (get_maxidx_smap m') sstrg.
Proof.
  intros idx m m' smv sstrg ops H_valid_sstrg H_valid_smv H_add_to_map.
  destruct m as [maxid sb] eqn:E_m.
  destruct m' as [maxid' sb'] eqn:E_m'.
  assert (H_add_to_map' := H_add_to_map).
  unfold add_to_smap in H_add_to_map'.
  injection H_add_to_map' as H_maxid H_maxid' H_sb'.
  rewrite <- H_sb'.
  simpl.
  rewrite <- H_maxid'.
  apply valid_sstorage_S_maxidx.
  simpl in H_valid_sstrg.
  apply H_valid_sstrg.
Qed.

Lemma add_to_map_valid_sstate:
  forall sst idx m smv ops,
    valid_sstate sst ops ->
    valid_smap_value (get_maxidx_smap (get_smap_sst sst)) ops smv ->
    (idx,m) = add_to_smap (get_smap_sst sst) smv ->
    valid_sstate (set_smap_sst sst m) ops.
Proof. 
  intros sst idx m smv ops.

  unfold valid_sstate.
  rewrite set_and_then_get_smap_sst.
  rewrite sstack_preserved_when_updating_smap_sst.
  rewrite smemory_preserved_when_updating_smap_sst.
  rewrite sstorage_preserved_when_updating_smap_sst.

  intros H_valid_sst H_valid_smap_value H_add_to_smap.
  destruct H_valid_sst as [H_valid_sst_0 [H_valid_sst_1 [H_valid_sst_2 H_valid_sst_3]]].
 
  split.

  (* The case of smap *)
  - symmetry in H_add_to_smap.
    pose proof (add_to_smap_valid_smap idx (get_smap_sst sst) m smv ops H_valid_sst_0 H_valid_smap_value H_add_to_smap) as H_add_to_smap_valid_smap.
    apply H_add_to_smap_valid_smap.

  - split.

    (* The case of ssstack *)
    + symmetry in H_add_to_smap.
      pose proof (add_to_smap_valid_sstack idx (get_smap_sst sst) m smv (get_stack_sst sst) ops H_valid_sst_1 H_valid_smap_value H_add_to_smap) as H_add_to_smap_valid_sstack.
      apply H_add_to_smap_valid_sstack.

    + split.

    (* The case of smemory *)
    * symmetry in H_add_to_smap.
      pose proof (add_to_smap_valid_smemory idx (get_smap_sst sst) m smv (get_memory_sst sst) ops  H_valid_sst_2 H_valid_smap_value H_add_to_smap) as H_add_to_smap_valid_smemory.
      apply H_add_to_smap_valid_smemory.
        
    (* The case of sstorage *)
    * symmetry in H_add_to_smap.
      pose proof (add_to_smap_valid_sstorage idx (get_smap_sst sst) m smv (get_storage_sst sst) ops H_valid_sst_3 H_valid_smap_value H_add_to_smap) as H_add_to_smap_valid_sstorage.
      apply H_add_to_smap_valid_sstorage.
Qed.


(* when adding a value of the map, it key is smaller that maxidx of the new map *)
Lemma add_to_smap_key_lt_maxidx:
  forall m m' key smv,
    (key,m') = add_to_smap m smv ->
    key < get_maxidx_smap m'.
Proof.
  intros m m' key smv H_add_to_smap.
  destruct m as [maxid sb].
  simpl in H_add_to_smap.
  injection H_add_to_smap as H_maxid H_m'.
  rewrite H_m'.
  simpl.
  rewrite H_maxid.
  apply Nat.lt_succ_diag_r.
Qed.


Lemma valid_follow_in_smap:
  forall sb sv maxidx ops smv maxidx' sb',
    valid_sstack_value maxidx sv ->
    valid_bindings maxidx sb ops ->
    follow_in_smap sv maxidx sb = Some (FollowSmapVal smv maxidx' sb') ->
    valid_smap_value maxidx' ops smv /\
      valid_bindings maxidx' sb' ops /\
      (not_basic_value_smv smv = true -> maxidx > maxidx').
Proof.
  induction sb as [|p sb'' IHsb''].
  - intros sv maxidx ops smv maxidx' sb' H_valid_sv H_valid_sb H_follow.
    destruct sv eqn:E_sv.
    + simpl in H_valid_sv.
      simpl in H_valid_sb.
      simpl in H_follow.
      injection H_follow as H_smv H_maxidx' H_sb'.
      rewrite <- H_sb'.
      rewrite <- H_smv.
      rewrite <- H_maxidx'.
      simpl.
      split; try intuition.
      
    + simpl in H_valid_sv.
      simpl in H_valid_sb.
      simpl in H_follow.
      injection H_follow as H_smv H_maxidx' H_sb'.
      rewrite <- H_sb'.
      rewrite <- H_smv.
      rewrite <- H_maxidx'.
      simpl.
      split; try intuition.
    + discriminate.
  - intros sv maxidx ops smv maxidx' sb' H_valid_sv H_valid_sb H_follow.
    destruct sv eqn:E_sv.
    + simpl in H_valid_sv.
      simpl in H_valid_sb.
      simpl in H_follow.
      injection H_follow as H_smv H_maxidx' H_sb'.
      rewrite <- H_sb'.
      rewrite <- H_smv.
      rewrite <- H_maxidx'.
      simpl.
      split; try intuition.
    + simpl in H_valid_sv.
      simpl in H_valid_sb.
      simpl in H_follow.
      injection H_follow as H_smv H_maxidx' H_sb'.
      rewrite <- H_sb'.
      rewrite <- H_smv.
      rewrite <- H_maxidx'.
      simpl.
      split; try intuition.
    + destruct p as [idx value] eqn:E_p.
      simpl in H_valid_sv.
      simpl in H_valid_sb.
      simpl in H_follow.
      destruct H_valid_sb as [H_valid_sb_0 [H_valid_sb_1 H_valid_sb_2]].
      destruct (idx =? var) eqn:E_n_var.
      * destruct (is_fresh_var_smv value) as [idx'|] eqn:E_is_fresh_var_value.
        ** destruct value eqn:E_value; try discriminate.
           destruct val; try discriminate.
           simpl in E_is_fresh_var_value.
           injection E_is_fresh_var_value as E_is_fresh_var_value.
           simpl in H_valid_sb_1.
           rewrite E_is_fresh_var_value in H_valid_sb_1.

           assert(H_valid_sstack_value_FreshVar_idx': valid_sstack_value idx (FreshVar idx')). intuition.

           pose proof (IHsb'' (FreshVar idx') idx ops smv maxidx' sb' H_valid_sstack_value_FreshVar_idx' H_valid_sb_2 H_follow) as IHsb''_0.
           intuition.
           
        ** injection H_follow as  H_value H_idx H_sb''.
           rewrite <- H_idx.
           rewrite <- H_sb''.
           rewrite <- H_value.
           split.
           *** apply H_valid_sb_1.
           *** split.
               ***** apply H_valid_sb_2.
               ***** intro H_not_basic_value.
               destruct value; try intuition.
      * apply Nat.eqb_neq in E_n_var.
        assert(H_valid_sstack_value_FreshVar_idx': valid_sstack_value idx (FreshVar var)). simpl. intuition.
        pose proof (IHsb'' (FreshVar var) idx ops smv maxidx' sb' H_valid_sstack_value_FreshVar_idx' H_valid_sb_2 H_follow) as IHsb''_0.
        intuition.
Qed.

Lemma follow_in_smap_suc:
  forall sb sv maxidx ops,
    valid_sstack_value maxidx sv ->
    valid_bindings maxidx sb ops ->
    exists smv maxidx' sb',
      follow_in_smap sv maxidx sb = Some (FollowSmapVal smv maxidx' sb') /\
        is_fresh_var_smv smv = None.
Proof.
  induction sb as [| p sb' IHsb'].
  - intros sv maxidx ops H_valid_sv H_valid_bs.
    destruct sv eqn:E_sv.
    + simpl. exists (SymBasicVal (Val val)). exists maxidx. exists [].
      split; try reflexivity.
    + simpl. exists (SymBasicVal (InVar var)). exists maxidx. exists [].
      split; try reflexivity.
    + simpl in H_valid_bs.
      simpl in H_valid_sv.
      intuition.
  - intros sv maxidx ops H_valid_sv H_valid_bs.
    destruct sv eqn:E_sv.
    + simpl. exists (SymBasicVal (Val val)). exists maxidx. exists (p :: sb'). split; try reflexivity.
    + simpl. exists (SymBasicVal (InVar var)). exists maxidx. exists (p :: sb'). split; try reflexivity.
    + destruct p as [key value].      
      simpl in H_valid_bs.
      destruct H_valid_bs as [H_valid_bs_0 [H_valid_bs_1 H_valid_bs_2]].
      simpl in H_valid_sv.
      simpl.
      destruct (key =? var) eqn:E_key_var.
      * destruct (is_fresh_var_smv value) as [idx'|] eqn:E_is_fresh_var_smv_value.
        ** apply IHsb' with (ops:=ops).
           *** simpl.
               destruct value; try discriminate.
               simpl in E_is_fresh_var_smv_value.
               destruct val; try discriminate.
               injection E_is_fresh_var_smv_value as E_is_fresh_var_smv_value.
               simpl in H_valid_bs_1.
               intuition.
           *** apply H_valid_bs_2.
        ** exists value. exists key. exists sb'.
           split; try reflexivity.
           apply E_is_fresh_var_smv_value.
      * apply IHsb' with (ops:=ops).
        ** simpl.
           apply Nat.eqb_neq in E_key_var. intuition.
        ** apply H_valid_bs_2.
Qed.


(* Elements (using nth_error) of a valid sstack are also valid *)
Lemma valid_sstack_nth:
  forall maxidx sstk sv k,
    valid_sstack maxidx sstk ->
    nth_error sstk k = Some sv ->
      valid_sstack_value maxidx sv.
Proof.
  intros maxidx sstk sv.
  revert sstk.  
  induction sstk as [|a sstk' IHsstk'].
  - intros. destruct k; discriminate.
  - intros k H_valid_sstk H_nth.
    destruct k as [|k'].
    + simpl in H_nth.
      injection H_nth as H_nth.
      rewrite <- H_nth.
      simpl in H_valid_sstk.
      destruct H_valid_sstk as [H_valid_a _].
      apply H_valid_a.
    + simpl in H_nth.
      simpl in H_valid_sstk.
      destruct H_valid_sstk as [_ H_valid_sstk'].
      apply IHsstk' with (k:=k').
      apply H_valid_sstk'.
      apply H_nth.
Qed.

(* firstn of a valid sstack is valid *)
Lemma valid_sstack_firstn:
  forall maxidx sstk k,
    valid_sstack maxidx sstk ->
    valid_sstack maxidx (firstn k sstk).
Proof.
  intros maxidx.
  induction sstk as [|a sstk' IHsstk'].
  - intros; destruct k; reflexivity.
  - intros k H_valid_sstk.
    destruct k as [|k'].
    + reflexivity.
    + simpl in H_valid_sstk.
      destruct H_valid_sstk as [H_valid_a H_valid_sstk'].
      simpl.
      split.
      * apply H_valid_a.
      * apply IHsstk'.
        apply H_valid_sstk'.
Qed.

(* skipn of a valid sstack is valid *)
Lemma valid_sstack_skipn:
  forall maxidx sstk k,
    valid_sstack maxidx sstk ->
    valid_sstack maxidx (skipn k sstk).
Proof.
  intros maxidx.
  induction sstk as [|a sstk' IHsstk'].
  - intros; destruct k; reflexivity.
  - intros k H_valid_sstk.
    simpl in H_valid_sstk.
    destruct H_valid_sstk as [H_valid_a H_valid_sstk'].
    destruct k as [|k'].
    + simpl.
      split.
      * apply H_valid_a.
      * apply H_valid_sstk'.
    + simpl.
      apply IHsstk'.
      apply H_valid_sstk'.
Qed.

(* sv::sstk is valid when sv and sstk are valid *)
Lemma valid_sstack_cons:
  forall maxidx sstk sv,
    valid_sstack maxidx sstk ->
    valid_sstack_value maxidx sv ->
    valid_sstack maxidx (sv::sstk).
Proof.
  intros maxidx sskt sv H_valid_sstk H_valid_sv.
  simpl.
  split.
  - apply H_valid_sv.
  - apply H_valid_sstk.
Qed.

(* a memory update is valid when its ofsset and value are valid *)
Lemma valid_smemory_update_ov:
  forall maxidx soffset svalue,
    valid_sstack_value maxidx soffset ->
    valid_sstack_value maxidx svalue ->
    valid_smemory_update maxidx (U_MSTORE sstack_val soffset svalue) /\
      valid_smemory_update maxidx (U_MSTORE8 sstack_val soffset svalue).

Proof.
  intros maxidx soffset svalue H_valid_offset H_valid_value.
  unfold valid_smemory_update.
  intuition.
Qed.

(* a memory is still valid when extended with a valid update *)
Lemma valid_smemory_when_extended_with_valid_update:
  forall maxidx u smem,
    valid_smemory_update maxidx u ->
    valid_smemory maxidx smem ->
    valid_smemory maxidx (u::smem).
Proof.
  intros maxidx u smem H_valid_u H_valid_smem.
  simpl.
  intuition.
Qed.

(* a storage update is valid when its key and value are valid *)
Lemma valid_sstorage_update_kv:
  forall maxidx skey svalue,
    valid_sstack_value maxidx skey ->
    valid_sstack_value maxidx svalue ->
    valid_sstorage_update maxidx (U_SSTORE sstack_val skey svalue).

Proof.
  intros maxidx soffset svalue H_valid_skey H_valid_value.
  unfold valid_sstorage_update.
  intuition.
Qed.


(* a storage is still valid when extended with a valid update *)
Lemma valid_sstorage_when_extended_with_valid_update:
  forall maxidx u sstrg,
    valid_sstorage_update maxidx u ->
    valid_sstorage maxidx sstrg ->
    valid_sstorage maxidx (u::sstrg).
Proof.
  intros maxidx u sstrg H_valid_u H_valid_sstrg.
  simpl.
  intuition.
Qed.

(* FreshVar idx is valid when idx < maxidx *)
Lemma valid_sstack_val_freshvar:
  forall maxidx idx,
    idx < maxidx ->
    valid_sstack_value maxidx (FreshVar idx).
Proof.
  intros maxidx idx H_id_lt_maxid.
  simpl.
  apply H_id_lt_maxid.
Qed.




(* Lemmas about generation of valid smap values *)

Lemma metapush_valid_smv:
  forall maxidx ops cat v,
    valid_smap_value maxidx ops (SymMETAPUSH cat v).
Proof.
  intros.
  reflexivity.
Qed.

Lemma op_instr_valid_smv:
  forall maxidx ops label nargs args f H1 H2,
    valid_sstack maxidx args ->
    ops label = OpImp nargs f H1 H2 ->
    length args = nargs ->
    valid_smap_value maxidx ops (SymOp label args).
Proof.
  intros maxidx ops label nargs args f H1 H2 H_valid_args H_label H_len.
  simpl.
  unfold valid_stack_op_instr.
  rewrite H_label.
  split.
  - apply H_len.
  - apply H_valid_args.
Qed.


(* a memory update is valid when its key and value are valid *)
Lemma sha3_smv:
  forall maxidx ops smem soffset ssize,
    valid_smemory maxidx smem -> (* The memory is valid *)
    valid_sstack_value maxidx soffset ->
    valid_sstack_value maxidx ssize ->
    valid_smap_value maxidx ops (SymSHA3 soffset ssize smem).
Proof.
  intros maxidx ops smem soffset ssize H_valid_smem H_valid_soffset H_valid_ssize.
  unfold valid_smap_value.
  split.
  - apply H_valid_soffset.
  - split.
    + apply H_valid_ssize.
    + apply H_valid_smem.
Qed.

Lemma symsload_valid_smv:
  forall maxidx skey sstrg ops,
    valid_sstack_value maxidx skey ->
    valid_sstorage maxidx sstrg ->
    valid_smap_value maxidx ops (SymSLOAD skey sstrg).
Proof.
  intros maxidx skey sstrg ops H_valid_skey H_valid_sstrg.
  simpl.
  intuition.
Qed.

Lemma empty_sstrg_is_valid:
  forall maxidx,
    valid_sstorage maxidx empty_sstorage.
Proof.
  intros.
  simpl.
  apply I.
Qed.

Lemma valid_sstack_val_freshvar_Sn_n:
  forall idx,
    valid_sstack_value (S idx) (FreshVar idx).
Proof.
  intros idx.
  simpl.
  intuition.
Qed.



End ValidSymbolicState.
