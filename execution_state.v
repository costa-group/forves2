(**

This file includes definitions related to an execution state (concrete)

**)
 

Require Import bbv.Word.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.sha3.
Import SHA3.

Require Import List.
Import ListNotations.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Arith.
Require Import Nat.
Require Import Bool.
Require Import bbv.Word.
Require Import Coq.NArith.NArith.
Require Import List.
Import ListNotations.

Module ExecutionState.
       
(*** Execution State and its auxiliary data-structures ***)

(* Stack is a list of EVMWord *)
Definition stack : Type := list EVMWord.
Definition empty_stack : stack := [].

(*

Memory is a mapping from N to EVMByte. We do not keep its accessed
size, i.e., don't handle memory expansion, because we don't track gas
consumption. We also use an infinite memory (the domain is N), but
even if the domain is N, we will use addresses that can be represented
using EVMWords only.

*)
Definition memory : Type := N -> EVMByte.
Definition empty_memory : memory := fun _ => BZero.

(*

Storage is a function from N (key) to values EVMWord (value). Similar
to memory, we only use keys that can be represented using EVMWord. We
don't model the warm/cold properties since we don't track gas
consumption, etc.

*)
Definition storage : Type := N -> EVMWord.
Definition empty_storage : storage := fun _ => WZero.

(*

Externals is a structure that we use to encapsulates all
contract/blockchain information, and operations that we don't want to
implement such as KECCAK256 (correctness will be shown for any value
of such operations). The structure is immutable.

*)

Inductive code_info :=
| CodeInfo (size : nat) (content : word size) (hash : EVMWord).

Inductive block_info :=
| BlockInfo (size : nat) (content : word size) (timestamp: EVMWord) (hash : EVMWord).

Inductive sha3_info :=
| SHA3Info (f: sha3_op) (H_sha3: (sha3_op_assumptions f)).

Definition get_sha3_info_op (sha3 :sha3_info) :=
  match sha3 with
  | SHA3Info f _ => f
  end.

Inductive chunk :=
| Chunk (size : nat) (content : word size).

Inductive externals :=
| Exts
  (address : EVMAddr)
  (balance : EVMAddr -> EVMWord)
  (origin : EVMAddr)
  (caller : EVMAddr)
  (callvalue : EVMWord)
  (data: chunk)
  (code : EVMAddr -> code_info ) 
  (gasprice : EVMWord)
  (outdata: chunk)
  (blocks : EVMWord -> block_info)
  (miner : EVMAddr)
  (currblock : EVMWord)
  (gaslimit : EVMWord)
  (chainid : EVMWord)
  (basefee : EVMWord)
  (keccak256 : sha3_info)
  (tags : N -> N -> EVMWord)
  (_extra_2 : nat)
  (_extra_3 : nat)
  (_extra_4 : nat)
  (_extra_5 : nat).


(*
  
  The empty_externals will be used only for the purpose of testing the
  concrete interpreter. It will not be used in any theorem/lemma/etc.

*)
Definition empty_externals : externals :=
 Exts
  AZero (* (address : EVMAddr) *)
  (fun _ => WZero) (* (balance : EVMAddr -> EVMWord) *)
  AZero (* (origin : EVMAddr) *)
  AZero (* (caller : EVMAddr) *)
  WZero (* (callvalue : EVMWord) *)
  (Chunk 0 WO) (* (data: chunk) *)
  (fun _ => CodeInfo 0 WO WZero) (* (code : EVMAddr -> code_info )  *)
  WZero (* (gasprice : EVMWord) *)
  (Chunk 0 WO) (* (outdata: chunk) *)
  (fun _ => BlockInfo 0 WO WZero WZero) (* (blocks : EVMWord -> block_info) *)
  AZero (* (miner : EVMAddr) *)
  WZero (* (currblock : EVMWord) *)
  WZero (* (gaslimit : EVMWord) *)
  WZero (* (chainid : EVMWord) *)
  WZero (* (basefee : EVMWord) *)
  (SHA3Info dummy_sha3 dummy_sha3_assumptions)
  (fun cat v => (NToWord EVMWordSize (cat + v))) (* tags: N -> EVMWord *)
  0 (* (_extra_2 : nat) *)
  0 (* (_extra_3 : nat) *)
  0 (* (_extra_4 : nat) *)
  0. (* (_extra_5 : nat) *)

(* Exts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ *)
 
Definition get_address_exts (c : externals) :=
  match c with
  | Exts x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_balance_exts (c : externals) :=
  match c with
  | Exts _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_origin_exts (c : externals) :=
  match c with
  | Exts _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_caller_exts (c : externals) :=
  match c with
  | Exts _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_callvalue_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_data_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_code_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_gasprice_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_outdata_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_blocks_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_miner_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_currblock_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _ => x
  end.

Definition get_gaslimit_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ _ => x
  end.

Definition get_chainid_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ _ => x
  end.

Definition get_basefee_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ _ => x
  end.

Definition get_keccak256_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _ => x
  end.

Definition get_tags_exts (c : externals) :=
  match c with
  | Exts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ => x
  end.


(*

An execution state consists of a stack, memory, storage and externals.

*)

Inductive state :=
| ExState (stk: stack) (mem: memory) (strg: storage) (exts :externals).

Definition make_st (stk: stack) (mem: memory) (strg: storage) (exts : externals) : state :=
  ExState stk mem strg exts.

(*

The empty state is used just for the sake of testing the concrete
interpreter, it will no be used in any theorem/lemma/etc.

*)
Definition empty_state := make_st empty_stack empty_memory
empty_storage empty_externals.

Definition get_stack_st (st: state) : stack :=
  match st with
  | ExState stk _ _ _ => stk
  end.

Definition set_stack_st (st: state) (stk: stack) : state :=
  match st with
  | ExState _ mem strg exts => ExState stk mem strg exts
  end.

Definition get_memory_st (st: state) : memory :=
  match st with
  | ExState _ mem _ _=> mem
  end.

Definition set_memory_st (st: state) (mem: memory) : state :=
  match st with
  | ExState stk _ strg exts => ExState stk mem strg exts
  end.

Definition get_storage_st (st: state) : storage :=
  match st with
  | ExState _ _ strg _ => strg
  end.

Definition set_store_st (st: state) (strg: storage) : state :=
  match st with
  | ExState stk mem _ exts => ExState stk mem strg exts
  end.

  Definition get_externals_st (st: state) : externals :=
    match st with
    | ExState _ _ _ exts => exts
    end.

Definition set_externals_st (st: state) (exts: externals) : state :=
  match st with
  | ExState stk mem strg _ => ExState stk mem strg exts
  end.


(* 

When two state are equivalent. It is not simply equivalence of
terms because memory and storage are functions, so we need functional
equivalence as well  -- see execution_state_facts.

*)

Definition eq_stack (stk1 stk2: stack) : Prop :=
  stk1 = stk2.

Definition eq_memory (mem1 mem2: memory) : Prop :=
  forall w, mem1 w = mem2 w.

Definition eq_storage (strg1 strg2: storage) : Prop :=
  forall w, strg1 w = strg2 w.

Definition eq_externals (exts1 exts2: externals) : Prop :=
  exts1 = exts2.

Definition eq_execution_states (st1 st2: state) : Prop :=    
  eq_stack (get_stack_st st1) (get_stack_st st2) /\
    eq_memory (get_memory_st st1) (get_memory_st st2) /\
    eq_storage (get_storage_st st1) (get_storage_st st2) /\
    eq_externals (get_externals_st st1) (get_externals_st st2).



End ExecutionState.

