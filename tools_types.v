

Require Import FORVES2.storage_ops_solvers.
Import StorageOpsSolvers.

Require Import FORVES2.memory_ops_solvers.
Import MemoryOpsSolvers.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.


(* Record to encapsulate all comparators, solvers, updaters, etc. -- no used yet *)
Module ToolsTypes.

Module Tools.
Record tools_t : Type := 
  {
    (* stack value comparator -- recieves recursion depth and comparators for mem/strg/sha3 *)
    sstack_val_cmp_ext_2 : sstack_val_cmp_ext_2_t;
    H_sstack_val_cmp_ext_2_snd: safe_sstack_value_cmp_wrt_others sstack_val_cmp_ext_2;
    H_sstack_val_cmp_ext_2_d0_snd: sstack_val_cmp_fail_for_d_eq_0 sstack_val_cmp_ext_2;

    (* memory comparator -- recieves sstack_val_cmp_ext_1_t *)
    smemory_cmp_ext : smemory_cmp_ext_t;
    H_smemory_cmp_ext_snd: safe_smemory_cmp_ext_wrt_sstack_value_cmp smemory_cmp_ext;

    (* storage comparator -- recieves sstack_val_cmp_ext_1_t *)
    sstorage_cmp_ext : sstorage_cmp_ext_t;
    H_sstorage_cmp_ext_snd: safe_sstorage_cmp_ext_wrt_sstack_value_cmp sstorage_cmp_ext;

    (* sha3 comparator -- recieves sstack_val_cmp_ext_1_t *)
    sha3_cmp_ext : sha3_cmp_ext_t;
    H_sha3_cmp_ext_snd: safe_sha3_cmp_ext_wrt_sstack_value_cmp sha3_cmp_ext;

    (* stack value comparator -- recieves recursion depth *)
    sstack_val_cmp_ext_1 : sstack_val_cmp_ext_1_t;
    H_sstack_val_cmp_ext_1_snd: safe_sstack_val_cmp_ext_1 sstack_val_cmp_ext_1;

    (* mload solver -- recieves sstack_val_cmp_ext_1_t *)
    mload_solver_ext : mload_solver_ext_type;
    H_mload_solver_ext_snd : mload_solver_ext_snd mload_solver_ext;

    (* sload solver -- recieves sstack_val_cmp_ext_1_t *)
    sload_solver_ext : sload_solver_ext_type;
    H_sload_solver_ext_snd : sload_solver_ext_snd sload_solver_ext;

    (* memory updater -- recieves sstack_val_cmp_ext_1_t *)
    smemory_updater_ext : smemory_updater_ext_type;
    H_smemory_updater_ext_snd : smemory_updater_ext_snd smemory_updater_ext;

    (* storage updater -- recieves sstack_val_cmp_ext_1_t *)
    sstorage_updater_ext : sstorage_updater_ext_type;
    H_sstorage_updater_ext_snd : sstorage_updater_ext_snd sstorage_updater_ext;

    (* mload solver *)
    mload_solver : mload_solver_type;
    H_mload_solver_snd : mload_solver_snd mload_solver;

    (* sload solver  *)
    sload_solver : sload_solver_type;
    H_sload_solver_snd : sload_solver_snd sload_solver;

    (* memory updater *)
    smemory_updater : smemory_updater_type;
    H_smemory_updater_snd : smemory_updater_snd smemory_updater;

    (* storage updater *)
    sstorage_updater : sstorage_updater_type;
    H_sstorage_updater_snd : sstorage_updater_snd sstorage_updater;
  }.


End Tools.

Module Tools_1.
Record tools_1_t : Type := 
  {
    tools : Tools.tools_t;

    (* stack value comparator *)
    sstack_val_cmp : sstack_val_cmp_t;
    H_sstack_val_cmp_snd: safe_sstack_val_cmp sstack_val_cmp;

    (* memory comparator *)
    smemory_cmp : smemory_cmp_t;
    H_smemory_cmp_snd: safe_smemory_cmp smemory_cmp;

    (* storage comparator *)
    sstorage_cmp : sstorage_cmp_t;
    H_sstorage_cmp_snd: safe_sstorage_cmp sstorage_cmp;
  }.
End Tools_1.

End ToolsTypes.

      
