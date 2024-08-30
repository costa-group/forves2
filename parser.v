From Coq Require Import Numbers.DecimalString.
From Coq Require Import Numbers.HexadecimalNat.
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
Require Import Hexadecimal HexadecimalFacts Arith.
Require Import Coq.NArith.NArith.
From Coq Require Import Lists.List. Import ListNotations.


Require Import bbv.Word.

Require Import FORVES2.program.
Import Program.

Require Import FORVES2.block_equiv_checker.
Import BlockEquivChecker.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Require Import bbv.Word.


Module Parser.

  
(* ################################################################# *)
(** * Internals *)

(* ================================================================= *)
(** ** Lexical Analysis *)



Definition white_chars := [32 (* space *); 9 (* tab *); 10 (* linefeed *); 13 (* Carriage return. *)]%N.

Definition delim_chars := [28 (* ( *); 29 (* ) *); 91 (* [ *); 93 (* ]. *); 44 (* , *); 43 (* + *); 60 (* < *); 61 (* = *) ]%N.

Definition isWhite (c : ascii) : bool :=
  let n := N_of_ascii c in
  existsb (fun m => (n =? m)%N) white_chars.

Definition isDelimiter (c : ascii) : bool :=
  let n := N_of_ascii c in
  existsb (fun m => (n =? m)%N) delim_chars.

Inductive chartype := white | other | delim.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isDelimiter c then
         delim
       else
         other.


Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.


Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, white, _    =>
        tk ++ (tokenize_helper white [] xs')

    | _, delim, _    =>
        tk ++ [[x]] ++ (tokenize_helper white [] xs')
           
    | other,other,x  =>
        tokenize_helper other (x::acc) xs'
                        
    | _,tp,x         =>
        tk ++ (tokenize_helper tp [x] xs')
           
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Fixpoint uint_to_N (d:uint) : N :=
  match d with
  | Nil => 0x0
  | D0 d => 0x10 * uint_to_N d
  | D1 d => 0x1 + 0x10 * uint_to_N d
  | D2 d => 0x2 + 0x10 * uint_to_N d
  | D3 d => 0x3 + 0x10 * uint_to_N d
  | D4 d => 0x4 + 0x10 * uint_to_N d
  | D5 d => 0x5 + 0x10 * uint_to_N d
  | D6 d => 0x6 + 0x10 * uint_to_N d
  | D7 d => 0x7 + 0x10 * uint_to_N d
  | D8 d => 0x8 + 0x10 * uint_to_N d
  | D9 d => 0x9 + 0x10 * uint_to_N d
  | Da d => 0xa + 0x10 * uint_to_N d
  | Db d => 0xb + 0x10 * uint_to_N d
  | Dc d => 0xc + 0x10 * uint_to_N d
  | Dd d => 0xd + 0x10 * uint_to_N d
  | De d => 0xe + 0x10 * uint_to_N d
  | Df d => 0xf + 0x10 * uint_to_N d
  end.

Fixpoint parseHexNumber' (x : list ascii) (acc : uint) :=
  match x with
    | [] => Some acc
    | "0"%char::xs => parseHexNumber' xs (D0 acc)
    | "1"%char::xs => parseHexNumber' xs (D1 acc)
    | "2"%char::xs => parseHexNumber' xs (D2 acc)
    | "3"%char::xs => parseHexNumber' xs (D3 acc)
    | "4"%char::xs => parseHexNumber' xs (D4 acc)
    | "5"%char::xs => parseHexNumber' xs (D5 acc)
    | "6"%char::xs => parseHexNumber' xs (D6 acc)
    | "7"%char::xs => parseHexNumber' xs (D7 acc)
    | "8"%char::xs => parseHexNumber' xs (D8 acc)
    | "9"%char::xs => parseHexNumber' xs (D9 acc)
    | "a"%char::xs => parseHexNumber' xs (Da acc)
    | "A"%char::xs => parseHexNumber' xs (Da acc)
    | "b"%char::xs => parseHexNumber' xs (Db acc)
    | "B"%char::xs => parseHexNumber' xs (Db acc)
    | "c"%char::xs => parseHexNumber' xs (Dc acc)
    | "C"%char::xs => parseHexNumber' xs (Dc acc)
    | "d"%char::xs => parseHexNumber' xs (Dd acc)
    | "D"%char::xs => parseHexNumber' xs (Dd acc)
    | "e"%char::xs => parseHexNumber' xs (De acc)
    | "E"%char::xs => parseHexNumber' xs (De acc)
    | "f"%char::xs => parseHexNumber' xs (Df acc)
    | "F"%char::xs => parseHexNumber' xs (Df acc)
    | _ => None
  end.

Definition parseHexNumber (x : string) : option N :=
  let xl := (list_of_string x) in
  match xl with
  | "0"%char::"x"%char::xs =>
      match (parseHexNumber' xs Nil) with
      | None => None
      | Some n => Some (uint_to_N n)
      end
  | _ => None
  end.


Fixpoint parseDecNumber_N' (x : list ascii) (acc : N) :=
  match x with
  | [] => Some acc
  | d::ds => let n := N_of_ascii d in
             if (andb (N.leb 48%N n) (N.leb n 57%N)) then
               parseDecNumber_N' ds (10*acc+(n-48)%N)
             else None
  end.

Definition parseDecNumber_N (x : string) : option N :=
  parseDecNumber_N' (list_of_string x) 0%N.


Definition parseDecNumber (x : string) : option nat :=
  match parseDecNumber_N x with
  | Some n => Some (N.to_nat n)
  | None => None
  end.                        

Definition parseDecNumber' (x : list ascii) : option nat :=
  match parseDecNumber_N' x 0%N with
  | Some n => Some (N.to_nat n)
  | None => None
  end.                        

Definition is_push (s : string) : option nat :=
  match (list_of_string s) with
  | "P"%char::"U"%char::"S"%char::"H"%char::xs => match (parseDecNumber' xs) with
                                                  | None => None
                                                  | Some n => if (andb (Nat.leb 1 n) (Nat.leb n 32)) then Some n else None
                                                  end                                                 
  | _ => None
  end.

Definition is_metapush (s : string) : bool :=
  match s with
  | "METAPUSH"%string => true
  | _ => false
  end.

Definition is_dup (s : string) : option nat :=
  match (list_of_string s) with
  | "D"%char::"U"%char::"P"%char::xs => match (parseDecNumber' xs) with
                                        | None => None
                                        | Some n => if (andb (Nat.leb 1 n) (Nat.leb n 16)) then Some n else None
                                        end                                                 
  | _ => None
  end.

Definition is_swap (s : string) : option nat :=
  match (list_of_string s) with
  | "S"%char::"W"%char::"A"%char::"P"%char::xs => match (parseDecNumber' xs) with
                                                  | None => None
                                                  | Some n => if (andb (Nat.leb 1 n) (Nat.leb n 16)) then Some n else None
                                                  end                                                 
  | _ => None
  end.

Definition parse_stack_op_instr (s : string) : option stack_op_instr :=
  match s with
  | "ADD"%string => Some ADD
  | "MUL"%string => Some MUL
  | "SUB"%string => Some SUB
  | "DIV"%string => Some DIV
  | "SDIV"%string => Some SDIV
  | "MOD"%string => Some MOD
  | "SMOD"%string => Some SMOD
  | "ADDMOD"%string => Some ADDMOD
  | "MULMOD"%string => Some MULMOD
  | "EXP"%string => Some EXP
  | "SIGNEXTEND"%string => Some SIGNEXTEND
  | "LT"%string => Some LT
  | "GT"%string => Some GT
  | "SLT"%string => Some SLT
  | "SGT"%string => Some SGT
  | "EQ"%string => Some EQ
  | "ISZERO"%string => Some ISZERO
  | "AND"%string => Some AND
  | "OR"%string => Some OR
  | "XOR"%string => Some XOR
  | "NOT"%string => Some NOT
  | "BYTE"%string => Some BYTE
  | "SHL"%string => Some SHL
  | "SHR"%string => Some SHR
  | "SAR"%string => Some SAR
  | "ADDRESS"%string => Some ADDRESS
  | "BALANCE"%string => Some BALANCE
  | "ORIGIN"%string => Some ORIGIN
  | "CALLER"%string => Some CALLER
  | "CALLVALUE"%string => Some CALLVALUE
  | "CALLDATALOAD"%string => Some CALLDATALOAD
  | "CALLDATASIZE"%string => Some CALLDATASIZE
  | "CODESIZE"%string => Some CODESIZE
  | "GASPRICE"%string => Some GASPRICE
  | "EXTCODESIZE"%string => Some EXTCODESIZE
  | "RETURNDATASIZE"%string => Some RETURNDATASIZE
  | "EXTCODEHASH"%string => Some EXTCODEHASH
  | "BLOCKHASH"%string => Some BLOCKHASH
  | "COINBASE"%string => Some COINBASE
  | "TIMESTAMP"%string => Some TIMESTAMP
  | "NUMBER"%string => Some NUMBER
  | "DIFFICULTY"%string => Some DIFFICULTY
  | "GASLIMIT"%string => Some GASLIMIT
  | "CHAINID"%string => Some CHAINID
  | "SELFBALANCE"%string => Some SELFBALANCE
  | "BASEFEE"%string => Some BASEFEE
  | "GAS"%string => Some GAS
  | "JUMPI"%string => Some JUMPI
  | _ => None
  end.

Definition parse_non_stack_op_instr (s : string) : option instr :=
  match s with
  | "POP"%string => Some POP
  | "MLOAD"%string => Some MLOAD
  | "MSTORE"%string => Some MSTORE
  | "MSTORE8"%string => Some MSTORE8
  | "SLOAD"%string => Some SLOAD
  | "SSTORE"%string => Some SSTORE
  | "SHA3"%string => Some SHA3
  | "KECCAK256"%string => Some KECCAK256
  | _ => None
  end.

Definition parse_non_push_instr (s : string) : option instr :=
  match (is_dup s) with
  | Some n => Some (DUP n)
  | None =>
      match (is_swap s) with
      | Some n => Some (SWAP n)
      | None =>
          match parse_non_stack_op_instr s with
          | Some i => Some i
          | None =>
              match parse_stack_op_instr s with
              | Some i => Some (OpInstr i)
              | None => None
              end
          end
      end
  end.

Fixpoint parse_block' (l : list string) : option block :=
  match l with
  | [] => Some []
  | x::xs => match (is_push x) with
             |  Some n =>
                  match xs with
                  | y::ys =>
                      match (parseHexNumber y) with
                      |  None => None
                      |  Some v =>
                           match (parse_block' ys) with
                           | None => None
                           | Some bs => Some ((PUSH n v)::bs)
                           end
                      end
                  | _ => None
                  end
             | None =>
                 match (is_metapush x) with
                 | true =>
                     match xs with
                     | z::y::ys =>
                         match (parseHexNumber y) with
                         |  None => None
                         |  Some v =>
                              match (parseDecNumber z) with
                              | None => None
                              | Some cat =>
                                  match (parse_block' ys) with
                                  | None => None
                                  | Some bs => Some ((METAPUSH (N.of_nat cat) v)::bs)
                                  end
                              end
                         end
                     | _ => None
                     end
                 | false =>
                           match (parse_non_push_instr x) with
                           | None => None
                           | Some i => match (parse_block' xs) with
                                       | None => None
                                       | Some bs => Some (i::bs)
                                       end
                           end
                       end
             end               
  end.

Definition parse_block (block_str : string) : option block :=
  parse_block' (tokenize block_str).


Definition str_to_opt (s : string) : option available_optimization_step :=
  match s with
  | "eval"%string => Some OPT_eval
  | "add_zero"%string => Some OPT_add_zero
  | "not_not"%string => Some OPT_not_not
  | "and_and"%string => Some OPT_and_and
  | "and_origin"%string => Some OPT_and_origin
  | "mul_shl"%string => Some OPT_mul_shl
  | "div_shl"%string => Some OPT_div_shl
  | "shr_zero_x"%string => Some OPT_shr_zero_x
  | "shr_x_zero"%string => Some OPT_shr_x_zero
  | "eq_zero"%string => Some OPT_eq_zero
  | "sub_x_x"%string => Some OPT_sub_x_x
  | "and_zero"%string => Some OPT_and_zero
  | "div_one"%string => Some OPT_div_one
  | "lt_x_one"%string => Some OPT_lt_x_one
  | "gt_one_x"%string => Some OPT_gt_one_x
  | "and_address"%string => Some OPT_and_address
  | "mul_one"%string => Some OPT_mul_one
  | "iszero_gt"%string => Some OPT_iszero_gt
  | "eq_iszero"%string => Some OPT_eq_iszero
  | "and_caller"%string => Some OPT_and_caller
  | "iszero3"%string => Some OPT_iszero3
  | "add_sub"%string => Some OPT_add_sub
  | "shl_zero_x"%string => Some OPT_shl_zero_x
  | "sub_zero"%string => Some OPT_sub_zero
  | "shl_x_zero"%string => Some OPT_shl_x_zero
  | "mul_zero"%string => Some OPT_mul_zero
  | "div_x_x"%string => Some OPT_div_x_x
  | "div_zero"%string => Some OPT_div_zero
  | "mod_one"%string => Some OPT_mod_one
  | "mod_zero"%string => Some OPT_mod_zero
  | "mod_x_x"%string => Some OPT_mod_x_x
  | "exp_x_zero"%string => Some OPT_exp_x_zero
  | "exp_x_one"%string => Some OPT_exp_x_one
  | "exp_one_x"%string => Some OPT_exp_one_x
  | "exp_zero_x"%string => Some OPT_exp_zero_x
  | "exp_two_x"%string => Some OPT_exp_two_x
  | "gt_zero_x"%string => Some OPT_gt_zero_x
  | "gt_x_x"%string => Some OPT_gt_x_x
  | "lt_x_zero"%string => Some OPT_lt_x_zero
  | "lt_x_x"%string => Some OPT_lt_x_x
  | "eq_x_x"%string => Some OPT_eq_x_x
  | "iszero_sub"%string => Some OPT_iszero_sub
  | "iszero_lt"%string => Some OPT_iszero_lt
  | "iszero_xor"%string => Some OPT_iszero_xor
  | "iszero2_gt"%string => Some OPT_iszero2_gt
  | "iszero2_lt"%string => Some OPT_iszero2_lt
  | "iszero2_eq"%string => Some OPT_iszero2_eq
  | "xor_x_x"%string => Some OPT_xor_x_x
  | "xor_zero"%string => Some OPT_xor_zero
  | "xor_xor"%string => Some OPT_xor_xor
  | "or_or"%string => Some OPT_or_or
  | "or_and"%string => Some OPT_or_and
  | "and_or"%string => Some OPT_and_or
  | "and_not"%string => Some OPT_and_not
  | "or_not"%string => Some OPT_or_not
  | "or_x_x"%string => Some OPT_or_x_x
  | "and_x_x"%string => Some OPT_and_x_x
  | "or_zero"%string => Some OPT_or_zero
  | "or_ffff"%string => Some OPT_or_ffff
  | "and_ffff"%string => Some OPT_and_ffff
  | "and_coinbase"%string => Some OPT_and_coinbase
  | "balance_address"%string => Some OPT_balance_address
  | "slt_x_x"%string => Some OPT_slt_x_x
  | "sgt_x_x"%string => Some OPT_sgt_x_x
  | "mem_solver"%string => Some OPT_mem_solver
  | "strg_solver"%string => Some OPT_strg_solver
  | "jumpi_neq"%string => Some OPT_jumpi_neq
  | "lt_ctx"%string => Some OPT_lt_ctx
  | "gt_ctx"%string => Some OPT_gt_ctx
  | "eq_ctx"%string => Some OPT_eq_ctx
  | _ => None
  end.

Fixpoint strs_to_opts (l : list string) : option list_opt_steps :=
  match l with
  | [] => Some []
  | x::xs => match (str_to_opt x) with
             | None => None
             | Some o => match (strs_to_opts xs) with
                         | None => None
                         | Some os => Some (o::os)
                         end
             end
  end.


Definition parse_opts_arg (opts_to_apply : list string) : option list_opt_steps :=
  match opts_to_apply with
  | ["none"%string] => Some []
  | ["all"%string] => Some all_optimization_steps
  | ["all_size"%string] => Some all_optimization_steps'
  | _ => strs_to_opts opts_to_apply
  end.

Definition parse_memory_updater (s: string) :=
  match s with
  | "trivial"%string => Some SMemUpdater_Trivial
  | "basic"%string => Some SMemUpdater_Basic
  | _ => None
  end.

Definition parse_storage_updater (s: string) :=
  match s with
  | "trivial"%string => Some SStrgUpdater_Trivial
  | "basic"%string => Some SStrgUpdater_Basic
  | _ => None
  end.

Definition parse_mload_solver (s: string) :=
  match s with
  | "trivial"%string => Some MLoadSolver_Trivial
  | "basic"%string => Some MLoadSolver_Basic
  | _ => None
  end.

Definition parse_sload_solver (s: string) :=
  match s with
  | "trivial"%string => Some SLoadSolver_Trivial
  | "basic"%string => Some SLoadSolver_Basic
  | _ => None
  end.

Definition parse_sstack_value_cmp (s: string) :=
  match s with
  | "trivial"%string => Some SStackValCmp_Trivial
  | "basic"%string => Some SStackValCmp_Basic
  | "basic_w_eq_chk"%string => Some SStackValCmp_Basic_w_eq_chk
  | _ => None
  end.

Definition parse_memory_cmp (s: string) :=
  match s with
  | "trivial"%string => Some SMemCmp_Trivial
  | "basic"%string => Some SMemCmp_Basic
  | "po"%string => Some SMemCmp_PO
  | _ => None
  end.

Definition parse_storage_cmp (s: string) :=
  match s with
  | "trivial"%string => Some SStrgCmp_Trivial
  | "basic"%string => Some SStrgCmp_Basic
  | "po"%string => Some SStrgCmp_PO
  | _ => None
  end.

Definition parse_sha3_cmp (s: string) :=
  match s with
  | "trivial"%string => Some SHA3Cmp_Trivial
  | "basic"%string => Some SHA3Cmp_Basic
  | _ => None
  end.

Definition parse_imp_chkr (s: string) :=
  match s with
  | "dummy"%string => Some ImpChkr_Dummy
  | "syntactic"%string => Some ImpChkr_Syntactic
  | "oct"%string => Some ImpChkr_Oct
  | _ => None
  end.

Definition parser_type (A : Type) : Type := option (A*(list string)).


Definition parse_sstack_val (s: string) : option sstack_val :=
  match (parseHexNumber s) with
  | None => match (list_of_string s) with
            | "v"%char::cs => match (parseDecNumber' cs) with
                              | None => None
                              | Some n => Some (InVar n)
                              end
            | "e"%char::cs => match (parseDecNumber' cs) with
                              | None => None
                              | Some n => Some (FreshVar n)
                              end
            | _ => None
            end
  | Some v => Some (Val (NToWord EVMWordSize v))
  end.

Fixpoint parse_stack' (l: list string) : sstack * (list string) :=
  match l with
  | x::xs =>
      match parse_sstack_val x with
      | None => ([],l)
      | Some xv =>
          match xs with
          | ","%string::xs' =>
              match parse_stack' xs' with
              | (vl,xs'') => (xv::vl,xs'')
              end
          | _ => ([xv],xs)
          end
      end
  | _ => ([],l)
  end.

Definition parse_stack (s: list string) : parser_type sstack:=
  match s with
  | "["%string::xs =>
      match parse_stack' xs with
      | (stk, xs') =>
          match xs' with
          | "]"%string::xs'' => Some (stk,xs'')
          | _ => None
          end
      end
  | _ => None
  end.



Fixpoint parse_memory' (l: list string) : smemory * (list string) :=
  match l with
  | store_type::offset::value::xs =>
      match 
        (match parse_sstack_val offset with
        | None => None
        | Some offsetv =>
            match parse_sstack_val value with
            | None => None
            | Some valuev =>
                match store_type with
                | "MSTORE"%string => Some (U_MSTORE sstack_val offsetv valuev)
                | "MSTORE8"%string => Some (U_MSTORE8 sstack_val offsetv valuev)
                | _ => None
                end
            end
        end)
      with
      | Some u =>
          match xs with
          | ","%string::xs' =>
              match parse_memory' xs' with
              |  (us,xs'') => (u::us,xs'')
              end
          | _ => ([u],xs)
          end
      | None => ([],l)
      end
  | _ => ([],l)
  end.

Definition parse_memory (s: list string) : parser_type smemory :=
  match s with
  | "["%string::xs =>
      match parse_memory' xs with
      | (mem, xs') =>
          match xs' with
          | "]"%string::xs'' => Some (mem,xs'')
          | _ => None
          end
      end
  | _ => None
  end.


Fixpoint parse_storage' (l: list string) : sstorage * (list string) :=
  match l with
  | "SSTORE"%string::key::value::xs =>
      match parse_sstack_val key with
      | Some keyv =>
          match parse_sstack_val value with
          | Some valuev =>
              let u := (U_SSTORE sstack_val keyv valuev) in
              match xs with
              | ","%string::xs' =>
                  match parse_storage' xs' with
                  | (us,xs'') => (u::us,xs'')
                  end
              | _ => ([u],xs)
              end
          | None => ([], l)
          end
      | None => ([], l)
      end
  | _ => ([],l)
  end.

Definition parse_storage (s: list string) : parser_type sstorage :=
  match s with
  | "["%string::xs =>
      match parse_storage' xs with
      | (strg, xs') =>
          match xs' with
          | "]"%string::xs'' => Some (strg,xs'')
          | _ => None
          end
      end
  | _ => None
  end.

Definition parse_sbinding (l: list string) : parser_type sbinding :=
  match l with
  | id::"="%string::l' =>
      match parseDecNumber id with
      | Some n =>
          match l' with
          | "BV"%string::val::xs =>
              match parse_sstack_val val with
              | None => None
              | Some valv => Some ((n,SymBasicVal valv),xs)
              end
          | "MP"%string::cat::val::xs =>
              match parseDecNumber_N cat with
              | None => None
              | Some catv =>
                  match parseDecNumber_N val with
                  | None => None
                  | Some valv => Some ((n,SymMETAPUSH catv valv),xs)
                  end
              end
          | "OP"%string::label::xs =>
              match parse_stack_op_instr label with
              | None => None
              | Some labelv =>
                  match parse_stack xs with
                  | None => None
                  | Some (args,xs') => Some ((n,SymOp labelv args),xs')
                  end
              end
          | "ML"%string::offset::xs =>
              match parse_sstack_val offset with
              | None => None
              | Some offsetv =>
                  match parse_memory xs with
                  | None => None
                  | Some (mem,xs') => Some ((n,SymMLOAD offsetv mem),xs')
                  end
              end
          | "SL"%string::key::xs =>
              match parse_sstack_val key with
              | None => None
              | Some keyv =>
                  match parse_storage xs with
                  | None => None
                  | Some (strg,xs') => Some ((n,SymSLOAD keyv strg),xs')
                  end
              end
          | "SHA3"%string::offset::size::xs =>
              match parse_sstack_val offset with
              | None => None
              | Some offsetv =>
                  match parse_sstack_val size with
                  | None => None
                  | Some sizev =>
                      match parse_memory xs with
                      | None => None
                      | Some (mem,xs') => Some ((n,SymSHA3 offsetv sizev mem),xs')
                      end
                  end
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Fixpoint parse_sbindings' (d: nat) (l: list string) : sbindings*(list string) :=
  match d with
  | 0 => ([], l)
  | S d' =>
      match (parse_sbinding l) with
      | Some (b,l') =>
          match l' with
          | ","%string::l'' =>
              match parse_sbindings' d' l'' with
              | (vl'',l''') => (b::vl'',l''')
              end
          | _ => ([b],l')
          end
      | None => ([], l)
      end
  end.
    
Definition parse_sbindings (d: nat) (l: list string) : parser_type sbindings :=
  match l with
  | "["%string::xs =>
      match parse_sbindings' d xs with
      | (bs, xs') =>
          match xs' with
          | "]"%string::xs'' => Some (bs,xs'')
          | _ => None
          end
      end
  | _ => None
  end.

Definition parse_smap (d: nat) (l: list string) : parser_type smap :=
  match parse_sbindings d l with
  | None => None
  | Some (bs,l') => Some ((SymMap (length bs) bs), l')
  end.


Definition parse_literal (l: list string) : parser_type cliteral :=
  match l with
  | a::"+"%string::b::xs =>
      let al := list_of_string a in
      match al with
      | "v"%char::cs =>
          match (parseDecNumber' cs) with
          | Some n =>
              match parseDecNumber_N b with
              | Some d => Some ((C_VAR_DELTA n d),xs)
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | a::xs =>
      let al := list_of_string a in
      match al with
      | "v"%char::cs =>
          match (parseDecNumber' cs) with
          | Some n => Some ((C_VAR n),xs)
          | None => None
          end
      | _ =>
          match parseDecNumber_N a with
          | Some n => Some ((C_VAL n),xs)
          | None => None
          end
      end
  | _ => None
  end.

Definition parse_constraint (l: list string) : parser_type constraint :=
  match parse_literal l with
  | Some (a,l') =>
      match
        (match l' with
              | "<"%string::"="%string::xs  => Some ("<="%string,xs)
              | "<"%string::xs =>Some ("<"%string,xs)
              | "="%string::xs  => Some ("="%string,xs)
         | _ => None
         end)
      with
      | Some (op,l'') =>
          match parse_literal l'' with
          | Some (b,l''') =>
              match op with
              | "<="%string  => Some ((C_LE a b),l''')
              | "<"%string => Some ((C_LT a b),l''')
              | "="%string  => Some ((C_EQ a b),l''')
              | _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Fixpoint parse_conjunction' (d: nat) (l: list string) : conjunction*(list string) :=
  match d with
  | 0 => ([],l)
  | S d' =>
      match (parse_constraint l) with
      | Some (c,l') =>
          match l' with
          | ","%string::l'' =>
              match  parse_conjunction' d' l'' with
              | (vl'',l''') => (c::vl'',l''')
              end
          | _ => ([c],l')
          end
      | None => ([],l)
      end
  end.

Definition parse_conjunction (d: nat) (l: list string) : parser_type conjunction :=
  match l with
  | "["%string::xs =>
      match parse_conjunction' d xs with
      | (cs, xs') =>
          match xs' with
          | "]"%string::xs'' => Some (cs,xs'')
          | _ => None
          end
      end
  | _ => None
  end.

Fixpoint parse_disjunction' (d: nat) (l: list string) : disjunction*(list string) :=
  match d with
  | 0 => ([],l)
  | S d' =>
      match (parse_conjunction d l) with
      | Some (c,l') =>
          match l' with
          | ","%string::l'' =>
              match  parse_disjunction' d' l'' with
              | (vl'',l''') => (c::vl'',l''')
              end
          | _ => ([c],l')
          end
      | None => ([],l)
      end
  end.

Definition parse_disjunction (d: nat) (l: list string) : parser_type disjunction :=
  match l with
  | "["%string::xs =>
      match parse_disjunction' d xs with
      | (ds, xs') =>
          match xs' with
          | "]"%string::xs'' => Some (ds,xs'')
          | _ => None
          end
      end
  | _ => None
  end.


Definition parse_init_state_type_1 (d: nat) (l: list string) : option (constraints * sstate) :=
  match l with
  | [] => None
  | x::xs =>
      match (parseDecNumber x) with
      | Some k_nat =>
          let sst := gen_empty_sstate_from_stk_height k_nat in
          match xs with
          | [] => Some ([], sst)
          | _::_ =>
              match parse_disjunction d xs with
              | Some (ds, xs') =>
                  match xs' with
                  | [] => Some (ds,sst)
                  | _ => None
                  end
              | None => None
              end
          end
      | _ => None
      end
  end.

Definition parse_init_state_type_2 (d: nat) (l: list string) : option (constraints * sstate) :=
  match parse_stack l with
    | None => None
    | Some (sstk, l') =>
        match parse_memory l' with
        | None => None
        | Some (smem, l'') =>
            match parse_storage l'' with
            | None => None
            | Some (sstrg, l''') =>
                match parse_smap d l''' with
                | None => None
                | Some (smap, l'''') =>
                    let sst := make_sst sstk smem sstrg empty_sexternals smap in
                    match l'''' with 
                    | [] => Some ([], sst)
                    | _::_ =>
                        match parse_disjunction d l'''' with
                        | None => None
                        | Some (ds, l''''') =>
                            match l''''' with 
                            | [] => Some (ds, sst)
                            | _::_ => None
                            end
                        end
                    end
                end
            end
        end
  end.
    
                            
                
Definition parse_init_state (init_state: string) : option (constraints * sstate) :=
  let l := tokenize init_state in
  let d := length l in
  match parse_init_state_type_1 d l with
  | Some (cs,sst) => Some (cs,sst)
  | None =>
      match parse_init_state_type_2 d l with
      | Some (cs,sst) => Some (cs,sst)
      | None => None
      end
  end.
    
  
Definition block_eq (memory_updater storage_updater mload_solver sload_solver sstack_value_cmp memory_cmp storage_cmp sha3_cmp imp_chkr opt_step_rep opt_pipeline_rep: string) (opts_to_apply : list string) :
  option (string -> string -> string -> option bool) :=
  match (parse_memory_updater memory_updater) with
  | None => None
  | Some memory_updater_tag =>
      match (parse_storage_updater storage_updater) with
      | None => None
      | Some storage_updater_tag =>
          match (parse_mload_solver mload_solver) with
          | None => None
          | Some mload_solver_tag =>
              match (parse_sload_solver sload_solver) with
              | None => None
              | Some sload_solver_tag =>
                  match (parse_sstack_value_cmp sstack_value_cmp) with
                  | None => None
                  | Some sstack_value_cmp_tag =>
                      match (parse_memory_cmp memory_cmp) with
                      | None => None
                      | Some memory_cmp_tag =>
                          match (parse_storage_cmp storage_cmp) with
                          | None => None
                          | Some storage_cmp_tag =>
                              match (parse_sha3_cmp sha3_cmp) with
                              | None => None
                              | Some sha3_cmp_tag =>
                                  match (parse_imp_chkr imp_chkr) with
                                  | None => None
                                  | Some imp_chkr_tag =>
                                      match (parseDecNumber opt_step_rep) with
                                      | None => None
                                      | Some opt_step_rep_nat =>
                                          match (parseDecNumber opt_pipeline_rep) with
                                          | None => None
                                          | Some opt_pipeline_rep_nat =>
                                              match (parse_opts_arg opts_to_apply) with
                                              | None => None
                                              | Some optimization_steps =>
                                                  let chkr_lazy :=
                                                    evm_eq_block_chkr_lazy memory_updater_tag storage_updater_tag mload_solver_tag sload_solver_tag sstack_value_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag imp_chkr_tag optimization_steps opt_step_rep_nat opt_pipeline_rep_nat in
                                                  Some (fun (p_opt p init_state : string) => 
                                                          match (parse_block p_opt) with
                                                          | None => None
                                                          | Some b1 => 
                                                              match (parse_block p) with
                                                              | None => None
                                                              | Some b2 =>
                                                                  match parse_init_state init_state with
                                                                  | None => None
                                                                  | Some (cs,sst) => Some (chkr_lazy cs sst b1 b2)
                                                                  end
                                                              end
                                                          end)
                                              end
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end
  end.


End Parser.
 
