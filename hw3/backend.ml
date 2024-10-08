(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge



(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt:ctxt) (dest:X86.operand) : Ll.operand -> ins =
  fun (op: Ll.operand) ->
      match ctxt with
      | { tdecls : (lbl * ty) list; layout : layout; } ->
        let temp_reg = Reg R10 in
        match op with
        | Null -> (Movq, [Imm (Lit 0L); dest])
        | Const x -> (Movq, [Imm (Lit x); dest])
        | Gid lbl ->
          let mgld_lbl = Platform.mangle lbl in
          (Leaq, [Ind3 ((Lbl mgld_lbl), Rip); dest])
        | Id lbl -> (Movq, [(lookup layout lbl); temp_reg])

let compile_operand_full (ctxt:ctxt) (dest:X86.operand) (src:Ll.operand) : ins list =
  let temp_reg = Reg R10 in
  match src with
  | Id _ -> [(compile_operand ctxt dest src); (Movq, [temp_reg; dest])]
  | _ -> [compile_operand ctxt dest src]

(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)




(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls:(tid * ty) list) (t:Ll.ty) : int =
match t with
| Void | I8 | Fun (_, _) -> 0
| I1 | I64 | Ptr _ -> 8
| Struct l -> List.fold_left (+) 0 (List.map (size_ty tdecls) l)
| Array (n, t') -> n * (size_ty tdecls t')
| Namedt lbl -> size_ty tdecls (lookup tdecls lbl)

(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let rec struct_index (ctxt:ctxt) (t: Ll.ty list) (counter: int64) : int64 = if counter = 0L then 0L else
  match t with
    |[] -> 0L
    |(x::xs) -> Int64.add (Int64.of_int (size_ty ctxt.tdecls x)) (struct_index ctxt xs (Int64.sub counter 1L))
    |_ -> failwith "invalid struct_index"

let rec helper_gep (ctxt:ctxt) (t:Ll.ty) (path: Ll.operand list) : ins list = 
  match path with
  | [] -> []
  | x::xs -> 
    let actual_type = 
      match t with
      | Namedt ty -> lookup ctxt.tdecls ty
      | _ -> t
    in
    begin match actual_type with
    | Struct y ->
      let size = 
        begin match x with
        | Const z -> z
        | _ -> 0L
        end 
      in 
      let amount = struct_index ctxt y size in
      [
        (Movq, [Imm (Lit amount); Reg R09]);
        (Addq, [Reg R09; Reg R11])
        ] @ helper_gep ctxt (List.nth y (Int64.to_int size)) xs
    | Array (_, y) -> 
      let size = compile_operand_full ctxt (Reg R09) x
        (* begin match x with
        | Const z -> Imm (Lit z)
        | Gid z ->
          let mgld_lbl = Platform.mangle z in
          lookup ctxt.layout mgld_lbl
        | Id z -> lookup ctxt.layout z
        | _ -> failwith "Invalid argument passed to getelementptr instruction"
        end  *)
      in 
      let amount = Int64.of_int (size_ty ctxt.tdecls y) in
      size @
      [
        (Imulq, [Imm (Lit amount); Reg R09]);
        (Addq, [Reg R09; Reg R11])
        ] @ helper_gep ctxt y xs
    | _ -> let size =
      begin 
        match x with
        | Const z -> Imm (Lit z)
        | Gid z ->
          let mgld_lbl = Platform.mangle z in
          lookup ctxt.layout mgld_lbl
        | Id z -> lookup ctxt.layout z
        | _ -> failwith "Invalid argument passed to getelementptr instruction"
        end 
      in let amount = Int64.of_int (size_ty ctxt.tdecls t) in
      [
        (Movq, [size; Reg R09]);
        (Imulq, [Imm (Lit amount); Reg R09]);
        (Addq, [Reg R09; Reg R11])
        ]
    end

let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) ((x::xs): Ll.operand list) : ins list =
  match op with
    | (Ptr t, _) -> let index = (compile_operand_full ctxt (Reg R09) x) @ [(Imulq, [Imm (Lit (Int64.of_int (size_ty ctxt.tdecls t))); Reg R09])];
      in match op with
      |(Ptr t, Const x) -> index @ [(Leaq, [Imm (Lit x); Reg R11]); (Addq, [Reg R09; Reg R11])] @ helper_gep ctxt t xs
      |(Ptr t, Gid x) ->
        let place = compile_operand_full ctxt (Reg R11) (Gid x) in
        index @ place @ [(Addq, [Reg R09; Reg R11])] @ helper_gep ctxt t xs
      | (Ptr t, Id x) ->
        let place = compile_operand_full ctxt (Reg R11) (Id x) in
        index @ place @ [(Addq, [Reg R09; Reg R11])] @ helper_gep ctxt t xs
      | _ -> []



(* compiling instructions  -------------------------------------------------- *)

let resolve_op (op:Ll.operand) (layout:layout) =
  match op with
  | Null -> Imm (Lit 0L)
  | Const n -> Imm (Lit n)
  | Gid id ->
    let mgld_lbl = Platform.mangle id in
    lookup layout mgld_lbl
  | Id id -> lookup layout id

let compile_bop (ctxt:ctxt) (bop:bop) (op1:Ll.operand) (op2:Ll.operand) (dest:X86.operand) (layout:layout) : X86.ins list =
  let temp_reg = (Reg R11) in
  let compiled_op1 = compile_operand_full ctxt temp_reg op1 in
  let x86op2 = resolve_op op2 layout in
  let temp_to_dest_transf = (Movq, [temp_reg; dest]) in
  begin match bop with
  | Add -> compiled_op1 @ [(Addq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Sub -> compiled_op1 @ [(Subq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Mul -> compiled_op1 @ [(Imulq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Shl ->
    let sh_reg_1 = (Reg R10) in 
    let sh_reg_2 = (Reg Rcx) in
    let sh_op1 = compile_operand_full ctxt sh_reg_1 op1 in
    let sh_op2 = compile_operand_full ctxt sh_reg_2 op2 in
    let sh_dest_transf = (Movq, [sh_reg_1; dest]) in
     sh_op1 @ sh_op2 @ [(Shlq, [sh_reg_2; sh_reg_1]); sh_dest_transf]
  | Lshr ->
    let sh_reg_1 = (Reg R10) in 
    let sh_reg_2 = (Reg Rcx) in
    let sh_op1 = compile_operand_full ctxt sh_reg_1 op1 in
    let sh_op2 = compile_operand_full ctxt sh_reg_2 op2 in
    let sh_dest_transf = (Movq, [sh_reg_1; dest]) in
    sh_op1 @ sh_op2 @ [(Shrq, [sh_reg_2; sh_reg_1]); sh_dest_transf]
  | Ashr ->
    let sh_reg_1 = (Reg R10) in 
    let sh_reg_2 = (Reg Rcx) in
    let sh_op1 = compile_operand_full ctxt sh_reg_1 op1 in
    let sh_op2 = compile_operand_full ctxt sh_reg_2 op2 in
    let sh_dest_transf = (Movq, [sh_reg_1; dest]) in
    sh_op1 @ sh_op2 @ [(Sarq, [sh_reg_2; sh_reg_1]); sh_dest_transf]
  | And -> compiled_op1 @ [(Andq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Or -> compiled_op1 @ [(Orq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Xor -> compiled_op1 @ [(Xorq, [x86op2; temp_reg]); temp_to_dest_transf]
  end

let compile_alloca (tdecls:(lbl * ty) list) (ty:ty) (dest:X86.operand) : X86.ins list =
  let ty_size = Int64.of_int (size_ty tdecls ty) in
  let stack_allocation = (Subq, [Imm (Lit ty_size); Reg Rsp]) in
  (* let temp_reg = Reg R10 in
  let pointer_comp = [(Leaq, [Ind2 Rsp; temp_reg]); (Movq, [temp_reg; dest])] in *)
  let pointer_comp = [(Movq, [Reg Rsp; dest])] in
  [stack_allocation] @ pointer_comp

let compile_load (ctxt:ctxt) (op:Ll.operand) (dest:X86.operand) (layout:layout) : X86.ins list =
  let temp_reg = Reg R10 in
  let compiled_op = compile_operand_full ctxt temp_reg op in
  compiled_op @
  [
    (Movq, [Ind2 R10; Reg R11]);
    (Movq, [Reg R11; dest]);
  ]
  (* begin match op with
  | Null | Const _ -> []
  | Gid id ->
    let mgld_lbl = Platform.mangle id in
    [(Movq, [(lookup layout mgld_lbl); dest])]
  | Id id -> [temp_to_dest_transf; (Movq, [temp_reg; dest])]
  end *)

let compile_store (ctxt:ctxt) (op1:Ll.operand) (op2:Ll.operand) (layout:layout) : X86.ins list =
  begin match op1 with
  | Null -> []
  | _ ->
    let x86op1 = compile_operand_full ctxt (Reg R12) op1 in
    begin match op2 with
    | Null | Const _ -> []
    | _ ->
      let x86op2 = compile_operand_full ctxt (Reg R13) op2 in
      x86op1 @
      x86op2 @
      [Movq, [Reg R12; Ind2 R13]]
        (* match (x86op1, x86op2) with
        | (Ind1 _, Ind1 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind1 _, Ind2 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind1 _, Ind3 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind2 _, Ind1 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind2 _, Ind2 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind2 _, Ind3 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind3 _, Ind1 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind3 _, Ind2 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind3 _, Ind3 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | _ -> [Movq, [x86op1; x86op2]] *)
    end
  end

let compile_icmp (cond:Ll.cnd) (op1:Ll.operand) (op2:Ll.operand) (dest:X86.operand) (ctxt:ctxt) : X86.ins list =
  let temp_reg1 = Reg R10 in
  let temp_reg2 = Reg R11 in
  let temp_reg3 = Reg R10 in
  let x86_op1 = compile_operand_full ctxt temp_reg1 op1 in
  let x86_op2 = compile_operand_full ctxt temp_reg2 op2 in

  let comp = (Cmpq, [temp_reg2; temp_reg1]) in
  match cond with
  | Eq ->  x86_op2 @ x86_op1 @ [comp; (Set Eq, [temp_reg3]); (Movq, [temp_reg3; dest])]
  | Ne ->  x86_op2 @ x86_op1 @ [comp; (Set Neq,[temp_reg3]); (Movq, [temp_reg3; dest])]
  | Slt -> x86_op2 @ x86_op1 @ [comp; (Set Lt, [temp_reg3]); (Movq, [temp_reg3; dest])]
  | Sle -> x86_op2 @ x86_op1 @ [comp; (Set Le, [temp_reg3]); (Movq, [temp_reg3; dest])]
  | Sgt -> x86_op2 @ x86_op1 @ [comp; (Set Gt, [temp_reg3]); (Movq, [temp_reg3; dest])]
  | Sge -> x86_op2 @ x86_op1 @ [comp; (Set Ge, [temp_reg3]); (Movq, [temp_reg3; dest])]

  let call_first_reg_helper (n : int) (op:X86.operand) : ins =
    match n with
    | 0 -> (Movq, [op; Reg Rdi])
    | 1 -> (Movq, [op; Reg Rsi])
    | 2 -> (Movq, [op; Reg Rdx])
    | 3 -> (Movq, [op; Reg Rcx])
    | 4 -> (Movq, [op; Reg R08])
    | 5 -> (Movq, [op; Reg R09])
    | _ -> (Movq, [op; Reg R10]) (* (Pushq, [Ind3 ( Lit ( Int64.mul 8L (Int64.sub (Int64.of_int n) 5L ) ) , Rbp )]) *)

let rec inv_take (n:int) (l: 'a list) : 'a list =
  match n, l with
  | 0, _ -> l
  | _, [] -> []
  | n, (_::ls) -> inv_take (n - 1) ls

let mem_args_helper : ('a list -> 'a list) = inv_take 6

let compile_call (fn:Ll.operand) (operands:(ty * Ll.operand) list) (dest:X86.operand) (ctxt:ctxt) : ins list =
  match fn with
  | Null | Const _ -> []
  | Gid lbl | Id lbl ->
  let push_reg_args = 
    List.concat ( List.mapi (
      fun i ((_, op):(ty * Ll.operand)) -> 
        (compile_operand_full ctxt (Reg R10) op) @ [(call_first_reg_helper i (Reg R10))]
    ) operands)
  in
  let mem_args = List.rev (mem_args_helper operands) in
  let push_mem_args = List.concat_map (fun (_, op) -> compile_operand_full ctxt (Reg R10) op @ [(Pushq, [Reg R10])]) mem_args in
  let pop_mem_args = List.concat_map (fun (_, op) -> compile_operand_full ctxt (Reg R10) op @ [(Popq, [Reg R10])]) mem_args in
  let push_caller_saved = [(Pushq, [Reg Rax]);(Pushq, [Reg Rbx]);(Pushq, [Reg Rcx]);(Pushq, [Reg Rsi]);(Pushq, [Reg Rdi]);(Pushq, [Reg R08]);(Pushq, [Reg R09]);(Pushq, [Reg R10]);(Pushq, [Reg R11]);(Pushq, [Reg R12]);(Pushq, [Reg R13]);(Pushq, [Reg R14]);(Pushq, [Reg R15])] in
  let pop_caller_saved = [(Popq, [Reg R15]);(Popq, [Reg R14]);(Popq, [Reg R13]);(Popq, [Reg R12]);(Popq, [Reg R11]);(Popq, [Reg R10]);(Popq, [Reg R09]);(Popq, [Reg R08]);(Popq, [Reg Rdi]);(Popq, [Reg Rsi]);(Popq, [Reg Rcx]);(Popq, [Reg Rbx]);(Popq, [Reg Rax])] in 
  push_caller_saved @
  push_reg_args @
  push_mem_args @
  [ 
    (Callq, [Imm (Lbl (Platform.mangle lbl))])
  ] @ 
  pop_mem_args @

  [(Movq, [Reg Rax; dest])] @ pop_caller_saved

let compile_bitcast (op:Ll.operand) (dest:X86.operand) (ctxt:ctxt) : X86.ins list =
  let temp_reg = Reg R10 in
  let x86_op = compile_operand_full ctxt temp_reg op in
  x86_op @
  [(Movq, [temp_reg; dest])]

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn (ctxt:ctxt) ((uid:uid), (i:Ll.insn)) : X86.ins list =
  match ctxt with
  | { tdecls : (lbl * ty) list; layout : layout; } ->
    let dest = lookup layout uid in
    begin match i with
    | Binop (bop, _, op1, op2) -> compile_bop ctxt bop op1 op2 dest layout
    | Alloca ty -> compile_alloca tdecls ty dest
    | Load (_, op) -> compile_load ctxt op dest layout
    | Store (_, op1, op2) -> compile_store ctxt op1 op2 layout
    | Icmp (cond, _, op1, op2) -> compile_icmp cond op1 op2 dest ctxt
    | Call (_, op, operands) -> compile_call op operands dest ctxt
    | Bitcast (_, op, _) -> compile_bitcast op dest ctxt
    | Gep (ty, op, operands) -> (compile_gep ctxt (ty, op) operands) @ [(Movq, [Reg R11; dest])]
    end



(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn:string) (l:string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn:string) (ctxt:ctxt) (t:Ll.terminator) : ins list =
  let amount = Int64.mul (Int64.of_int (List.length ctxt.tdecls)) 8L in 
  match t with
  | Ret (Void, _) -> 
    [(Addq, [Imm (Lit amount); Reg Rsp]);
    (Movq, [Reg Rbp; Reg Rsp]);
    (Popq, [Reg Rbp]);
    (Retq, [])]
  | Br x -> 
    let mgld_lbl = mk_lbl fn x in
    [(Jmp, [Imm (Lbl mgld_lbl)])]
  | Ret (_, Some (Id x)) -> 
    [
      (Movq, [lookup ctxt.layout x; Reg Rax]);
      (Addq, [Imm (Lit amount); Reg Rsp]);
      (Movq, [Reg Rbp; Reg Rsp]);
      (Popq, [Reg Rbp]);
      (Retq, [])
    ]
  | Ret (_, Some (Gid x)) ->
    [
      (Leaq, [Ind3 ((Lbl (Platform.mangle x)), Rip); Reg Rax]);
      (Addq, [Imm (Lit amount); Reg Rsp]);
      (Movq, [Reg Rbp; Reg Rsp]);
      (Popq, [Reg Rbp]);
      (Retq, [])
    ]
  | Ret (_, Some (Const x)) -> 
    [
      (Movq, [Imm (Lit x); Reg Rax]);
      (Addq, [Imm (Lit amount); Reg Rsp]);
      (Movq, [Reg Rbp; Reg Rsp]);
      (Popq, [Reg Rbp]);
      (Retq, [])
    ]
  | Cbr ((Const n), y, z) -> 
    if n = 1L then
      [
        (Jmp, [Imm (Lbl (mk_lbl fn y))])
      ]
    else
    [
      Jmp, [Imm (Lbl (mk_lbl fn z))]
    ]
  | Cbr ((Id x), y, z) | Cbr ((Gid x), y, z) -> 
    [
      (Cmpq, [Imm(Lit 1L); lookup ctxt.layout (Platform.mangle x)]);
      (J Eq,[Imm (Lbl (mk_lbl fn y))]); 
      (Jmp, [Imm (Lbl (mk_lbl fn z))])
    ]
  | _ -> []


(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete.
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn:string) (ctxt:ctxt) (blk:Ll.block) : ins list =
  match blk with
  | { insns : (lbl * insn) list; term : lbl * terminator; } ->
    match term with
    | (_, terminator) -> (List.concat_map (compile_insn ctxt) insns) @ (compile_terminator fn ctxt terminator)

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
match n with
| 0 -> Reg Rdi
| 1 -> Reg Rsi
| 2 -> Reg Rdx
| 3 -> Reg Rcx
| 4 -> Reg R08
| 5 -> Reg R09
| _ -> Ind3 ( Lit ( Int64.mul 8L (Int64.sub (Int64.of_int (n + 1)) 5L ) ) , Rbp )


(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals

*)
let rec reg_layout (args_list : uid list) (i:int) : layout =
match args_list with
| [] -> []
| (args :: xs) -> 
  match xs with
  | [] -> [(args, arg_loc i)]
  | _ -> (args, arg_loc i) :: (reg_layout xs (i + 1))

let block_layout (uids : uid list) (offset:quad) : layout =
  let offset = ref offset in
  List.concat (List.map (fun (uid: uid) : layout ->
    let old_offset = !offset in 
    offset := Int64.sub !offset 8L;
    [(uid, Ind3 (Lit old_offset, Rbp))]
  ) uids)

let rec unifier (l : (lbl * block) list) : (uid * insn) list =
  match l with
  | [] -> []
  | (_, {insns; _})::xs -> insns @ (unifier xs)

let stack_layout (args : uid list) ((block, lbled_blocks):cfg) : layout =
  let uids_all = (List.map fst block.insns) @ (List.map fst lbled_blocks) @ (List.concat_map (fun bl -> List.map fst bl.insns) (List.map snd lbled_blocks)) in
  reg_layout args 0 @ (block_layout (uids_all) (-8L))

(* The code for the entry-point of a function must do several things:
/compi
   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
(* `f_ty` is a function type that consists of a list of argument types and a return type. *)
(* `f_param` is a list of unique identifiers for the function parameters *)
(* `f_cfg` is a control flow graph that represents the body of the function *)
let compile_fdecl (tdecls:(tid * ty) list) (name:string) ({ f_ty; f_param; f_cfg }:fdecl) : prog =
  match f_cfg with
  | (entry, blocks) ->
    let uids_all = (List.map fst (fst f_cfg).insns) @ (List.map fst (snd f_cfg)) @ (List.concat_map (fun bl -> List.map fst bl.insns) (List.map snd (snd f_cfg))) in
    let params_layout = (stack_layout f_param f_cfg) in
    let params_length = Int64.mul 8L (Int64.of_int (List.length uids_all)) in
    let ctxt = { tdecls = tdecls; layout = params_layout } in
    let entry_ins = (compile_block name ctxt entry) in
    let blocks_asm = List.map (fun (lbl, blk) -> compile_lbl_block name lbl ctxt blk) blocks in
    let first_list : ins list = [
      (Pushq, [Reg Rbp]);
      (Movq, [Reg Rsp; Reg Rbp]);
      (Subq, [Imm (Lit params_length); Reg Rsp])
    ]
    in
    let snd_list = [
      (Addq, [Imm (Lit params_length); Reg Rsp]);
      (Movq, [Reg Rsp; Reg Rbp]);
      (Popq, [Reg Rbp]);
      (Retq, [])
    ]
    in
    [Asm.gtext (Platform.mangle name) (first_list @ entry_ins @ snd_list)] @
    blocks_asm
      (* { lbl = Platform.mangle name; global = true; asm = first_list @  }
      ( Text (List.concat [first_list; (compile_block name ctxt entry); (List.concat_map (fun (lbl, block) -> compile_block lbl ctxt block) blocks); snd_list]) ) *)
      (* let block_lbls = (List.map (fun (lbl, block) -> compile_lbl_block name lbl ctxt block) blocks) in *)
      (* ( Text (List.concat [first_list; (compile_block name ctxt entry); ; snd_list]) ) *)



(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1,g,t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  let prog = (List.map g gdecls) @ (List.map f fdecls |> List.flatten) in
  prog
