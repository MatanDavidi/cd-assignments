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
let rec helper_gep (ctxt:ctxt) (t:Ll.ty) (path: Ll.operand list) : ins list =
  match path with
  | [] -> []
  | x::xs ->
    begin match t with
    | Struct y ->
      let size =
      begin match x with
      | Const z -> z
      end in let amount = Int64.of_int (size_ty ctxt.tdecls t) in
      [
        (Movq, [Imm (Lit size); Reg R09]);
        (Imulq, [Imm (Lit amount); Reg R09]);
        (Addq, [Reg R09; Reg R10])
        ] @ helper_gep ctxt (List.nth y (Int64.to_int size)) xs
    | Array (_, y) ->
      let size =
      begin match x with
      | Const z -> Imm (Lit z)
      | Gid z ->
        let mgld_lbl = Platform.mangle z in
        lookup ctxt.layout mgld_lbl
      | Id z -> lookup ctxt.layout z
      end in let amount = Int64.of_int (size_ty ctxt.tdecls t) in
      [
        (Movq, [size; Reg R09]);
        (Imulq, [Imm (Lit amount); Reg R09]);
        (Addq, [Reg R09; Reg R10])
        ] @ helper_gep ctxt y xs
    | _ -> let size =
      begin match x with
      | Const z -> Imm (Lit z)
      | Gid z ->
        let mgld_lbl = Platform.mangle z in
        lookup ctxt.layout mgld_lbl
      | Id z -> lookup ctxt.layout z
      end in let amount = Int64.of_int (size_ty ctxt.tdecls t) in
      [
        (Movq, [size; Reg R09]);
        (Imulq, [Imm (Lit amount); Reg R09]);
        (Addq, [Reg R09; Reg R10])
        ]
    end

let compile_gep (ctxt:ctxt) (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  match op with
  |(Ptr t, Const x) -> [(Leaq, [Imm (Lit x); Reg R10])] @ helper_gep ctxt t path
  |(Ptr t, Gid x) ->
    (* let mgld_lbl = Platform.mangle x in
    let place = (print_endline ("looking up GID " ^ mgld_lbl)); lookup ctxt.layout mgld_lbl in
    (print_endline ("I looked up GID " ^ mgld_lbl)); [(Leaq, [place; Reg R10])] @ helper_gep ctxt t path *)
    let place = (print_endline ("looking up GID " ^ x)); compile_operand_full ctxt (Reg R10) (Gid x) in
    (print_endline ("I looked up GID " ^ x)); place @ helper_gep ctxt t path
  | (Ptr t, Id x) ->
    (* let place = (print_endline ("looking up ID " ^ x)); lookup ctxt.layout x in
    (print_endline ("I looked up ID " ^ x)); [(Leaq, [place; Reg R10])] @ helper_gep ctxt t path *)
    let place = (print_endline ("looking up ID " ^ x));compile_operand_full ctxt (Reg R10) (Id x) in
    place @ helper_gep ctxt t path
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
  | Shl -> compiled_op1 @ [(Shlq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Lshr -> compiled_op1 @ [(Shrq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Ashr -> compiled_op1 @ [(Sarq, [x86op2; temp_reg]); temp_to_dest_transf]
  | And -> compiled_op1 @ [(Andq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Or -> compiled_op1 @ [(Orq, [x86op2; temp_reg]); temp_to_dest_transf]
  | Xor -> compiled_op1 @ [(Xorq, [x86op2; temp_reg]); temp_to_dest_transf]
  end

let compile_alloca (ty:ty) (tdecls:(lbl * ty) list) (dest:X86.operand) : X86.ins list =
  let ty_size = Int64.of_int (size_ty tdecls ty) in
  let stack_allocation = (Subq, [Imm (Lit ty_size); Reg Rsp]) in
  let temp_reg = Reg R10 in
  let pointer_comp = [(Leaq, [Ind2 Rsp; temp_reg]); (Movq, [temp_reg; dest])] in
  [stack_allocation] @ pointer_comp

let compile_load (ctxt:ctxt) (op:Ll.operand) (dest:X86.operand) (layout:layout) : X86.ins list =
  let temp_reg = Reg R10 in
  let compiled_op = compile_operand_full ctxt temp_reg op in
  compiled_op
  (* begin match op with
  | Null | Const _ -> []
  | Gid id ->
    let mgld_lbl = Platform.mangle id in
    [(Movq, [(lookup layout mgld_lbl); dest])]
  | Id id -> [temp_to_dest_transf; (Movq, [temp_reg; dest])]
  end *)

let compile_store (op1:Ll.operand) (op2:Ll.operand) (layout:layout) : X86.ins list =
  begin match op1 with
  | Null -> []
  | _ ->
    let x86op1 = resolve_op op1 layout in
    begin match op2 with
    | Null | Const _ -> []
    | _ ->
      let x86op2 = resolve_op op2 layout in
        match (x86op1, x86op2) with
        | (Ind1 _, Ind1 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind1 _, Ind2 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind1 _, Ind3 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind2 _, Ind1 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind2 _, Ind2 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind2 _, Ind3 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind3 _, Ind1 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind3 _, Ind2 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | (Ind3 _, Ind3 _) -> [(Movq, [x86op1; Reg R10]); (Movq, [Reg R10; x86op2])]
        | _ -> [Movq, [x86op1; x86op2]]
    end
  end

let compile_icmp (cond:Ll.cnd) (op1:Ll.operand) (op2:Ll.operand) (dest:X86.operand) (layout:layout) : X86.ins list =
  let x86_op1 = resolve_op op1 layout in
  let x86_op2 = resolve_op op2 layout in
  let temp_reg = Reg R10 in
  let op1_to_temp = (Movq, [x86_op1; temp_reg]) in
  let comp = (Cmpq, [temp_reg; x86_op2]) in
  match cond with
  | Eq -> [op1_to_temp; comp; (Set Eq, [dest])]
  | Ne -> [op1_to_temp; comp; (Set Neq, [dest])]
  | Slt -> [op1_to_temp; comp; (Set Lt, [dest])]
  | Sle -> [op1_to_temp; comp; (Set Le, [dest])]
  | Sgt -> [op1_to_temp; comp; (Set Gt, [dest])]
  | Sge -> [op1_to_temp; comp; (Set Ge, [dest])]

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
        | Alloca ty -> compile_alloca ty tdecls dest
        | Load (_, op) -> compile_load ctxt op dest layout
        | Store (_, op1, op2) -> compile_store op1 op2 layout
        | Icmp (cond, _, op1, op2) -> compile_icmp cond op1 op2 dest layout
        | Call (_, op, operands) -> [] (* compile_call op operands layout *)
        | Bitcast (ty1, op, ty2) -> []
        | Gep (ty, op, operands) -> compile_gep ctxt (ty, op) operands @ [(Movq, [Reg R10; dest])]
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
  match t with
  | Ret (Void, _) -> 
    let amount = Int64.mul (Int64.of_int (List.length ctxt.tdecls)) 8L in 
    [(Addq, [Imm (Lit amount); Reg Rsp]);(Popq, [Reg Rbp]);(Retq, [])]
  | Br x -> 
    List.iter (
      fun (a, b) -> Printf.printf "%s\n" (string_of_operand b)
    ) ctxt.layout; [(Jmp, [lookup ctxt.layout x])]
  | Ret (_, Some (Id x)) | Ret (_, Some (Gid x))-> 
    let amount = Int64.mul (Int64.of_int (List.length ctxt.tdecls)) 8L in 
    [
      (Movq, [lookup ctxt.layout x; Reg Rax]);
      (Addq, [Imm (Lit amount); Reg Rsp]);
      (Popq, [Reg Rbp]);(Retq, [])
    ]
  | Ret (_, Some (Const x)) -> 
    let amount = Int64.mul (Int64.of_int (List.length ctxt.tdecls)) 8L in 
    [
      (Movq, [Imm (Lit x); Reg Rax]);
      (Addq, [Imm (Lit amount); Reg Rsp]);
      (Popq, [Reg Rbp]);(Retq, [])
    ]
  | Cbr ((Id x), y, z) | Cbr ((Gid x), y, z) -> 
    [
      (Cmpq, [Imm(Lit 1L); lookup ctxt.layout x]);
      (J Eq,[lookup ctxt.layout y]); 
      (Jmp, [lookup ctxt.layout z])
    ]


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
    | (lbl, terminator) -> List.concat_map (compile_insn ctxt) insns @ (compile_terminator lbl ctxt terminator)

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
| _ -> Ind3 ( Lit ( Int64.mul 8L (Int64.sub (Int64.of_int n) 5L ) ) , Rbp )


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
  let uids_all = args @ (List.map fst block.insns) @ (List.map fst lbled_blocks) in
  (* reg_layout args 0 @ *) (block_layout (uids_all) 0L)

(* The code for the entry-point of a function must do several things:

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
    let params_layout = (stack_layout f_param f_cfg) in
    (* List.iter (fun (a, b) -> (Printf.printf "%s: %s\n" a (string_of_operand b))) params_layout;
    raise Exit; *)
    let params_length = (Int64.mul 8L (Int64.of_int (List.length tdecls))) in
    let ctxt = { tdecls = tdecls; layout = params_layout } in
    let term_name = fst entry.term in
    let term = snd entry.term in
    let entry_ins = (compile_block name ctxt entry) @ (compile_terminator term_name ctxt term) in
    let blocks_asm = List.map (fun (lbl, blk) -> compile_lbl_block name lbl ctxt blk) blocks in
    let first_list : ins list = [
      (Pushq, [Reg Rbp]);
      (Movq, [Reg Rsp; Reg Rbp]);
      (Subq, [Imm (Lit params_length); Reg Rsp])
    ] 
    in
    let snd_list = [
      (Addq, [Imm (Lit params_length); Reg Rsp]);
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
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
