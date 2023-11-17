open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

let cmp_str (s:string) : Ll.ty * Ll.operand * stream =
  (* The `+ 1` is due to the first element in the compiled array being the length of the array *)
  let strlen = String.length s in
  let strarr = Array (strlen + 1, I8) in
  (* 
    The following three are arbitrary and just picked to be slightly semantic 
    These symbols are used to identify the string and its array.
  *)
  let gstr_sym = gensym "glbl_str" in 
  let strarr_sym = gensym "arr_of_str" in
  let load_sym = gensym "str_load" in
  let str_stream = 
    (* Hoist the string to global *)
    [G (gstr_sym, (strarr, GString s))] >@
    (* Bitcast the string to [n x i8] if necessary *)
    [G (strarr_sym, (Ptr I8, GBitcast (Ptr strarr, GGid gstr_sym, Ptr I8)))] >@
    (* Load contents of string into array *)
    [I (load_sym, Load (Ptr (Ptr I8), Gid strarr_sym))]
  in
  (* Return array of type *I8 that contains the loaded data *)
  (Ptr I8, Id load_sym, str_stream)

let cmp_id (c:Ctxt.t) (id:id) : Ll.ty * Ll.operand * stream =
  let (ty, operand) = Ctxt.lookup id c in
  let id_sym = gensym id in
  match ty with
  (* If the ID points to an array, cast it to an LLVM array pointer *)
  | Ptr (Array (_, arr_ty)) -> (Ptr arr_ty, Id id_sym, [I (id_sym, Bitcast (ty, operand, Ptr arr_ty))])
  (* If the ID points to anything else, don't cast it, just load it *)
  | Ptr (ptr_ty) -> (ptr_ty, Id id_sym, [I (id_sym, Load (ty, operand))])
  | _ -> failwith "Qui non so che altro fare rip :,("

let convert_binop (bop:binop) (re_ty:Ll.ty) (op1:Ll.operand) (op2:Ll.operand) : insn =
  match bop with
  | Add -> Binop (Add, re_ty, op1, op2)
  | Sub -> Binop (Sub, re_ty, op1, op2)
  | Mul -> Binop (Mul, re_ty, op1, op2)
  | Eq -> Icmp (Eq, re_ty, op1, op2)
  | Neq -> Icmp (Ne, re_ty, op1, op2)
  | Lt -> Icmp (Slt, re_ty, op1, op2)
  | Lte -> Icmp (Sle, re_ty, op1, op2)
  | Gt -> Icmp (Sgt, re_ty, op1, op2)
  | Gte -> Icmp (Sge, re_ty, op1, op2)
  | And -> Binop (And, re_ty, op1, op2) (* UI AR NOT SCIUR *)
  | Or -> Binop (Or, re_ty, op1, op2)   (* UI AR NOT SCIUR *)
  | IAnd -> Binop (And, re_ty, op1, op2)
  | IOr -> Binop (Or, re_ty, op1, op2)
  | Shl -> Binop (Shl, re_ty, op1, op2)
  | Shr -> Binop (Lshr, re_ty, op1, op2)
  | Sar -> Binop (Ashr, re_ty, op1, op2)

let convert_unop (uop:unop) (re_ty:Ll.ty) (op:Ll.operand) : insn = 
  match uop with
  | Neg -> Binop (Mul, re_ty, op, Const (Int64.neg 1L))
  | Lognot -> Icmp (Eq, re_ty, op, Const 0L) (* UI AR NOT SCIUR *) (* (Add, re_ty, 1L, Binop (Xor, re_ty, op, Const 0xFFFFFFFFL)) *)
  | Bitnot -> Binop (Xor, re_ty, op, Const (Int64.neg 1L))

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream =
  let int64_of_bool b = if b then 1L else 0L in
  match exp.elt with
  | CNull rty -> 
    let ll_ty = cmp_rty rty in
    (Ptr ll_ty, Null, [])
  | CBool b -> 
    (I1, Const (int64_of_bool b), [])
  | CInt i ->
    (I64, Const i, [])
  | CStr s -> cmp_str s
  | CArr (ty, exp_nodes_list) -> cmp_carr c ty exp_nodes_list
  | NewArr (ty, len_exp_node) -> cmp_newarr c ty len_exp_node
  | Id id -> cmp_id c id
  | Index (ref_exp_node, index_exp_node) -> cmp_index c ref_exp_node index_exp_node
  | Call (fname_exp_node, fparams_exp_nodes_list) -> cmp_call c fname_exp_node fparams_exp_nodes_list
  | Bop (bop, exp_node_op1, exp_node_op2) -> cmp_bop c bop exp_node_op1 exp_node_op2
  | Uop (uop, exp_node_op) -> cmp_uop c uop exp_node_op

and cmp_carr (c:Ctxt.t) (ty:Ast.ty) (exp_nodes_list:exp node list) : Ll.ty * Ll.operand * stream =
  (* Get array's length *)
  let arrlen = Int64.of_int (List.length exp_nodes_list) in
  (* Allocate space on stack for array *)
  let alloc_ty, alloc_operand, alloc_stream = oat_alloc_array ty (Const arrlen) in
  (* Define function to fold over all expressions in array to allocate their contents *)
  let f = fun (arr_ty, prev_array, prev_index, prev_stream) exp -> 
    (* Get compile expression *)
    let curr_ty, curr_op, curr_stream = cmp_exp c exp in
    (* Define symbol to associate to expression allocation/storage *)
    let gep_sym = gensym "arr_gep" in 
    (* Define expression allocation instruction *)
    let alloc_gep_stream = [I (gep_sym, Gep (arr_ty, prev_array, [Const 0L; Const 1L; Const prev_index]))] in
    (* Define expression storage (store) instruction *)
    let store_stream = [I (gep_sym, Store (curr_ty, curr_op, Id gep_sym))] in
    (* "Concatenate" new gep allocation and expression storage streams to previous array  *)
    (arr_ty, prev_array, (Int64.add prev_index 1L), prev_stream >@ curr_stream >@ alloc_gep_stream >@ store_stream)
  in
  (* Not sure what to do with array type, second-to-last array element operand and index gotten with fold *)
  let _, _, _, store_stream = List.fold_left f (alloc_ty, alloc_operand, 0L, []) exp_nodes_list in
  (alloc_ty, alloc_operand, alloc_stream >@ store_stream)

  and cmp_newarr (c:Ctxt.t) (ty:Ast.ty) (len_exp_node:exp node) : Ll.ty * Ll.operand * stream =
    (* Compile length expression -- returned type should be int, so it's ignored *)
    let _, cmp_operand, cmp_stream = cmp_exp c len_exp_node in
    (* Allocate space for array on stack *)
    let alloc_ty, alloc_operand, alloc_stream = oat_alloc_array ty cmp_operand in
    (alloc_ty, alloc_operand, cmp_stream >@ alloc_stream)

  and cmp_index (c:Ctxt.t) (ref_exp_node:exp node) (index_exp_node:exp node) : Ll.ty * Ll.operand * stream =
    (* For reference, this expression will look like `arr[5]` *)
    (* Compile array reference expression *)
    let ref_ty, ref_operand, ref_stream = cmp_exp c ref_exp_node in
    (* Compile index expression -- once again ignore implied `int` type *)
    let _, index_operand, index_stream = cmp_exp c index_exp_node in
    (* Assign arbitrary names to reference and index *)
    let ref_sym = gensym "reference" in
    let index_sym = gensym "index" in
    (* Only return something if ref_ty (i.e. type of `arr` in our example) is a pointer to an array *)
    match ref_ty with
    | Ptr (Struct [_; Array (_, arr_ty)]) -> 
      (* Assemble instructions stream *)
      let cmp_stream = 
        ref_stream >@
        index_stream >@
        [I (ref_sym, Gep (ref_ty, ref_operand, [Const 0L; Const 1L; index_operand]))] >@
        [I (index_sym, Load (Ptr arr_ty, Id ref_sym))]
      in
      (arr_ty, Id index_sym, cmp_stream)
    | _ -> failwith "Invalid syntax: Index reference compiles to non-array type"

  and cmp_call (c:Ctxt.t) (fname_exp_node: exp node) (fparams_exp_nodes_list: exp node list) : Ll.ty * Ll.operand * stream =
    match fname_exp_node with
    | { elt = Id f_name; loc = _ } ->
      (* Lookup function name *)
      let f_ty, f_op = Ctxt.lookup f_name c in
      (* Make sure function type is "pointer to function" *)
      begin match f_ty with
      | Ptr (Fun (args_ty, re_ty)) -> 
        let f (args, stream) arg_to_c = 
          let arg_ty, arg_op, arg_stream = cmp_exp c arg_to_c in
          (args @ [arg_ty, arg_op], stream >@ arg_stream)
        in
        let new_args, new_stream = List.fold_left f ([], []) fparams_exp_nodes_list in
        let call_sym = f_name ^ "_call" in
        let call_stream = [I (call_sym, Call (re_ty, f_op, new_args))] in
        (re_ty, Id call_sym, new_stream >@ call_stream)
        | _ -> failwith "Could not compile: function type should be \"Pointer to function\""
      end
    | _ -> failwith "Invalid argument passed to function `cmp_call`"

  and cmp_bop (c:Ctxt.t) (bop:binop) (exp_node_op1:exp node) (exp_node_op2:exp node) : Ll.ty * Ll.operand * stream = 
    let _, _, re_ty = typ_of_binop bop in
    let op1_ty, op1, op1_stream = cmp_exp c exp_node_op1 in
    let op2_ty, op2, op2_stream = cmp_exp c exp_node_op2 in
    let res_sym = gensym "bop_ans" in
    let mov_stream = [I (res_sym, convert_binop bop (cmp_ty re_ty) op1 op2)] in
    let bop_stream = op1_stream >@ op2_stream >@ mov_stream in
    (cmp_ty re_ty, Id res_sym, bop_stream)

  and cmp_uop (c:Ctxt.t) (uop:unop) (exp_node_op:exp node) : Ll.ty * Ll.operand * stream =
    let _, re_ty = typ_of_unop uop in
    let op_ty, op, op_stream = cmp_exp c exp_node_op in
    let res_sym = gensym "uop_ans" in
    let mov_stream = [I (res_sym, convert_unop uop (cmp_ty re_ty) op)] in
    let uop_stream = op_stream >@ mov_stream in
    (cmp_ty re_ty, Id res_sym, uop_stream)

let cmp_assn (c:Ctxt.t) (ref_exp_node:exp node) (val_exp_node:exp node) : Ctxt.t * stream =
  let val_ty, val_operand, val_stream = cmp_exp c val_exp_node in
  match ref_exp_node.elt with
  | Id id -> 
    let store_sym = gensym "store_assn_id" in
    let _, ref_operand = Ctxt.lookup id c in
    (c, val_stream >@ [I (store_sym, Store (val_ty, val_operand, ref_operand))])
  | Index (arr_exp_node, index_exp_node) -> 
    let arr_ty, arr_operand, arr_stream = cmp_exp c arr_exp_node in
    (* Again, ignore type that is assumed to be int *)
    let _, index_operand, index_stream = cmp_exp c index_exp_node in
    let store_sym = gensym "store_assn_arr" in
    let arr_sym = gensym "arr_assn" in
    let assn_stream = 
      [I (arr_sym, Gep (arr_ty, arr_operand, [Const 0L; Const 1L; index_operand]))] >@
      [I (store_sym, Store (val_ty, val_operand, Id arr_sym))] 
    in
    (c, val_stream >@ arr_stream >@ index_stream >@ assn_stream)
  | _ -> failwith "Invalid lhs expression for assignment statement"

let cmp_decl (c:Ctxt.t) ((id, assn_exp_node):vdecl) : Ctxt.t * stream =
  let assn_ty, assn_operand, assn_stream = cmp_exp c assn_exp_node in
  let decl_sym = gensym id ^ "_decl" in
  let new_c = Ctxt.add c id (Ptr assn_ty, Id decl_sym) in
  let alloca_stream = [E (decl_sym, Alloca assn_ty)] in
  let store_stream = [I (decl_sym, Store (assn_ty, assn_operand, Id decl_sym))] in
  (* TODO: Check if order of streams is correct? *)
  (new_c, assn_stream >@ alloca_stream >@ store_stream)

let cmp_ret (c:Ctxt.t) (opt:exp node option) : Ctxt.t * stream =
  match opt with
  | Some ret_exp -> 
    let ret_ty, ret_operand, ret_stream = cmp_exp c ret_exp in
    let term_stream =  [T (Ret (ret_ty, Some ret_operand))] in
    (c, ret_stream >@ term_stream)
  | None -> 
    (c, [T (Ret (Void, None))])

(* The following function is implemented ad cazzum, and should not be treated as correct by any means *)
let cmp_scall (c:Ctxt.t) (func_exp_node:exp node) (args_exp_nodes_list:exp node list) : Ctxt.t * stream =
  let call_ty, call_operand, call_stream = cmp_exp c ({ elt = (Call (func_exp_node, args_exp_nodes_list)); loc = Range.norange}) in
  (c, call_stream)

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)

let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  match stmt.elt with
  | Assn (ref_exp_node, val_exp_node) -> cmp_assn c ref_exp_node val_exp_node
  | Decl var_decl -> cmp_decl c var_decl
  | Ret opt -> cmp_ret c opt
  | SCall (func_exp_node, args_exp_nodes_list) -> cmp_scall c func_exp_node args_exp_nodes_list
  | If (cond_exp_node, true_stmt_nodes_list, false_stmt_nodes_list) -> cmp_if c rt cond_exp_node true_stmt_nodes_list false_stmt_nodes_list
  | While (cond_exp_node, body_stmt_nodes_list) -> cmp_while c rt cond_exp_node body_stmt_nodes_list
  | For (vdecls, cond_exp_node_opt, updates_stmt_nodes_list, body_stmt_nodes_list) -> cmp_for c rt vdecls cond_exp_node_opt updates_stmt_nodes_list body_stmt_nodes_list

and cmp_if (c:Ctxt.t) (rt:Ll.ty) (cond_exp_node:exp node) (true_stmt_nodes_list:stmt node list) (false_stmt_nodes_list:stmt node list) =
let cond_ty, cond_operand, cond_stream = cmp_exp c cond_exp_node in
(* let f = fun (prev_c, prev_stream) curr_stmt -> 
  let (curr_c, curr_stream) = cmp_stmt prev_c rt curr_stmt in
  (curr_c, prev_stream >@ curr_stream)
in *)
let (true_context, true_stream) =   cmp_block c rt true_stmt_nodes_list in (* List.fold_left f (c, []) true_stmt_nodes_list in *)
let (false_context, false_stream) = cmp_block true_context rt false_stmt_nodes_list in (* List.fold_left f (true_context, []) false_stmt_nodes_list in *)
let if_sym = gensym "if" in
let if_lbl = [L if_sym] in
let then_sym = gensym "then" in
let then_lbl = [L then_sym] in
let else_sym = gensym "else" in
let else_lbl = [L else_sym] in
let end_if_sym = gensym "end_if" in
let end_if_lbl = [L end_if_sym] in
let if_term = [T (Br if_sym)] in
let end_if_term = [T (Br end_if_sym)] in
let if_cbr_term = [T (Cbr (cond_operand, then_sym, else_sym))] in
let else_cbr_term = [T (Cbr (cond_operand, then_sym, end_if_sym))] in
let true_term = match true_stream with | [] -> [] | (i :: _) -> [i] in
let false_term = match false_stream with | [] -> [] | (i :: _) -> [i] in
(* If both blocks end in a return, adjust overall return *)
let ret_stream = 
  match (true_term, false_term) with
  | [T (Ret (Void, None))], [T (Ret (Void, None))] -> [T (Ret (Void, None))]
  | [T (Ret (true_ty, Some true_op))], [T (Ret (false_ty, Some false_op))] -> [T (Ret ((false_ty, Some true_op)))]
  | _ -> []
in
let if_stream = 
  if_term >@
  if_lbl >@
  cond_stream >@
  if_cbr_term >@
  then_lbl >@
  true_stream >@
  end_if_term >@
  else_lbl >@
  false_stream >@
  end_if_term >@
  end_if_lbl >@
  ret_stream
in
let if_no_else_stream = 
  if_term >@
  if_lbl >@
  cond_stream >@
  else_cbr_term >@
  then_lbl >@
  true_stream >@
  end_if_term >@
  end_if_lbl >@
  ret_stream in
if false_stream = [] then
  (c, if_stream)
else
  (c, if_no_else_stream)

and cmp_while (c:Ctxt.t) (rt:Ll.ty) (cond_exp_node:exp node) (body_block:Ast.block) : Ctxt.t * stream =
  let cond_ty, cond_operand, cond_stream = cmp_exp c cond_exp_node in
  let body_c, body_stream = cmp_block c rt body_block in
  let cond_sym = gensym "while_cond" in
  let cond_lbl = [L cond_sym] in
  let body_sym = gensym "while_body" in
  let body_lbl = [L body_sym] in
  let end_sym = gensym "while_end" in
  let end_lbl = [L end_sym] in
  let while_term_br = [T (Br (cond_sym))] in
  let while_term_cbr = [T (Cbr (cond_operand, body_sym, end_sym))] in
  let while_stream = 
    cond_lbl >@
    cond_stream >@
    while_term_cbr >@
    body_lbl >@
    body_stream >@
    while_term_br >@
    end_lbl
  in
  (c, while_stream)

and cmp_for (c:Ctxt.t) (rt:Ll.ty) (vdecls:vdecl list) (cond_exp_node_opt:exp node option) (update_stmt_node_opt:stmt node option) (body_stmt_nodes_list:Ast.block) : Ctxt.t * stream = 
  (* Function cmp_vdecls is missing, so we create our own *)
  let vdecl_f = 
    begin 
      fun (prev_c, prev_stream) (vdecl) -> 
        let curr_c, curr_stream = cmp_decl prev_c vdecl in
        (curr_c, prev_stream >@ curr_stream)
    end in
  let vdecl_c, vdecl_stream = List.fold_left vdecl_f (c, []) vdecls in
  let cond_exp = match cond_exp_node_opt with
  | None -> { elt = CBool true; loc = Range.norange }
  | Some exp -> exp
  in 
  let body_stmts = match update_stmt_node_opt with
  | None -> body_stmt_nodes_list
  | Some update_stmt -> body_stmt_nodes_list @ [update_stmt]
  in
  let while_stmt = While (cond_exp, body_stmts) in
  let res_c, res_stream = cmp_stmt c rt { elt = while_stmt; loc = Range.norange } in
  (c, vdecl_stream >@ res_stream)

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let rec converter (e:Ast.exp) : Ll.ty =
  match e with
  | CNull x -> Ptr (Ptr (cmp_rty x))
  | CBool x -> Ptr I1
  | CInt x -> Ptr I64
  | CStr str -> Ptr (Ptr I8)
  | Bop (x, _, _) ->
    begin match x with 
    | Add | Sub | Mul | IAnd | IOr | Shl | Shr | Sar -> I64
    | _ -> I1
    end
  | Uop (u, _) ->
    begin match u with
    | Neg | Bitnot -> I64
    | _ -> I1 
    end
  | Index (x, _) | Call (x, _) -> converter x.elt
  | Id x -> Ptr (cmp_rty RString)
  | CArr (arr_ty, _) -> (Ptr (Ptr (Struct [I64; Array(0, cmp_ty arr_ty)])))
  | NewArr (x, _) -> Ptr (cmp_rty (RArray x))

let rec map_cmp_ty (t:(ty * id) list) : Ll.ty list= 
  match t with
  | [] -> []
  | (x,_)::xs -> (cmp_ty x) :: map_cmp_ty xs

let rec helper_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =  
  begin match p with
  | (x::xs) -> 
    begin match x with
    | Gvdecl z ->
      let id = z.elt.name in
      let ty = converter z.elt.init.elt in
      helper_global_ctxt (Ctxt.add c id (ty, Ll.Gid id)) xs
    | Gfdecl z -> 
      (* let id = z.elt.fname in
      let ret_ty = cmp_ret_ty z.elt.frtyp  in
      let args = map_cmp_ty z.elt.args in *)
      helper_global_ctxt c xs
    end
  | _ -> c
  end

let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t = helper_global_ctxt c p


(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)

let rec streamgen (c:Ctxt.t) (s:stream) (args:(ty * id) list) : Ctxt.t * stream = 
  match args with
  | [] -> (c,s)
  | (x::xs) -> 
    (* let ty, id = x in *)
    let fold_args = fun (prev_c, prev_stream) (ty, id) ->
      let id_sym = gensym id in
      let store_sym = gensym ("store_" ^ id) in
      let ll_ty = cmp_ty ty in
      let new_c = [id, (Ptr ll_ty, Ll.Id id_sym)] in
      let alloc_stream = [E (id_sym, Alloca ll_ty)] in
      let store_stream = [I (store_sym, Store (ll_ty, Id id, Id id_sym))] in
      (new_c @ prev_c, prev_stream >@ alloc_stream >@ store_stream)
    in
    List.fold_left fold_args (c, s) args
    (* match cmp_ty ty with
    | I1 | I8 | I64 -> 
      let newone = 
        s >@
        [E (gensym id, Alloca (cmp_ty ty))] >@
        [I (gensym id, Store (cmp_ty ty, Id id, Id (gensym id)))]
      in
      streamgen (Ctxt.add c id (Ptr (cmp_ty ty), Id (gensym id))) newone xs
    | _ -> streamgen (Ctxt.add c id (cmp_ty ty, Id id)) s xs *)

let typer ((a,b):(ty * id)) : Ll.ty = cmp_ty a
let typer1 ((a,b):(ty * id)) : id = b

let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let return = f.elt.frtyp in 
  let args =  f.elt.args in 
  let newctxt, newstrm = streamgen c [] args in
  let _, block = cmp_block newctxt (cmp_ret_ty return) f.elt.body in
  let cfg, gvars = cfg_of_stream (newstrm >@ block) in
  let func = (List.map typer args, cmp_ret_ty return) in 
  let param = List.map typer1 args in 
  ({f_ty=func; f_param=param; f_cfg=cfg}, gvars)



(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)
let bool_value (x:bool) : int64 = if x then 1L else 0L

let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull x -> ((Ptr (cmp_rty x), GNull), [])
  | CBool x -> ((I1, GInt (bool_value x)), [])
  | CInt x -> ((I64, GInt x), [])
  | CStr x -> 
    let str_sym = gensym "gstr_id" in
    let strarr = Array ((String.length x) + 1, I8) in
    ((Ptr I8, GBitcast (Ptr strarr, GGid str_sym, Ptr I8)), [str_sym, (strarr, GString x)])
  | CArr (arr_ty, elements_nodes_list) -> 
    let cmpd_ty = cmp_ty arr_ty in
    let arr_len = List.length elements_nodes_list in
    let args_fold = fun (prev_args, prev_decls) expression_node ->
      let arg, gdecl = cmp_gexp c expression_node in
      (prev_args @ [arg], prev_decls @ gdecl)
    in
    let args, gdecls = List.fold_left args_fold ([], []) elements_nodes_list in
    let arr_sym = gensym "arr_id" in
    let ptr_struct = Struct [ I64; Array (0, cmpd_ty) ] in
    let arr_decl = Struct [ I64; Array (arr_len, cmpd_ty) ] in
    let gstruct_decl = GStruct [ I64, GInt (Int64.of_int arr_len); Array (arr_len, cmpd_ty), GArray args ] in
    ((Ptr ptr_struct, GBitcast (Ptr arr_decl, GGid arr_sym, Ptr ptr_struct)), ([(arr_sym, (arr_decl, gstruct_decl))] @ gdecls))
  | _ -> failwith "Unable to globally declare expression. Should be Null, Bool, Int, Str, CArr"

(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
