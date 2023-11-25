open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err = 
  let (_, (s, e), _) = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))


(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [ "array_of_string",  ([TRef RString],  RetVal (TRef(RArray TInt)))
  ; "string_of_array",  ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", ([TRef RString],  RetVal TInt)
  ; "string_of_int",    ([TInt], RetVal (TRef RString))
  ; "string_cat",       ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     ([TRef RString],  RetVoid)
  ; "print_int",        ([TInt], RetVoid)
  ; "print_bool",       ([TBool], RetVoid)
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2 
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive) 
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TNullRef x, TNullRef y -> subtype_ref c x y
  | TRef x, TNullRef y -> subtype_ref c x y
  | TRef x, TRef y -> subtype_ref c x y
  | _ -> false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1, t2 with
  | RString, RString -> true
  | RArray x, RArray y -> subtype c x y
  | RStruct x, RStruct y -> 
    let second = Tctxt.lookup_struct y c in
    List.for_all (fun second -> let n = second.fieldName in let y = second.ftyp in
      match lookup_field_option x n c with
      | Some x -> subtype c x y
      | None -> false
      ) second
  | RFun (x, y), RFun (x', y') -> List.length x = List.length x' && List.for_all2 (subtype c) x' x && subtype_retty c y y'
  | _ -> false

(* Decides whether H |-rt rt1 <: rt2 *)
and subtype_retty (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool = 
  match t1, t2 with
  | RetVoid, RetVoid -> true
  | RetVal x, RetVal y -> subtype c x y
  | _ -> false


(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the 
      type is not well-formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
 *)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TInt -> ()
  | TBool -> ()
  | TRef x -> typecheck_ref l tc x
  | TNullRef x -> typecheck_ref l tc x
  | _ -> type_error l "Invalid"

and typecheck_ref (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.rty) : unit =
  match t with
  | RString -> ()
  | RArray x -> typecheck_ty l tc x
  | RStruct x -> if Tctxt.lookup_struct_option x tc = None then type_error l "Invalid" else ()
  | RFun (x, y) -> List.iter (typecheck_ty l tc) x; typecheck_retty l tc y 
  | _ -> type_error l "Invalid"

and typecheck_retty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ret_ty) : unit =
  match t with
  | RetVoid -> ()
  | RetVal x -> typecheck_ty l tc x

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)

*)

let converter = function
  | Ast.RetVoid -> failwith "Cannot convert RetVoid to ty"
  | Ast.RetVal ty -> ty

let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  (* print_endline "Il pota"; *)
  match e.elt with
  | CNull x -> 
    (* print_endline "Bella bra"; *)
    typecheck_ref e c x; TNullRef x
  | CBool _ -> 
    (* print_endline "Bella bre"; *)
    TBool
  | CInt _ -> 
    (* print_endline "Bella bri"; *)
    TInt
  | CStr _ -> 
    (* print_endline "Bella bro"; *)
    TRef RString
  | Id x -> 
    (* print_endline "Il doggo"; *)
    let id_opt = Tctxt.lookup_option x c in
    (* print_endline "L'altro doggo"; *)
    begin match id_opt with
    | None -> type_error e ("Undefined Identifier " ^ x)
    | Some ty -> ty
    end
  | CArr (x,y) -> let ty' = typecheck_ty e c x in
    List.iter (fun t -> let ty = typecheck_exp c t in
    if not (subtype c ty x) then type_error t "Array element type does not match array type") y; TRef (RArray x)
  | NewArr (ty, x, y, z) ->
    (* print_endline "Bella cane"; *)
    let ty' = typecheck_ty e c ty in
    let ty'' = typecheck_exp c x in
    if not (subtype c ty'' TInt) then
    type_error x "Array size expression must be of type int";
    let ty''' = typecheck_exp (Tctxt.add_local c y TInt) z in
    if not (subtype c ty''' ty) then
    type_error z "Array initialization expression type does not match array type"; TRef (RArray ty)
  | Index (x, y) -> 
    (* print_endline "Bella cana"; *)
    let ty = typecheck_exp c x in
    let ty' = typecheck_exp c y in
    if not (subtype c ty' TInt) then type_error y "Array index must be of type int";
    begin match ty with
    | TRef (RArray x) -> x
    | _ -> type_error x "Invalid"
    end
  | Length x -> 
    (* print_endline "Bella cuno"; *)
    let ty = typecheck_exp c x in
    begin match ty with
    | TRef (RArray _) -> TInt
    | _ -> type_error x "Invalid"
    end
  | CStruct (x, y) ->
    (* print_endline "Bella Cuneo"; *)
    (* let ty = Tctxt.lookup_global x c in *)
    (* print_endline "MA SEI CERTO?!?!"; *)
    List.iter (fun (id, exp) ->
    let field_ty = typecheck_exp c exp in
    let field_opt_ty = lookup_field_option x id c in
    let declared_field_ty = 
      begin match field_opt_ty with
      | None -> type_error e ("Undefined field " ^ id ^ " in struct type " ^ x)
      | Some ty -> ty
      end
    in
    if not (subtype c field_ty declared_field_ty) then
    type_error exp "Field type does not match struct field type") y; TRef (RStruct x)
  | Proj (x, y) ->
    (* print_endline "Bella Allola"; *)
    let ty = typecheck_exp c x in
    (* print_endline "ALloal andata"; *)
    begin match ty with
    | TRef (RStruct z) -> 
      let field_op = lookup_field_option z y c in
      begin match field_op with
      | None -> type_error e ("Undefined field " ^ y ^ " in struct " ^ z)
      | Some ty -> ty
      end
    | _ -> type_error x "Invalid"
    end
  | Call (x, y) ->
    (* print_endline "Bella Champagna"; *)
    let ty = typecheck_exp c x in
    begin match ty with
    | TRef (RFun (arg_tys, ret_ty)) ->
      List.iter2 (fun arg def_ty ->
        let actual_ty = typecheck_exp c arg in
        if not (subtype c actual_ty def_ty) then
        type_error arg "Argument type does not match function parameter type"
      ) y arg_tys; converter ret_ty
    | _ -> type_error x "Call operation is only valid on functions"
    end
  | Bop (x, y, z) ->
    (* print_endline "Bella Castagna"; *)
    begin match x with
    |Eq | Neq -> 
      let ty = typecheck_exp c y in
      let ty' = typecheck_exp c z in
      if not (subtype c ty ty') || not (subtype c ty' ty) then type_error e "Invalid"; TBool
    | Add | Mul | Sub | Shr | Shl | Sar | IAnd | IOr -> 
      let ty = typecheck_exp c y in 
      let ty' = typecheck_exp c z in
      if not (subtype c ty TInt) || not (subtype c ty' TInt) then type_error e "Invalid"; TInt
    | Lt | Lte | Gt | Gte -> 
      let ty = typecheck_exp c y in
      let ty' = typecheck_exp c z in
      if not (subtype c ty TInt) || not (subtype c ty' TInt) then type_error e "Invalid"; TBool
    | And | Or -> 
      let ty = typecheck_exp c y in
      let ty' = typecheck_exp c z in
      if not (subtype c ty TBool) || not (subtype c ty' TBool) then type_error e "Invalid"; TBool
    end
  | Uop (x, y) ->
    (* print_endline "Bella Brucdo"; *)
    match x with
    | Neg | Bitnot -> 
      let ty = typecheck_exp c y in
      if not (subtype c ty TInt) then type_error e "Invalid"; TInt
    | Lognot -> 
      let ty = typecheck_exp c y in
      if not (subtype c ty TBool) then type_error e "Invalid"; TBool

(* statements --------------------------------------------------------------- *)

(* Typecheck a statement 
   This function should implement the statement typechecking rules from oat.pdf.  

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns 

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not 
        contain a return statement, then the entier conditional statement might 
        not return.
  
        looping constructs never definitely return 

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the 
     block typecheck rules.
*)

let rec lhs_id = function
  | Id x -> x
  | Proj (x, y) -> lhs_id x.elt
  | Index (x, y) -> lhs_id x.elt
  | _ -> failwith "Invalid"

let exist_local (x : Ast.id) (tc : Tctxt.t) : bool =
  match Tctxt.lookup_local_option x tc with
  | None -> false
  | Some x -> true

let exist_global (x : Ast.id) (tc : Tctxt.t) : bool =
  match Tctxt.lookup_global_option x tc with
  | None -> false
  | Some x -> true
  
let rec typecheck_stmt (tc : Tctxt.t) (s:Ast.stmt node) (to_ret:ret_ty) : Tctxt.t * bool =
  (* print_endline "I'm in (typecheck_stmt)"; *)
  match s.elt with
  | Assn (x, y) -> 
    (* print_endline "A"; *)
    let lhs = lhs_id x.elt in
    if not (exist_local lhs tc || not (exist_local lhs tc)) then type_error s "Invalid assignment";
    let ty1 = typecheck_exp tc x in
    let ty2 = typecheck_exp tc y in
    if not (subtype tc ty2 ty1) then type_error s "Invalid assignment"; (tc, false)
  | Decl (id, e) ->
    (* print_endline "B"; *)
    let ty = typecheck_exp tc e in
    (* print_endline "I polish up real"; *)
    let tc' = add_local tc id ty in
    (* print_endline "Nice :)"; *)
    if exist_local id tc then type_error s "Invalid declaration"; (tc', false)
  | Ret e -> 
    (* print_endline "C"; *)
    begin match e with
    | Some e -> let ty = typecheck_exp tc e in
      if not (subtype_retty tc (RetVal ty) to_ret) then type_error s "Invalid return"; (tc, true)
    | None -> if not (subtype_retty tc RetVoid to_ret) then type_error s "Invalid return"; (tc, true)
    end
  | SCall (x, y) -> 
    (* print_endline "D"; *)
    let ty = typecheck_exp tc x in
    begin match ty with
    | TRef (RFun (arg_tys, ret_ty)) ->
      List.iter2 (fun arg arg_ty ->
        let arg_ty' = typecheck_exp tc arg in
        if not (subtype tc arg_ty' arg_ty) then
        type_error arg "Argument type does not match function parameter type"
      ) y arg_tys; (tc, false)
    | _ -> type_error x "Call operation is only valid on functions"
    end
  | If (x, y, z) -> 
    (* print_endline "E"; *)
    let ty = typecheck_exp tc x in
    if not (subtype tc ty TBool) then type_error x "If condition must be of type bool";
    let (_, ret) = typecheck_blk tc y to_ret in
    let (_, ret') = typecheck_blk tc z to_ret in (tc, ret && ret')
    (* `Cast` example (`int[]` is `re_ty`, `y` is `id`, `x` is `exp`):
        var x = new int[3]?;
        if? (int[] y = x) {
          `then_stmt_nodes`
        } else {
          `else_stmt_nodes`
        }
    *)
  | Cast (re_ty, id, exp, then_stmt_nodes, else_stmt_nodes) -> 
    (* print_endline "F"; *)
    (* Get type of exp *)
    let exp_ty = typecheck_exp tc exp in
    (* Get `ref` part of type `ref?` *)
    let exp_rty = 
    match exp_ty with
    | TNullRef exp_rty -> exp_rty
    | TRef _ -> type_error exp "Cannot cast from non-nullable reference type."
    | _ -> type_error exp "Expression should be of reference type. Non-reference types cannot be nullable."
    in
    (* Check that type of exp is supertype of ref type `exp_rty` *)
    if not (subtype_ref tc exp_rty re_ty) then type_error exp "Invalid cast. Source type should be subtype of destination type" else
      (* Typecheck both blocks *)
      let (tc', is_then_valid) = typecheck_blk tc then_stmt_nodes to_ret in
      let (tc'', is_else_valid) = typecheck_blk tc' else_stmt_nodes to_ret in
      (tc'', is_then_valid && is_else_valid)
  | While (x, y) -> 
    (* print_endline "G"; *)
    let ty = typecheck_exp tc x in
    if not (subtype tc ty TBool) then type_error x "While condition must be of type bool";
    let (_, ret) = typecheck_blk tc y to_ret in (tc, false)
  | For (x, y, z, w) -> 
    (* print_endline "H"; *)
    let tc' = List.fold_left (fun tc vdecl -> typecheck_vdecl tc vdecl) tc x in
    let _ = match y with
    | Some exp -> 
      let ty = typecheck_exp tc' exp in
      if not (subtype tc' ty TBool) then type_error exp "For condition must be of type bool"
    | None -> type_error s "For condition must be of type bool"
    in let _ = match z with
    | Some stmt -> typecheck_stmt tc' stmt to_ret
    | None -> type_error s "For without update statement" in
    let (_, ret) = typecheck_blk tc' w to_ret in (tc, false)

and typecheck_blk (tc : Tctxt.t) (stmts : stmt node list) (to_ret : ret_ty) =
  match stmts with
  | [] -> (tc, false)
  | [stmt] -> 
    (* print_endline "Typechecking stmt"; *)
    let (tc', ret) = typecheck_stmt tc stmt to_ret in
    (* print_endline "Typechecked stmt"; *)
    if not ret then type_error stmt "Last statement in a block must return a value"; (tc', ret)
  | stmt :: rest ->
    (* print_endline "Typechecking stmt"; *)
    let (tc', ret) = typecheck_stmt tc stmt to_ret in
    (* print_endline "Typechecked stmt"; *)
    if ret then type_error stmt "Only the last statement in a block can return a value";
    typecheck_blk tc' rest to_ret

and typecheck_vdecl (tc : Tctxt.t) (vdecl : Ast.vdecl) : Tctxt.t =
  let (id, exp) = vdecl in
  let ty = typecheck_exp tc exp in
  if exist_local id tc then type_error exp "Invalid declaration"; add_local tc id ty

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is 
   is needed elswhere in the type system.
 *)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> (List.exists (fun x -> x.fieldName = h.fieldName) t) || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs  (l : 'a Ast.node) : unit =
  if check_dups fs
  then type_error l ("Repeated fields in " ^ id) 
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration 
    - extends the local context with the types of the formal parameters to the 
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)

let check_dups1 (xs : id list) : bool =
  let sorted_uniq_lst = List.sort_uniq compare xs in
  List.length sorted_uniq_lst <> List.length xs


let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let frtyp = f.frtyp in
  let args = f.args in
  let dupcheck = List.map snd f.args in
  if check_dups1 dupcheck then 
    type_error l ("Duplicate argument names in function " ^ f.fname)
  else
    (* NOTE FOR NOAH: Se tolgo questo blocco (prox. 4 righe), sblocchiamo 27 test in più :) *)
    let block = f.body in
    let tc' = List.fold_left (fun x (y, z) -> Tctxt.add_local x z y) tc args in
    (* print_endline "Compiling block"; *)
    let (_, x) = typecheck_blk tc' block frtyp in 
    if not x then type_error l "Function must return" else ()

(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2    


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)

let create_struct_ctxt (p:Ast.prog) : Tctxt.t =
  let fold_struct = 
    fun (prev_ctxt:Tctxt.t) (d:decl) : Tctxt.t -> 
      match d with
      | Gtdecl { elt = added_ctxt ; _} -> 
        let decl_id = (fst added_ctxt) in
        if Tctxt.lookup_struct_option decl_id prev_ctxt <> None then 
          raise (TypeError ("Duplicate struct definition " ^ decl_id))
        else
          let fields = (snd added_ctxt) in
          let appended_ctxt = Tctxt.add_struct prev_ctxt decl_id fields in
          appended_ctxt
      | _ -> prev_ctxt
  in
  let final_ctxt = List.fold_left fold_struct Tctxt.empty p in
  final_ctxt

let create_function_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let builtins_fold = fun (prev_ctxt:Tctxt.t) ((f_name, (params, re_ty)):(id * (ty list * ret_ty))) : Tctxt.t ->
    Tctxt.add_global prev_ctxt f_name (TRef (RFun (params, re_ty)))
  in
  let tc = List.fold_left builtins_fold tc builtins in
  let fold_func = 
    fun (prev_ctxt:Tctxt.t) (d:decl) : Tctxt.t -> 
      match d with
      | Gfdecl { elt = decl ; _} -> 
        if Tctxt.lookup_global_option decl.fname prev_ctxt <> None then 
          raise (TypeError ("Duplicate function definition " ^ decl.fname))
        else
          begin match decl.frtyp with
          | RetVal ty -> Tctxt.add_global prev_ctxt decl.fname (TRef (RFun (List.map fst decl.args, RetVal ty)))
          | RetVoid -> Tctxt.add_global prev_ctxt decl.fname (TRef (RFun (List.map fst decl.args, RetVoid)))
          end
      | _ -> prev_ctxt
  in
  let final_ctxt = List.fold_left fold_func tc p in
  final_ctxt

let create_global_ctxt (tc:Tctxt.t) (p:Ast.prog) : Tctxt.t =
  let tc = { structs = tc.structs; globals = tc.globals; locals = tc.locals } in
  let fold_func = 
    fun (prev_ctxt:Tctxt.t) (d:decl) : Tctxt.t -> 
      match d with
      | Gvdecl { elt = decl ; _} -> 
        if Tctxt.lookup_global_option decl.name prev_ctxt <> None then 
          raise (TypeError ("Duplicate global value definition " ^ decl.name))
        else
          let ty = 
          begin match decl.init.elt with
          | CNull rty -> (TNullRef rty)
          | CBool _ -> TBool
          | CInt _ -> TInt
          | CStr _ -> TRef RString
          | Id id -> 
            let looked_up_id = Tctxt.lookup_global_option id prev_ctxt in
            begin match looked_up_id with
              | Some ty -> ty
              | _ -> raise (TypeError ("Undefined symbol " ^ id))
            end
          | CArr (ty, _) -> TRef (RArray ty)
          | NewArr (ty, _, _, _) -> TRef (RArray ty)
          | Index (arr_exp_node, _) -> 
            let arr_ty = typecheck_exp prev_ctxt arr_exp_node in
            (* If `arr : ty[]` and `i : int`, then `arr[i] : ty` *)
            begin match arr_ty with
            | TRef (RArray ty) -> ty
            | _ -> type_error arr_exp_node decl.name
            end
          | Length _ -> TInt
          | CStruct (id, []) -> raise (TypeError ("Cannot initialize var " ^ decl.name ^ " to empty struct " ^ id))
          | CStruct (_, e::_) -> typecheck_exp prev_ctxt (snd e)
          | Proj (struct_exp_node, id) ->
            begin match struct_exp_node.elt with
            (* s.id is only valid if `s` is a struct type, and `id` is found inside `struct s` declaration *)
            | CStruct (s_name, _) -> 
              let field = lookup_field_option s_name id prev_ctxt in
              begin match field with
              | None -> type_error struct_exp_node id
              | Some ty -> ty
              end
            | _ -> type_error struct_exp_node id
            end
          | Call (f_exp, _) -> 
            let f_type = typecheck_exp prev_ctxt f_exp in
            begin match f_type with
            | TRef (RFun (_, RetVal ty)) -> ty
            | _ -> raise (TypeError "Could not get return type of function call")
            end
          | Bop (binop, _, _) -> 
            let _, _, re_ty = typ_of_binop binop in
            re_ty
          | Uop (unop, _) -> 
            snd (typ_of_unop unop)
          end in
          Tctxt.add_global prev_ctxt decl.name ty
      | _ -> prev_ctxt
  in
  let final_ctxt = List.fold_left fold_func tc p in
  final_ctxt


(* This function implements the |- prog and the H ; G |- prog 
   rules of the oat.pdf specification.   
*)
let typecheck_program (p:Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter (fun p ->
    match p with
    | Gfdecl ({elt=f} as l) -> typecheck_fdecl tc f l
    | Gtdecl ({elt=(id, fs)} as l) -> typecheck_tdecl tc id fs l 
    | _ -> ()) p
