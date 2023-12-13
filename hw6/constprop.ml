open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t

let translate_op (op:Ll.operand) (d:fact) : Ll.operand =
  begin match op with
  | Id id | Gid id -> 
    let op_res = UidM.find_opt id d in
    begin match op_res with
    | Some (SymConst.Const a) -> Ll.Const a
    | _ -> op
    end
  | _ -> op
  end

(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let insn_flow (u,i:uid * insn) (d:fact) : fact =
  match i with
  | Binop (bop, _, op1, op2) -> 
    let op1 = translate_op op1 d in
    let op2 = translate_op op2 d in
    begin match op1 with
    | Const val1 -> 
      begin match op2 with
      | Const val2 ->
        let new_val = 
          begin match bop with
          | Add -> Int64.add val1 val2
          | Sub -> Int64.sub val1 val2
          | Mul -> Int64.mul val1 val2
          | Shl -> Int64.shift_left val1 (Int64.to_int val2)
          | Lshr -> Int64.shift_right_logical val1 (Int64.to_int val2)
          | Ashr -> Int64.shift_right val1 (Int64.to_int val2)
          | And -> Int64.logand val1 val2
          | Or -> Int64.logor val1 val2
          | Xor -> Int64.logxor val1 val2 
          end
        in
        UidM.add u (SymConst.Const new_val) d
      | _ -> UidM.add u SymConst.NonConst d
      end
    | _ -> UidM.add u SymConst.NonConst d
    end
  | Icmp (cnd, _, op1, op2) -> 
    let op1 = translate_op op1 d in
    let op2 = translate_op op2 d in
    begin match op1 with
    | Const val1 -> 
      begin match op2 with
      | Const val2 -> 
        let new_val = 
          begin match cnd with
          | Eq -> val1 = val2
          | Ne -> val1 <> val2
          | Slt -> val1 < val2
          | Sle -> val1 <= val2
          | Sgt -> val1 > val2
          | Sge -> val1 >= val2
          end
        in
        UidM.add u (SymConst.Const (if new_val then 1L else 0L)) d
      | _ -> UidM.add u SymConst.NonConst d
      end
    | _ -> UidM.add u SymConst.NonConst d
    end
  | Store (ty, _, _) -> 
    begin match ty with
    | Void -> UidM.add u SymConst.UndefConst d
    | _ -> d
    end
  | Call (ty, _, _) ->
    begin match ty with
    | Void -> UidM.add u SymConst.UndefConst d
    | _ -> UidM.add u SymConst.NonConst d
    end
  | Alloca _
  | Load _
  | Bitcast _
  | Gep _ -> UidM.add u SymConst.NonConst d

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let combine (ds:fact list) : fact = 
      let combine_helper (a: SymConst.t) (b: SymConst.t) : SymConst.t =
        match (a, b) with
        | (Const a, _) | (_, Const a) -> Const a
        | _ -> NonConst
      in
      List.fold_left (fun acc d -> 
        UidM.merge (fun _ a b ->
          match a, b with
          | Some v, None | None, Some v -> Some v
          | Some v1, Some v2 -> Some (combine_helper v1 v2)
          | None, None -> None
        ) acc d) UidM.empty ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg

  let helper (id:uid) (d:fact) : Ll.operand =
    let op = UidM.find_opt id d in
    begin match op with
    | Some (SymConst.Const val1) -> Const val1
    | _ -> Id id
    end

(* helper functions for running constant propagation ------------------------- *)
let ins_helper (uid : uid) (t : terminator) (cb : uid -> Fact.t) ((id,insn) : Ll.uid * Ll.insn) : (uid * Ll.insn) = 
  let new_ins =
  begin match insn with
  | Binop (bop, ty, Id id1, Id id2) -> Binop(bop, ty, helper id1 (cb id), helper id2 (cb id))
  | Binop (bop, ty, Id id1, op2) -> Binop(bop, ty, helper id1 (cb id), op2)
  | Binop (bop, ty, op1, Id id2) -> Binop(bop, ty, op1, helper id2 (cb id))
  | Call (ty, op, ops) -> 
    Call (ty, op, List.map (fun (x, y) -> 
      match y with
      | Id id1 -> (x, helper id1 (cb id))
      | _ -> (x, y)
    ) ops)
  | Bitcast (ty1, Id id1, ty2) -> Bitcast (ty1, helper id1 (cb id), ty2)
  | Store (ty, Id id1, op) -> Store (ty, helper id1 (cb id), op)
  | Icmp (cnd, ty, Id id1, Id id2) -> Icmp (cnd, ty, helper id1 (cb id), helper id2 (cb id))
  | Icmp (cnd, ty, Id id1, op2) -> Icmp (cnd, ty, helper id1 (cb id), op2)
  | Icmp (cnd, ty, op1, Id id2) -> Icmp (cnd, ty, op1, helper id2 (cb id))
  | _ -> insn
  end
  in (id, new_ins)

let term_helper (uid : uid) (t : terminator) (cb : uid -> Fact.t) : (uid*Ll.terminator) = 
  begin match t with 
  | Ret (ty, Some (Id id)) -> (uid, Ret(ty, Some (helper id (cb uid))))
  | Cbr (Id id, lbl_1, lbl_2) -> (uid, Cbr(helper id (cb uid), lbl_1, lbl_2))
  | _ -> (uid, t)           
  end 

(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    let (uid, typ) = b.term in 
    Cfg.add_block l {insns = List.map (ins_helper uid typ cb) b.insns; term = term_helper uid typ cb;} cfg
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
