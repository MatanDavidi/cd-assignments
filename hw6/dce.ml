(** Dead Code Elimination  *)
open Ll
open Datastructures


(* expose a top-level analysis operation ------------------------------------ *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)
let dce_block (lb:uid -> Liveness.Fact.t) 
              (ab:uid -> Alias.fact)
              (b:Ll.block) : Ll.block =
(* TODO: THIS FUNCTION IS NOT COMPLETELY CORRECT! 13/15 *)
  let is_id_non_aliased id = 
    try
    not (UidM.mem id (ab id))
    with Not_found -> true
  in
  let is_id_dead id = 
    try
    not (UidS.mem id (lb id))
    with Not_found -> false
  in
  let is_ins_dead = 
    fun ((id, ins):(uid * insn)) : bool ->
      begin match ins with
      | Binop _
      | Alloca _
      | Load _
      | Icmp _
      | Bitcast _
      | Gep _ -> is_id_dead id
      | Store (_, _, op2) -> 
        begin match op2 with
        | Gid did | Id did -> is_id_non_aliased did && is_id_dead did
        | _ -> failwith "Cannot store into null or constant"
        end
      | Call _ -> false
      end
  in
  {
    insns = List.filter (fun a -> not (is_ins_dead a)) b.insns;
    term = b.term
  }

let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg

