(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref true

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x ->
  match x with
    |Eq -> fz
    |Neq -> not fz
    |Lt -> fo <> fs
    |Le -> fz || (fo <> fs)
    |Gt -> not (fz || (fo <> fs))
    |Ge -> not (fo <> fs)


(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option = if addr >= mem_bot && addr < mem_top then Some (Int64.to_int (Int64.sub addr mem_bot)) else None

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

let option_to_int x : int =
  match x with
    |Some x -> x
    |None ->raise X86lite_segfault

let rec unifier (xs:operand list) (m:mach) : operand list = 
  match xs with
  | [] -> []
  | x :: xss ->
    match x with
    | Imm (Lit n) -> Imm (Lit n) :: unifier xss m
    | Ind1 (Lit n) -> Ind1 (Lit n) :: unifier xss m
    | Ind2 r -> Ind1 (Lit m.regs.(rind r)) :: unifier xss m
    | Ind3 (Lit x, y) -> Ind1 (Lit (Int64.add x m.regs.(rind y))) :: unifier xss m
    | Reg r -> Reg r :: unifier xss m

let frommem (m:mach) (x:int64) : sbyte list = let i = option_to_int (map_addr x) in let checking = map_addr (Int64.add x 7L) in [m.mem.(i); m.mem.(i+1); m.mem.(i+2); m.mem.(i+3); m.mem.(i+4); m.mem.(i+5); m.mem.(i+6); m.mem.(i+7)]
let tomem (m:mach) (x:int64) (y:sbyte list) : unit = let i = option_to_int (map_addr x) in let checking = map_addr (Int64.add x 7L) in m.mem.(i) <- List.nth y 0; m.mem.(i+1) <- List.nth y 1; m.mem.(i+2) <- List.nth y 2; m.mem.(i+3) <- List.nth y 3; m.mem.(i+4) <- List.nth y 4; m.mem.(i+5) <- List.nth y 5; m.mem.(i+6) <- List.nth y 6; m.mem.(i+7) <- List.nth y 7

let setter (m:mach) (x:bool list) : unit = let cur = m.flags in (cur.fo <- List.nth x 0; cur.fs <- List.nth x 1; cur.fz <- List.nth x 2)
let special_setter (m:mach) (x:bool list) : unit = let cur = m.flags in (cur.fs <- List.nth x 0; cur.fz <- List.nth x 1)
let equalbit (x:int64) : bool = let firstone = Int64.logand (Int64.shift_right x 63) 1L in let secondone = Int64.logand (Int64.shift_right x 62) 1L in firstone <> secondone
let most_sign (x:int64) : bool = let firstone = Int64.logand (Int64.shift_right x 63) 1L in firstone = 1L
let byte_setter (b:int64) (n : int64) : int64 = let clear = Int64.logand n (Int64.lognot 255L) in Int64.logor clear b


let step (m:mach) : unit =
  let InsB0 (operator, location) = m.mem.(option_to_int (map_addr m.regs.(rind Rip))) in m.regs.(rind Rip) <- Int64.add 8L m.regs.(rind Rip);
  match operator,(unifier location m) with
    | Movq, [Ind1 (Lit x); Reg y] -> let n = int64_of_sbytes (frommem m x) in m.regs.(rind y) <- n
    | Movq, [Imm (Lit x); Ind1 (Lit y)] -> let n = sbytes_of_int64 x in tomem m y n
    | Movq, [Reg x; Ind1 (Lit y)] -> let n = sbytes_of_int64 (m.regs.(rind x)) in tomem m y n
    | Movq, [Imm (Lit x); Reg y] -> m.regs.(rind y) <- x
    | Movq, [Reg x; Reg y] -> let n = m.regs.(rind x) in m.regs.(rind y) <- n
    | Pushq, [Reg x] -> let n = m.regs.(rind Rsp) in m.regs.(rind Rsp) <- Int64.sub n 8L; tomem m m.regs.(rind Rsp) (sbytes_of_int64 m.regs.(rind x))
    | Pushq, [Imm (Lit x)] -> let n = m.regs.(rind Rsp) in m.regs.(rind Rsp) <- Int64.sub n 8L; tomem m m.regs.(rind Rsp) (sbytes_of_int64 x)
    | Pushq, [Ind1 (Lit x)] -> let n = m.regs.(rind Rsp) in m.regs.(rind Rsp) <- Int64.sub n 8L; tomem m m.regs.(rind Rsp) (frommem m x)
    | Popq, [Reg x] -> let n = int64_of_sbytes (frommem m m.regs.(rind Rsp)) in m.regs.(rind x) <- n; m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L
    | Popq, [Ind1 (Lit x)] -> let n = frommem m m.regs.(rind Rsp) in tomem m x n; m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L
    | Leaq, [Ind1 (Lit x); Reg y] -> m.regs.(rind y) <- x
    | Addq, [Ind1 (Lit x); Reg y] -> let n = int64_of_sbytes (frommem m x) in let z = m.regs.(rind y) in let result = Int64_overflow.add n z in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Addq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64_overflow.add n z in (tomem m y (sbytes_of_int64 result.Int64_overflow.value); setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Addq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64_overflow.add n z in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Addq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64_overflow.add n z in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Addq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64_overflow.add n z in (tomem m y (sbytes_of_int64 result.Int64_overflow.value); setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Incq, [Ind1 (Lit x)] -> let n = int64_of_sbytes (frommem m x) in let result = Int64_overflow.succ n in (tomem m x (sbytes_of_int64 result.Int64_overflow.value); setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Incq, [Reg x] -> let n = m.regs.(rind x) in let result = Int64_overflow.succ n in (m.regs.(rind x) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Decq, [Ind1 (Lit x)] -> let n = int64_of_sbytes (frommem m x) in let result = Int64_overflow.pred n in (tomem m x (sbytes_of_int64 result.Int64_overflow.value); setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Decq, [Reg x] -> let n = m.regs.(rind x) in let result = Int64_overflow.pred n in (m.regs.(rind x) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Negq, [Ind1 (Lit x)] -> let n = int64_of_sbytes (frommem m x) in let result = Int64_overflow.neg n in (tomem m x (sbytes_of_int64 result.Int64_overflow.value); setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Negq, [Reg x] -> let n = m.regs.(rind x) in let result = Int64_overflow.neg n in (m.regs.(rind x) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Subq, [Ind1 (Lit x); Reg y] -> let n = int64_of_sbytes (frommem m x) in let z = m.regs.(rind y) in let result = Int64_overflow.sub z n in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Subq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64_overflow.sub n z in (tomem m y (sbytes_of_int64 result.Int64_overflow.value); setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Subq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64_overflow.sub n z in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Subq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64_overflow.sub n z in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Subq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64_overflow.sub n z in (tomem m y (sbytes_of_int64 result.Int64_overflow.value); setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L])
    | Imulq, [Ind1 (Lit x); Reg y] -> let n = int64_of_sbytes (frommem m x) in let z = m.regs.(rind y) in let result = Int64_overflow.mul z n in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; false; false])
    | Imulq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64_overflow.mul n z in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; false; false])
    | Imulq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64_overflow.mul n z in (m.regs.(rind y) <- result.Int64_overflow.value; setter m [result.Int64_overflow.overflow; false; false])
    | Notq, [Ind1 (Lit x)] -> let n = int64_of_sbytes (frommem m x) in let result = Int64.lognot n in tomem m x (sbytes_of_int64 result)
    | Notq, [Reg x] -> let n = m.regs.(rind x) in let result = Int64.lognot n in m.regs.(rind x) <- result
    | Andq, [Ind1 (Lit x); Reg y] -> let n = int64_of_sbytes (frommem m x) in let z = m.regs.(rind y) in let result = Int64.logand n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Andq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64.logand n z in (tomem m y (sbytes_of_int64 result); setter m [false; result < 0L; result = 0L])
    | Andq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64.logand n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Andq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64.logand n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Andq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64.logand n z in (tomem m y (sbytes_of_int64 result); setter m [false; result < 0L; result = 0L])
    | Orq, [Ind1 (Lit x); Reg y] -> let n = int64_of_sbytes (frommem m x) in let z = m.regs.(rind y) in let result = Int64.logor n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Orq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64.logor n z in (tomem m y (sbytes_of_int64 result); setter m [false; result < 0L; result = 0L])
    | Orq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64.logor n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Orq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64.logor n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Orq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64.logor n z in (tomem m y (sbytes_of_int64 result); setter m [false; result < 0L; result = 0L])
    | Xorq, [Ind1 (Lit x); Reg y] -> let n = int64_of_sbytes (frommem m x) in let z = m.regs.(rind y) in let result = Int64.logxor n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Xorq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64.logxor n z in (tomem m y (sbytes_of_int64 result); setter m [false; result < 0L; result = 0L])
    | Xorq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64.logxor n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Xorq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64.logxor n z in (m.regs.(rind y) <- result; setter m [false; result < 0L; result = 0L])
    | Xorq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64.logxor n z in (tomem m y (sbytes_of_int64 result); setter m [false; result < 0L; result = 0L])
    | Sarq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64.shift_right n (Int64.to_int z) in (tomem m y (sbytes_of_int64 result); if z <> 0L then (if z = 1L then setter m [false; result < 0L; result = 0L] else special_setter m [result < 0L; result = 0L]))
    | Sarq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64.shift_right n (Int64.to_int z) in (m.regs.(rind y) <- result; if z <> 0L then (if z = 1L then setter m [false; result < 0L; result = 0L] else special_setter m [result < 0L; result = 0L]))
    | Sarq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64.shift_right n (Int64.to_int z) in (m.regs.(rind y) <- result; if z <> 0L then (if z = 1L then setter m [false; result < 0L; result = 0L] else special_setter m [result < 0L; result = 0L]))
    | Sarq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64.shift_right n (Int64.to_int z) in (tomem m y (sbytes_of_int64 result); if z <> 0L then (if z = 1L then setter m [false; result < 0L; result = 0L] else special_setter m [result < 0L; result = 0L]))
    | Shlq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64.shift_left n (Int64.to_int z) in (tomem m y (sbytes_of_int64 result); if z <> 0L then (if z = 1L then setter m [equalbit n; result < 0L; result = 0L] else special_setter m [result < 0L; result = 0L]))
    | Shlq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64.shift_left n (Int64.to_int z) in (m.regs.(rind y) <- result; if z <> 0L then (if z = 1L then setter m [equalbit n; result < 0L; result = 0L] else special_setter m [result < 0L; result = 0L]))
    | Shlq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64.shift_left n (Int64.to_int z) in (m.regs.(rind y) <- result; if z <> 0L then (if z = 1L then setter m [equalbit n; result < 0L; result = 0L] else special_setter m [result < 0L; result = 0L]))
    | Shlq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64.shift_left n (Int64.to_int z) in (tomem m y (sbytes_of_int64 result); if z <> 0L then (if z = 1L then setter m [equalbit n; result < 0L; result = 0L] else special_setter m [result < 0L; result = 0L]))
    | Shrq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64.shift_right_logical n (Int64.to_int z) in (tomem m y (sbytes_of_int64 result); if z <> 0L then (if z = 1L then setter m [most_sign n; most_sign result; result = 0L] else special_setter m [most_sign result; result = 0L]))
    | Shrq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64.shift_right_logical n (Int64.to_int z) in (m.regs.(rind y) <- result; if z <> 0L then (if z = 1L then setter m [most_sign n; most_sign result; result = 0L] else special_setter m [most_sign result; result = 0L]))
    | Shrq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64.shift_right_logical n (Int64.to_int z) in (m.regs.(rind y) <- result; if z <> 0L then (if z = 1L then setter m [most_sign n; most_sign result; result = 0L] else special_setter m [most_sign result; result = 0L]))
    | Shrq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64.shift_right_logical n (Int64.to_int z) in (tomem m y (sbytes_of_int64 result); if z <> 0L then (if z = 1L then setter m [most_sign n; most_sign result; result = 0L] else special_setter m [most_sign result; result = 0L]))
    | Set x, [Reg y] -> let n = m.regs.(rind y) in if interp_cnd m.flags x then m.regs.(rind y) <- byte_setter 1L n else m.regs.(rind y) <- byte_setter 0L n
    | Set x, [Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in if interp_cnd m.flags x then tomem m y (sbytes_of_int64 (byte_setter 1L n)) else tomem m y (sbytes_of_int64 (byte_setter 0L n))
    | Cmpq, [Ind1 (Lit x); Reg y] -> let n = int64_of_sbytes (frommem m x) in let z = m.regs.(rind y) in let result = Int64_overflow.sub z n in setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L]
    | Cmpq, [Reg x; Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let z = m.regs.(rind x) in let result = Int64_overflow.sub n z in setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L]
    | Cmpq, [Reg x; Reg y] -> let n = m.regs.(rind y) in let z = m.regs.(rind x) in let result = Int64_overflow.sub n z in setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L]
    | Cmpq, [Imm (Lit z); Reg y] -> let n = m.regs.(rind y) in let result = Int64_overflow.sub n z in setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L]
    | Cmpq, [Imm (Lit z); Ind1 (Lit y)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64_overflow.sub n z in setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L]
    | Cmpq, [Reg y; Imm (Lit z)] -> let n = m.regs.(rind y) in let result = Int64_overflow.sub z n in setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L]
    | Cmpq, [Ind1 (Lit y); Imm (Lit z)] -> let n = int64_of_sbytes (frommem m y) in let result = Int64_overflow.sub z n in setter m [result.Int64_overflow.overflow; result.Int64_overflow.value < 0L; result.Int64_overflow.value = 0L]
    | Jmp, [Ind1 (Lit x)] -> let n = int64_of_sbytes (frommem m x) in m.regs.(rind Rip) <- n
    | Jmp, [Reg x] -> let n = m.regs.(rind x) in m.regs.(rind Rip) <- n
    | Jmp, [Imm (Lit x)] -> m.regs.(rind Rip) <- x
    | J y, [Ind1 (Lit x)] -> if interp_cnd m.flags y then let n = int64_of_sbytes (frommem m x) in m.regs.(rind Rip) <- n
    | J y, [Reg x] -> if interp_cnd m.flags y then let n = m.regs.(rind x) in m.regs.(rind Rip) <- n
    | J y, [Imm (Lit x)] -> if interp_cnd m.flags y then m.regs.(rind Rip) <- x
    | Callq, [Ind1 (Lit x)] -> let n = m.regs.(rind Rsp) in m.regs.(rind Rsp) <- Int64.sub n 8L; tomem m m.regs.(rind Rsp) (sbytes_of_int64 m.regs.(rind Rip)); let n = int64_of_sbytes (frommem m x) in m.regs.(rind Rip) <- n
    | Callq, [Reg x] -> let n = m.regs.(rind Rsp) in m.regs.(rind Rsp) <- Int64.sub n 8L; tomem m m.regs.(rind Rsp) (sbytes_of_int64 m.regs.(rind Rip)); let n = m.regs.(rind x) in m.regs.(rind Rip) <- n
    | Callq, [Imm (Lit x)] -> let n = m.regs.(rind Rsp) in m.regs.(rind Rsp) <- Int64.sub n 8L; tomem m m.regs.(rind Rsp) (sbytes_of_int64 m.regs.(rind Rip)); m.regs.(rind Rip) <- x
    | Retq, [] -> let n = int64_of_sbytes (frommem m m.regs.(rind Rsp)) in m.regs.(rind Rip) <- n; m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L
    | _ -> raise X86lite_segfault

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Computes the size of the text segment in a program *)
let size_of_text_segment (p:prog) : quad =
  List.fold_left (fun acc elem ->
    match elem.asm with
    | Text instructions -> Int64.add acc (Int64.mul ins_size (Int64.of_int (List.length instructions))) (* acc + 8 * (length instructions) *)
    | Data _ -> acc  (* ignore data segments *)
  ) 0L p

let operand_addr_helper (imm:imm) (base_addr:quad) : ((lbl * quad) list) * quad =
  let new_base_addr = ref base_addr in
  match imm with
  | Lbl x -> 
    new_base_addr := Int64.add base_addr ins_size;
    [(x, base_addr)], !new_base_addr
  | _ -> [], base_addr

let lbl_assign_addr (op:operand) (base_addr:quad) : ((lbl * quad) list) * quad =
  match op with
  | Imm imm 
  | Ind1 imm
  | Ind3 (imm, _) -> 
    let (re_sym, re_ba) = (operand_addr_helper imm base_addr) in (re_sym, re_ba)
  | _ -> [], base_addr
  
(* Builds a symbol table (i.e. a table that associates each label 
   with its absolute address) out of the given program.
*)
let build_symbol_tbl (p:prog) (base_addr_text:quad) (base_addr_data:quad) : (lbl * quad) list =
  let symbol_tbl = ref [] in
  let base_addr_text = ref base_addr_text in
  let base_addr_data = ref base_addr_data in
  List.iter (fun elem ->
    match elem.asm with
    | Text _ -> symbol_tbl := !symbol_tbl @ [(elem.lbl, !base_addr_text)]; 
                              base_addr_text := Int64.add !base_addr_text ins_size
    | Data _ -> symbol_tbl := !symbol_tbl @ [(elem.lbl, !base_addr_data)]; 
                              base_addr_data := Int64.add !base_addr_data ins_size
  ) p;
  !symbol_tbl

let build_text_seg (p:prog) : sbyte list =
  List.fold_left (fun (acc:sbyte list) (e:elem) : sbyte list ->
    match e.asm with
    | Text ins_list -> acc @ (List.concat (List.map (fun ins -> (if !debug_simulator then print_endline @@ (string_of_ins ins)); sbytes_of_ins ins) ins_list))
    | Data _ -> acc
  ) [] p 

let build_data_seg (p:prog) : sbyte list =
  List.fold_left (fun (acc:sbyte list) (e:elem) : sbyte list ->
    match e.asm with
    | Text _ -> acc
    | Data data_list -> acc @ (List.concat (List.map sbytes_of_data data_list))
  ) [] p 

(* Looks up label inside symble table and returns absolute address *)
let rec sym_tbl_lookup (l:lbl) (sym_tbl:(lbl * quad) list) : quad = 
  match sym_tbl with
  | [] -> raise (Undefined_sym l)
  | ((label, addr) :: tbl) -> 
      if label = l then addr
      else sym_tbl_lookup l tbl

(* Iterates through program p and resolves all Lbls inside instructions to their absolute value based on the contents of sym_tbl, 
   or raises an Undefined_sym exception if a label cannot be found in sym_tbl 
*)
let resolve_lbls (sym_tbl:(lbl * quad) list) (p:prog) : prog = 
  List.map (
    fun (e:elem) : elem -> 
      begin
        match e.asm with
        | Text instrs -> 
          let new_instrs = (List.map (
            fun (((opcode:opcode), (operands:operand list)):ins) : ins -> 
              (opcode, List.map (
                fun (o:operand) : operand -> 
                  begin
                    match o with
                    | Imm imm ->
                      begin
                        match imm with
                        | Lbl lbl -> Imm (Lit (sym_tbl_lookup lbl sym_tbl))
                        | Lit quad -> Imm (Lit quad)
                      end
                    | Ind1 imm -> 
                      begin
                        match imm with
                        | Lbl lbl -> Ind1 (Lit (sym_tbl_lookup lbl sym_tbl))
                        | Lit quad -> Ind1 (Lit quad)
                      end
                    | Ind3 (imm, reg) -> let new_imm = (
                      fun (i:imm) ->
                        match i with
                        | Lbl lbl -> Lit (sym_tbl_lookup lbl sym_tbl)
                        | Lit quad -> Lit quad
                      ) imm in 
                      Ind3 (new_imm, reg)
                    | _ -> o
                  end
              ) operands)
          ) instrs) in
          { lbl = e.lbl; global = e.global; asm = Text new_instrs }
        | Data x -> { lbl = e.lbl; global = e.global; asm = Data x }
      end
  ) p
(* Convert an X86 program into an object file:
  - separate the text and data segments
  - compute the size of each segment
    Note: the size of an Asciz string section is (1 + the string length)
          due to the null terminator

  - resolve the labels to concrete addresses and 'patch' the instructions to 
    replace Lbl values with the corresponding Imm values.

  - the text segment starts at the lowest address
  - the data segment starts after the text segment

HINT: List.fold_left and List.fold_right are your friends.
*)
let assemble (p:prog) : exec =
  let entry = 0L in
  let text_pos = mem_bot in
  let data_pos = Int64.add text_pos (size_of_text_segment p) in
  let sym_table = build_symbol_tbl p text_pos data_pos in
  let resolved_prog = resolve_lbls sym_table p in
  let text_seg = build_text_seg resolved_prog in
  let data_seg = build_data_seg resolved_prog in 
  let main_checker = (sym_tbl_lookup "main" sym_table) in
  {entry = entry; text_pos = text_pos; data_pos = data_pos; text_seg = text_seg; data_seg = data_seg}
(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
failwith "load unimplemented"