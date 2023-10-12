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
let debug_simulator = ref false

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

let size_of_text_segment (p:prog) : quad =
  List.fold_left (fun acc elem ->
    match elem.asm with
    | Text instructions -> Int64.add acc (Int64.mul ins_size (Int64.of_int (List.length instructions))) (* acc + 8 * (length instructions) *)
    | Data _ -> acc  (* ignore data segments *)
  ) 0L p

(* Builds a symbol table (i.e. a table that associates each label 
   with its absolute address) out of the given program.
*)
(* let build_symbol_tbl (p:prog) : (lbl * quad) list =
  List.map (fun e:elem -> 
    match e.asm with
    | Text ins_list -> []
    | Data data_list -> []
  ) p *)

let build_text_seg (p:prog) : sbyte list =
  List.fold_left (fun (acc:sbyte list) (e:elem) : sbyte list ->
    match e.asm with
    | Text ins_list -> acc @ (List.concat (List.map sbytes_of_ins ins_list))
    | Data _ -> [(Byte ' ')]
  ) [] p 

let build_data_seg (p:prog) : sbyte list =
  List.fold_left (fun (acc:sbyte list) (e:elem) : sbyte list ->
    match e.asm with
    | Text _ -> [(Byte ' ')]
    | Data data_list -> acc @ (List.concat (List.map sbytes_of_data data_list))
  ) [] p 

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
  (* let sym_table = build_symbol_tbl p in *)
  let entry = 0L in
  let text_pos = mem_bot in
  let data_pos = Int64.add text_pos (size_of_text_segment p) in
  let text_seg = [] (*build_text_seg p*) in
  let data_seg = [] in 
  {entry; text_pos; data_pos; text_seg; data_seg}
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