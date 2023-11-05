open Assert
open X86
open Ll
open Backend

(* Do NOT modify this file -- we will overwrite it with our *)
(* own version when we test your project.                   *)

(* These tests will be used to grade your assignment *)

let size_ty_tests =
  [ ("ty_size1", assert_eqf (fun () -> size_ty [] I1) 8)
  ; ("ty_size3", assert_eqf (fun () -> size_ty [] I64) 8)
  ; ("ty_size4", assert_eqf (fun () -> size_ty [] (Ptr Void)) 8)
  ; ("ty_size2", assert_eqf (fun () -> size_ty [] (Ptr I1)) 8)
  ; ("ty_size5", assert_eqf (fun () -> size_ty [] (Array (3, I64))) 24)
  ; ("ty_size6", assert_eqf
    (fun () -> size_ty [] (Struct [I64; I1; Ptr I8; Ptr I64; Array (10, I1) ])) 112)
  ; ("ty size7", assert_eqf
    (fun () -> size_ty [("O", I1);("S", I64)] (Struct [Namedt "O"; (Array (2, Namedt "S"))])) 24)
  ]

let arg_loc_tests =
  []

let exec_e2e_ast ll_ast args extra_files =
  let output_path = !Platform.output_path in
  let dot_s_file = Platform.gen_name output_path "test" ".s" in
  let exec_file = Platform.gen_name output_path "exec" "" in
  let asm_ast = Backend.compile_prog ll_ast in
  let asm_str = X86.string_of_prog asm_ast in
  let _ = Driver.write_file dot_s_file asm_str in
  let _ = Platform.link (dot_s_file::extra_files) exec_file in
  let result = Driver.run_executable args exec_file in
  let _ = Platform.sh (Printf.sprintf "rm -f %s %s" dot_s_file exec_file) Platform.ignore_error in
  let _ = Platform.verb @@ Printf.sprintf "** Executable exited with: %d\n" result in
  Int64.of_int result


let exec_e2e_file path args =
  let ast = Driver.parse_ll_file path in
  exec_e2e_ast ast args []

let io_test path args =
  let ll_ast = Driver.parse_ll_file path in
  let output_path = !Platform.output_path in
  let dot_s_file = Platform.gen_name output_path "test" ".s" in
  let exec_file = Platform.gen_name output_path "exec" "" in
  let tmp_file = Platform.gen_name output_path "tmp" ".txt" in
  let asm_ast = Backend.compile_prog ll_ast in
  let asm_str = X86.string_of_prog asm_ast in
  let _ = Driver.write_file dot_s_file asm_str in
  let _ = Platform.link (dot_s_file::["cinterop.c"]) exec_file in
  let args = String.concat " " args in
  let result = Driver.run_program args exec_file tmp_file in
  let _ = Platform.sh (Printf.sprintf "rm -f %s %s %s" dot_s_file exec_file tmp_file) Platform.ignore_error in
  let _ = Platform.verb @@ Printf.sprintf "** Executable output:\n%s\n" result in
  result

let c_link_test c_files path args =
  let ll_ast = Driver.parse_ll_file path in
  let output_path = !Platform.output_path in
  let dot_s_file = Platform.gen_name output_path "test" ".s" in
  let exec_file = Platform.gen_name output_path "exec" "" in
  let asm_ast = Backend.compile_prog ll_ast in
  let asm_str = X86.string_of_prog asm_ast in
  let _ = Driver.write_file dot_s_file asm_str in
  let _ = Platform.link (dot_s_file::c_files) exec_file in
  let args = String.concat " " args in
  let result = Driver.run_executable args exec_file in
  let _ = Platform.sh (Printf.sprintf "rm -f %s %s" dot_s_file exec_file) Platform.ignore_error in
    Int64.of_int result

let executed tests =
  List.map (fun (fn, ans) ->
      fn, assert_eqf (fun () -> exec_e2e_file fn "") ans)
    tests

let executed_io tests =
  List.map (fun (fn, args, ans) ->
      (fn ^ ":" ^ (String.concat " " args)), assert_eqf (fun () -> io_test fn args) ans)
    tests

let executed_c_link tests =
  List.map (fun (c_file, fn, args, ans) ->
      (fn ^ ":" ^ (String.concat " " args)), assert_eqf (fun () -> c_link_test c_file fn args) ans)
    tests

let binop_tests =
  [ "llprograms/add.ll", 14L
  ; "llprograms/sub.ll", 1L
  ; "llprograms/mul.ll", 45L
  ; "llprograms/and.ll", 0L
  ; "llprograms/or.ll",  1L
  ; "llprograms/xor.ll", 0L
  ; "llprograms/shl.ll", 168L
  ; "llprograms/lshr.ll", 10L
  ; "llprograms/ashr.ll", 5L ]

let calling_convention_tests =
  [ "llprograms/call.ll", 42L
  ; "llprograms/call1.ll", 17L
  ; "llprograms/call2.ll", 19L
  ; "llprograms/call3.ll", 34L
  ; "llprograms/call4.ll", 34L
  ; "llprograms/call5.ll", 24L
  ; "llprograms/call6.ll", 26L
  ]

let memory_tests =
  [ "llprograms/alloca1.ll", 17L
  ; "llprograms/alloca2.ll", 17L
  ; "llprograms/global1.ll", 12L
  ]

let terminator_tests =
  [ "llprograms/return.ll", 0L
  ; "llprograms/return42.ll", 42L
  ; "llprograms/br1.ll", 9L
  ; "llprograms/br2.ll", 17L
  ; "llprograms/cbr1.ll", 7L
  ; "llprograms/cbr2.ll", 9L
  ; "llprograms/duplicate_lbl.ll", 1L
  ]

let bitcast_tests =
  [ "llprograms/bitcast1.ll", 3L
  ]

let gep_tests =
  [ "llprograms/gep1.ll", 6L
  ; "llprograms/gep2.ll", 4L
  ; "llprograms/gep3.ll", 1L
  ; "llprograms/gep4.ll", 2L
  ; "llprograms/gep5.ll", 4L 
  ; "llprograms/gep6.ll", 7L
  ; "llprograms/gep7.ll", 7L
  ; "llprograms/gep8.ll", 2L 
  ]

let io_tests =
  [ "llprograms/helloworld.ll", [], "hello, world!"
  ; "llprograms/string1.ll", [], "hello, world!hello, world!"
  ; "llprograms/callback1.ll", [], "38"
  ; "llprograms/args1.ll", ["hello"], "argc < 3"
  ; "llprograms/args1.ll", ["hello"; "compilerdesign"], "hellocompilerdesign"
  ; "llprograms/args1.ll", ["hello"; "compilerdesign"; "foo"], "argc > 3"
  ]

(* Hidden *)
let hidden_large_tests =
  []

let large_tests = [ "llprograms/list1.ll", 3L
                  ; "llprograms/cbr.ll", 42L
                  ; "llprograms/factorial.ll", 120L
                  ; "llprograms/factrect.ll", 120L
                  ; "llprograms/duplicate_factorial.ll", 240L
                  ]

let prefix = "./compiler-design-eth-tests/03"

let dbernhard_tests = [
    prefix ^ "/dbernhard/load_simple.ll", 23L
  ; prefix ^ "/dbernhard/square.ll", 144L
  ; prefix ^ "/dbernhard/square_ptr.ll", 144L
  ; prefix ^ "/dbernhard/return_pointer.ll", 42L
  ; prefix ^ "/dbernhard/bitcast_1.ll", 255L
  ; prefix ^ "/dbernhard/bitcast_2.ll", 24L
  ; prefix ^ "/dbernhard/swap_none.ll", 42L (* performs NO swap *)
  ; prefix ^ "/dbernhard/swap_1.ll", 10L (* swaps once*)
  ; prefix ^ "/dbernhard/swap_2.ll", 42L (* swaps twice (same as no swap)*)
  ; prefix ^ "/dbernhard/arguments_1.ll", 100L (* tests if all 10 arguments are taken into account *)
  ; prefix ^ "/dbernhard/arguments_2.ll", 55L (* unique 10 arguments get summed up *)
  ; prefix ^ "/dbernhard/arguments_3.ll", 65L (* test if the last argument is correct *)
  ; prefix ^ "/dbernhard/update_global_value.ll", 44L (* updating of a global variable *)
  ; prefix ^ "/dbernhard/gep_inside_struct.ll", 42L (* index inside a struct which contains an array *)
  ; prefix ^ "/dbernhard/gep_inside_struct_array.ll", 11L (* index inside an array which is inside a struct *)
  ; prefix ^ "/dbernhard/gep_twice.ll", 199L
]

let gep_tests = 
  [ prefix ^ "/nicdard/gep0.ll", 1L
  ]

let local_names = 
  [ prefix ^ "/nicdard/local_names.ll", 29L
  ]

let return_tests = 
  [ prefix ^ "/nicdard/return42_2.ll", 42L 
  ]

(* The following tests files where already included in the project material, but they were not run in gradedtests.ml. *)
let arithmetic_missing_tests = 
  [ prefix ^ "/nicdard/add_twice.ll", 29L
  ; prefix ^ "/nicdard/arith_combo.ll", 4L
  ; prefix ^ "/nicdard/arith_combo_dce.ll", 4L
  ; prefix ^ "/nicdard/arith_combo_fold.ll", 4L
  ]

let gep_missing_tests = 
  [ prefix ^ "/nicdard/gep9.ll", 5L
  ; prefix ^ "/nicdard/gep10.ll", 3L
  ]

let analysis_missing_tests = 
  [ prefix ^ "/nicdard/analysis10_cf_opt.ll", 60L 
  ; prefix ^ "/nicdard/analysis10_dce_opt.ll", 60L 
  ; prefix ^ "/nicdard/analysis10.ll", 60L 
  ; prefix ^ "/nicdard/analysis11_cf_opt.ll", 3L 
  ; prefix ^ "/nicdard/analysis11_dce_opt.ll", 3L 
  ; prefix ^ "/nicdard/analysis11.ll", 3L 
  ; prefix ^ "/nicdard/analysis12_cf_opt.ll", 14L 
  ; prefix ^ "/nicdard/analysis12_dce_opt.ll", 14L 
  ; prefix ^ "/nicdard/analysis12.ll", 14L 
  ; prefix ^ "/nicdard/analysis13_cf_opt.ll", 7L
  ; prefix ^ "/nicdard/analysis13_dce_opt.ll", 7L
  ; prefix ^ "/nicdard/analysis13.ll", 7L 
  ; prefix ^ "/nicdard/analysis14_cf_opt.ll", 42L 
  ; prefix ^ "/nicdard/analysis14_dce_opt.ll", 42L 
  ; prefix ^ "/nicdard/analysis14.ll", 42L 
  ; prefix ^ "/nicdard/analysis15_cf_opt.ll", 2L 
  ; prefix ^ "/nicdard/analysis15_dce_opt.ll", 2L 
  ; prefix ^ "/nicdard/analysis15.ll", 2L
  ; prefix ^ "/nicdard/analysis16.ll", 1L
  ; prefix ^ "/nicdard/analysis18_cf_opt.ll", 42L 
  ; prefix ^ "/nicdard/analysis18_dce_opt.ll", 42L 
  ; prefix ^ "/nicdard/analysis18.ll", 42L 
  ; prefix ^ "/nicdard/analysis19_cf_opt.ll", 5L
  ; prefix ^ "/nicdard/analysis19_dce_opt.ll", 5L
  ; prefix ^ "/nicdard/analysis19.ll", 5L 
  ; prefix ^ "/nicdard/analysis1_cf_opt.ll", 49L 
  ; prefix ^ "/nicdard/analysis1.ll", 49L 
  ; prefix ^ "/nicdard/analysis2_cf_opt.ll", 8L 
  ; prefix ^ "/nicdard/analysis2.ll", 8L
  ; prefix ^ "/nicdard/analysis3_cf_opt.ll", 188L 
  ; prefix ^ "/nicdard/analysis3_dce_opt.ll", 188L 
  ; prefix ^ "/nicdard/analysis3.ll", 188L 
  ; prefix ^ "/nicdard/analysis4_cf_opt.ll", 254L 
  ; prefix ^ "/nicdard/analysis4.ll", 254L 
  ; prefix ^ "/nicdard/analysis5_cf_opt.ll", 14L 
  ; prefix ^ "/nicdard/analysis5_dce_opt.ll", 14L 
  ; prefix ^ "/nicdard/analysis5.ll", 14L 
  ; prefix ^ "/nicdard/analysis6_cf_opt.ll", 2L 
  ; prefix ^ "/nicdard/analysis6_dce_opt.ll", 2L  
  ; prefix ^ "/nicdard/analysis7.ll", 10L 
  ; prefix ^ "/nicdard/analysis8_cf_opt.ll", 95L 
  ; prefix ^ "/nicdard/analysis8_dce_opt.ll", 95L 
  ; prefix ^ "/nicdard/analysis8.ll", 95L  
  ; prefix ^ "/nicdard/analysis9.ll", 0L
  (* The following tests are rejected by clang due to ssa numbering order problems, 
     but are accepted by llinterp. *)
  ; prefix ^ "/nicdard/analysis16_cf_opt.ll", 1L
  ; prefix ^ "/nicdard/analysis16_dce_opt.ll", 1L
  ; prefix ^ "/nicdard/analysis1_dce_opt.ll", 49L
  ; prefix ^ "/nicdard/analysis4_dce_opt.ll", 254L
  ; prefix ^ "/nicdard/analysis7_cf_opt.ll", 10L
  ; prefix ^ "/nicdard/analysis7_dce_opt.ll", 10L
  ; prefix ^ "/nicdard/analysis9_cf_opt.ll", 0L
  ; prefix ^ "/nicdard/analysis9_dce_opt.ll", 0L
  (* The following tests do not run with the provided llinterp due to i1 invalid operand 
     (althought accepted by clang). *)
  ; prefix ^ "/nicdard/analysis2_dce_opt.ll", 8L
  ]

let zikai_tests = [
    prefix ^ "/zikai/nested_structs.ll", 16L
  ; prefix ^ "/zikai/nested_structs2.ll", 8L
  ; prefix ^ "/zikai/nested_structs3.ll", 127L
]

let nicdard_tests = gep_tests
  @ local_names
  @ return_tests
  @ analysis_missing_tests
  @ gep_missing_tests
  @ arithmetic_missing_tests  
  

let tests : suite =
  [ GradedTest("size_ty tests", 5, size_ty_tests)
  ; GradedTest("arg_loc tests", 5, arg_loc_tests)
  ; GradedTest("executed binop tests", 5, executed binop_tests)
  ; GradedTest("terminator tests", 10, executed terminator_tests)
  ; GradedTest("memory tests", 10, executed memory_tests)
  ; GradedTest("calling convention tests", 15, executed calling_convention_tests)
  ; GradedTest("bitcast tests", 2, executed bitcast_tests)
  ; GradedTest("gep tests", 10, executed gep_tests)
  ; GradedTest("large tests", 10, executed large_tests)
  ; GradedTest("hidden large tests", 18, hidden_large_tests)
  ; GradedTest("io tests", 10, executed_io io_tests)
  ; GradedTest("dbernhard tests", 0, executed dbernhard_tests)
  ; GradedTest("nicdard test", 0, executed nicdard_tests)
  ; GradedTest("zikai test", 0, executed zikai_tests)
  ]



let graded_tests : suite =
  tests
