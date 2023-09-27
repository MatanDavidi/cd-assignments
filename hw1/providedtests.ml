open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> prob3_ans) 42 );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);

  Test ("Student-Provided Tests For Problem 5", [
    ("case1", assert_eqf (fun () -> interpret sm_ctxt1 p1) (run sm_ctxt1 (compile p1)) );
    ("case2", assert_eqf (fun () -> interpret sm_ctxt1 p2) (run sm_ctxt1 (compile p2)) );
    ("case3", assert_eqf (fun () -> interpret sm_ctxt1 p3) (run sm_ctxt1 (compile p3)) );
    ("case4", assert_eqf (fun () -> interpret sm_ctxt1 p4) (run sm_ctxt1 (compile p4)) );
    ("case5", assert_eqf (fun () -> interpret sm_ctxt2 p5) (run sm_ctxt2 (compile p5)) );
    ("case6", assert_eqf (fun () -> interpret sm_ctxt2 p6) (run sm_ctxt2 (compile p6)) );
    ("case8", assert_eqf (fun () -> interpret sm_ctxt4 p8) (run sm_ctxt4 (compile p8)) );
    ("case9", assert_eqf (fun () -> interpret sm_ctxt5 p9) (run sm_ctxt5 (compile p9)) );
    ("case10", assert_eqf (fun () -> interpret sm_ctxt6 p10) (run sm_ctxt6 (compile p10)) );
    ("case11", assert_eqf (fun () -> interpret sm_ctxt7 p11) (run sm_ctxt7 (compile p11)) );
    ("case12", assert_eqf (fun () -> interpret sm_ctxt2 p1) (run sm_ctxt2 (compile p1)) );
    ("case13", assert_eqf (fun () -> interpret sm_ctxt2 p2) (run sm_ctxt2 (compile p2)) );
    ("case14", assert_eqf (fun () -> interpret sm_ctxt2 p3) (run sm_ctxt2 (compile p3)) );
    ("case15", assert_eqf (fun () -> interpret sm_ctxt2 p4) (run sm_ctxt2 (compile p4)) );
    ("case16", assert_eqf (fun () -> interpret sm_ctxt3 p5) (run sm_ctxt3 (compile p5)) );
    ("case17", assert_eqf (fun () -> interpret sm_ctxt3 p6) (run sm_ctxt3 (compile p6)) );
    ("case18", assert_eqf (fun () -> interpret sm_ctxt5 p8) (run sm_ctxt5 (compile p8)) );
    ("case19", assert_eqf (fun () -> interpret sm_ctxt6 p9) (run sm_ctxt6 (compile p9)) );
    ("case20", assert_eqf (fun () -> interpret sm_ctxt2 p12) (run sm_ctxt2 (compile p12)) );
    ("case21", assert_eqf (fun () -> interpret sm_ctxt3 p12) (run sm_ctxt3 (compile p12)) );
    ("case22", assert_eqf (fun () -> interpret sm_ctxt7 p12) (run sm_ctxt7 (compile p12)) );
    ("case23", assert_eqf (fun () -> interpret [] p13) (run [] (compile p13)))
  ]);
  
] 
