open Assert
open X86
open Simulator
open Sp15_tests
open Sp17_tests
open Sp18_tests
open Sp20_tests

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)


let provided_tests : suite = [
  Test ("Debug", 
  Sp15_tests.tests @
  Sp17_tests.tests @
  Sp18_tests.tests @
  Sp20_tests.tests);
] 
