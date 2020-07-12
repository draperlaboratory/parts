(* Copyright (c) 2020 The Charles Stark Draper Laboratory, Inc.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *)

open OUnit2
open ParTS
open Utils

(* let test_parse_3_2 res l = 
 *   let res' = Parse_3_2.compile_parse_3_2 (Stream.of_list l, ()) in
 *   assert_equal res' res
 * 
 * let test_parse_3_2_correct _ = 
 *   test_parse_3_2 (3,2) [3 ; 2]
 * 
 * 
 * let test_parse_3_2_correct' _ = 
 *   test_parse_3_2 (3,2) [3 ; 2 ; 6; 8]
 * 
 * let test_parse_3_2_fail _ = 
 *   assert_raises (Stdlib.Failure (Runtime.string_of_chars P_json.parse_exact_error_msg)) (fun _ -> 
 *       let _ = Parse_3_2.compile_parse_3_2 (Stream.of_list [2 ; 2; 2], ()) in ())
 * 
 * let test_parse_3_or_4_correct _ = 
 *   let n =  Parse_3_or_4.compile_parse_3_or_4 (Stream.of_list [3;2], ()) in 
 *   assert_equal 3 n
 * 
 * let test_parse_3_or_4_correct' _ = 
 *   let n =  Parse_3_or_4.compile_parse_3_or_4 (Stream.of_list [4;2], ()) in 
 *   assert_equal 4 n
 * 
 * let test_parse_3_or_4_fail _ = 
 *   assert_raises (Stdlib.Failure (Runtime.string_of_chars P_json.parse_exact_error_msg)) (fun _ -> 
 *       let _ =  Parse_3_or_4.compile_parse_3_or_4 (Stream.of_list [2 ; 2; 2], ()) in ()) *)





let parse_3_2_suite =[
  (* "test_parse_3_2_correct" >:: test_parse_3_2_correct;
   * "test_parse_3_2_correct'" >:: test_parse_3_2_correct';
   * "test_parse_3_2_fail"      >:: test_parse_3_2_fail *)
]

let parse_3_or_4_suite = [
  (* "test_parse_3_or_4_correct" >:: test_parse_3_or_4_correct;
   * "test_parse_3_or_4_correct'" >:: test_parse_3_or_4_correct';
   * "test_parse_3_or_4_fail"      >:: test_parse_3_or_4_fail *)
]

let suite =
  "Unit Tests" >::: [
    "Parse_3_2"         >::: parse_3_2_suite;
    "Parse_3_or_4"      >::: parse_3_or_4_suite;
    "Parse_Json"        >::: Test_parse.parse_json_suite;
    "Lex_JSon"          >::: Test_lex.lex_json_suite;
    "Full_Parse_Json"   >::: Test_full.full_json_suite;
    "Count_As_Tests"    >::: Test_as.count_as_suite;
    "Sexp_Tests"        >::: Test_sexp.sexp_suite;
    "Json_Tests"        >::: Test_json.pjson_suite;
    "PPM_Tests"         >::: Test_ppm.ppm_suite;
  ]

let _ = run_test_tt_main suite
