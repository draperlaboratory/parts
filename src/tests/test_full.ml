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

(* let test_p_full input res _ = 
 *   let (res', remainder) =  P_json.p_full_json_opt 42 (Stream.of_string input, ((),[])) in 
 *   assert_equal res' res
 * 
 * let test_p_full_file filename _ = 
 *   let (res', remainder) =  P_json.p_full_json_opt 1000 (stream_file filename, ((),[])) in 
 *   Printf.printf "\n\n%s\n\n" (json_to_string res')
 *   (\* assert_equal res' res *\) (\* just checking that no error is raised *\)
 * 
 * 
 * let test_p_full_fail input _ = 
 *   assert_raises (Stdlib.Failure (Runtime.string_of_chars P_json.parse_exact_error_msg )) (fun _ -> 
 *       let _ =  P_json.p_full_json_opt 42 (Stream.of_string input, ((),[])) in ())
 * 
 * let test_true = test_p_full "true" (P_json.Json_bool true)
 * let test_false = test_p_full "false " (P_json.Json_bool false)
 * let test_false2 = test_p_full "   \n \n false " (P_json.Json_bool false)
 * let test_empty_list = test_p_full "[]" (P_json.Json_list [])
 * let test_bad_list = test_p_full_fail "][]"
 * let test_obj = test_p_full "{\"fred\":true}"  (P_json.Json_obj  [  (explode "fred"  , P_json.Json_bool true) ] )
 * let test_num = test_p_full "32 " (P_json.Json_num ['3' ; '2']) (\* whitespace still isn't right *\)
 * let test_null = test_p_full "null" (P_json.Json_null) (\* null is not implemented yet *\)
 * 
 * (\* This is run from deep within the _build directory  *\)
 * let test_file = test_p_full_file "../../../tests/examples/simple.json" (\* "/Users/philip/Documents/ocaml/cody-parts/code/src/tests/examples/simple.json"  *\)
 *            (\*  (P_json.Json_obj [ (explode "name" , P_json.Json_string (explode "John"));
 *                  (explode "age" , P_json.Json_num (explode "30")) ;
 *                  (explode "car" , P_json.Json_bool true) 
 *                                 ]) *\)
 * 
 * let test_glossary = test_p_full_file "../../../tests/examples/glossary.json" 
 * 
 * let test_webapp = test_p_full_file "../../../tests/examples/webapp.json" 
 * 
 * let test_widget = test_p_full_file "../../../tests/examples/widget.json" *) 


let full_json_suite = [
  (* "Parse true" >:: test_true;
   * "Parse false" >:: test_false;
   * "Parse 32" >:: test_num;
   * "Parse false with whitespace" >:: test_false2;
   * "Parse empty list" >:: test_empty_list;
   * "Unmatched RSQR fail" >:: test_bad_list;
   * "Test simple obj" >:: test_obj;
   * "Test simple from file" >:: test_file;
   * "Test glossary example from file" >:: test_glossary;
   * "Test webapp from file" >:: test_webapp;
   * "Test widget from file" >:: test_widget;
   * "Test null" >:: test_null; *)
]
(*

fix whitespace issue
try to run optimizations


*)
