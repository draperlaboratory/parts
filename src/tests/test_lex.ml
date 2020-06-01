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

(* let test_p_lex input res _ = 
 *   let res' =  P_json.p_lex_opt 42 (Stream.of_string input, []) in 
 *   assert_equal res' res
 * 
 * let test_p_lex_fail input _ = 
 *   assert_raises (Stdlib.Failure (Runtime.string_of_chars P_json.parse_exact_error_msg )) (fun _ -> 
 *       let _ =  P_json.p_lex_opt 42 (Stream.of_string input, []) in ())
 * 
 * 
 * let test_p_lex_rsqr = test_p_lex "]" [RSQR]
 * let test_p_lex_lsqr = test_p_lex "[" [LSQR]
 * let test_p_lex_lcurl = test_p_lex "{" [LCURL]
 * let test_p_lex_string = test_p_lex "\"hello world\"" [STRING (explode "hello world")]
 * let test_p_lex_num = test_p_lex "42 " [NUMBER (explode "42")]
 * let test_p_lex_num' = test_p_lex " 42 " [NUMBER (explode "42")] (\* Fails? *\)
 * let test_p_lex_num3 = test_p_lex "42" [NUMBER (explode "42")] (\* Fails? *\)
 * let test_p_lex_string2 = test_p_lex_fail "hello world"(\* Should "hello world" parse as nothing? *\)
 * let test_p_lex_obj = test_p_lex "{\"fred\":true}"  [LCURL; STRING (explode "fred") ; COL ; TRUE ;  RCURL] *) 

let lex_json_suite = [
  (* "test_p_lex_rsqr" >:: test_p_lex_rsqr;
   * "test_p_lex_lsqr" >:: test_p_lex_lsqr;
   * "test_p_lex_lcurl" >:: test_p_lex_lcurl;
   * "test_p_lex_string" >:: test_p_lex_string;
   * "test_p_lex_num" >:: test_p_lex_num;
   * "Lex a num with whitespace" >:: test_p_lex_num';
   * "test_p_lex_num3" >:: test_p_lex_num3;
   * "test_p_lex_string2'" >:: test_p_lex_string2;
   * "test_p_lex_obj" >:: test_p_lex_obj *)
]
