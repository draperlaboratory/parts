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

(* let test_p_json input res _ = 
 *   let res' =  P_json.p_json_opt 42 (Stream.of_list input, ()) in 
 *   assert_equal res' res
 * 
 * let test_p_json_fail input _ = 
 *   assert_raises (Stdlib.Failure (Runtime.string_of_chars P_json.parse_exact_error_msg )) (fun _ -> 
 *       let _ =  P_json.p_json_opt 42 (Stream.of_list input, ()) in ())
 * (\*
 * let test_p_json_fail_string input _ = 
 *   assert_raises (Stdlib.Failure (Runtime.string_of_chars P_json.parse_exact_error_msg)) (fun _ -> 
 *       let _ =  P_json.p_json_opt 42 (Stream.of_list input, ()) in ())
 * *\)
 * let test_p_json_true _ = 
 *   let res =  P_json.p_json_opt 42 (Stream.of_list [P_json.TRUE], ()) in 
 *   assert_equal res (P_json.Json_bool true)
 * 
 * let test_p_json_false _ = 
 *   let res =  P_json.p_json_opt 42 (Stream.of_list [P_json.FALSE], ()) in 
 *   assert_equal res (P_json.Json_bool false)
 * 
 * let test_p_json_num _ = 
 *   let res =  P_json.p_json_opt 42 (Stream.of_list [P_json.NUMBER ['1']], ()) in 
 *   assert_equal res (P_json.Json_num ['1'])
 * 
 * let test_p_json_num _ = 
 *   let res =  P_json.p_json_opt 42 (Stream.of_list [P_json.NUMBER ['1']], ()) in 
 *   assert_equal res (P_json.Json_num ['1'])
 * 
 * 
 * let test_p_json_string _ = 
 *   let res =  P_json.p_json_opt 42 (Stream.of_list [P_json.STRING (explode "foobar")], ()) in 
 *   assert_equal res (P_json.Json_string (explode "foobar"))
 * 
 * let test_p_json_list = test_p_json [P_json.LSQR; P_json.TRUE; P_json.RSQR]  (P_json.Json_list [P_json.Json_bool true])
 * 
 * let test_p_json_list2 = test_p_json [P_json.LSQR; P_json.TRUE; P_json.COMMA; P_json.TRUE; P_json.RSQR]  (P_json.Json_list [P_json.Json_bool true; P_json.Json_bool true])
 * 
 * let test_p_json_list_fail = test_p_json_fail [RSQR ; LSQR]
 * 
 * let test_p_json_list_fail2 = test_p_json_fail [RSQR]
 * 
 * let test_p_json_list_fail3 = test_p_json_fail [RSQR ; TRUE; TRUE; LSQR]
 * 
 * let test_p_json_nest_list = test_p_json [LSQR; LSQR; RSQR; RSQR]  (P_json.Json_list [P_json.Json_list []])
 * 
 * let test_p_json_dict = test_p_json [P_json.LCURL; P_json.STRING (explode "field_name"); P_json.COL ; P_json.TRUE; P_json.RCURL]  (P_json.Json_obj [  ( explode "field_name" ,  P_json.Json_bool true )   ])
 * 
 * let test_p_json_dict2 = test_p_json [P_json.LCURL; P_json.STRING (explode "fred"); P_json.COL ; P_json.TRUE; P_json.COMMA;  P_json.STRING (explode "larry"); P_json.COL ; P_json.FALSE; P_json.RCURL]  (P_json.Json_obj [  ( explode "fred" ,  P_json.Json_bool true ) ; ( explode "larry" ,  P_json.Json_bool false )   ])
 * 
 * let test_p_json_dict_fail = test_p_json_fail [P_json.LCURL; P_json.STRING (explode "foobar") ;  P_json.TRUE; P_json.RCURL] 
 * 
 * let test_p_json_dict_fail2 = test_p_json_fail [P_json.LCURL; P_json.STRING (explode "foobar") ;  P_json.STRING (explode "foobar"); P_json.TRUE; P_json.RCURL] *) 

let parse_json_suite = [
  (* "test_p_json_true" >:: test_p_json_true;
   * "test_p_json_false" >:: test_p_json_false;
   * "test_p_json_num" >:: test_p_json_num;
   * "test_p_json_list" >:: test_p_json_list;
   * "test_p_json_list2" >:: test_p_json_list2;
   * "test_p_json_list_fail" >:: test_p_json_list_fail;
   * "test_p_json_list_fail2" >:: test_p_json_list_fail2;
   * "test_p_json_list_fail3" >:: test_p_json_list_fail3;
   * "test_p_json_nest_list" >:: test_p_json_nest_list;
   * "test_p_json_dict" >:: test_p_json_dict;
   * "test_p_json_dict2" >:: test_p_json_dict2;
   * "test_p_json_dict_fail" >:: test_p_json_dict_fail;
   * "test_p_json_dict_fail2" >:: test_p_json_dict_fail2 *)
]
