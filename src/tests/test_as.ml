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
open Example_parsers

let tests : (string * int) list =
  [("",0);
   ("a",1);
   ("aaa",3);
   ("aaabaaaaaa",3);
   ("aaaaaaaaaa",10);
   ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",30);
   ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaab",30);
   ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaba",30);
   ("aabaaaaaaaaaaaaaaaaaaaaaaaaaaaaba",2)
  ]

let build_test (st:'a) (m : 'a -> (char ocaml_stream, char) stream -> int)
               ((input, result) : string * int)
             : test =
  input >:: (fun _ -> assert_equal (m st (make_stream (Runtime.from_string input))) result)


let test_count_as_opt : test list =
  List.map (build_test () JustAs.p_count_as_opt) tests

let test_count_as_state_opt : test list =
  List.map (build_test 0 JustAs.p_count_as_state_opt) tests

let count_as_suite : test list =
  ["count_as" >::: test_count_as_opt;
   "count_as_state" >::: test_count_as_state_opt]
