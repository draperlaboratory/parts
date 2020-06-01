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

let benchmark_prefix = "../../../benchmarks/data/"

let sexp_filenames = [
    (262144,  "sexp/sexp.262144", 21946);
    (524288,  "sexp/sexp.524288", 43682);
    (786432,  "sexp/sexp.786432", 65542);
    (1048576, "sexp/sexp.1048576", 87567);
    (1310720, "sexp/sexp.1310720", 109565);
    (1572864, "sexp/sexp.1572864", 131623);
    (1835008, "sexp/sexp.1835008", 152657);
    (2097152, "sexp/sexp.2097152", 175043);
  ]

let build_test (st:'a) (m : 'a -> (char ocaml_stream, char) stream -> int)
               ((_, input, result) : int * string * int)
    : test =
  let file = benchmark_prefix ^ input in
  input >:: (fun _ -> assert_equal
                        (m st (make_stream (Runtime.from_file file)))
                        result)

let test_sexp_opt : test list =
  List.map (build_test ((),()) Example_parsers.Sexp.p_sexp_opt)
           sexp_filenames

let sexp_suite : test list =
  ["sexp_opt" >::: test_sexp_opt]
