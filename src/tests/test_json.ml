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
open P_json

let benchmark_prefix = "../../../benchmarks/data/"

let json_filenames = [
    (262144,  "json/collect_20.json", 440);
    (524288,  "json/collect_40.json", 880);
    (786432,  "json/collect_60.json", 1320);
    (1048576, "json/collect_80.json", 1760);
    (1310720, "json/collect_100.json", 2200);
    (1572864, "json/collect_120.json", 2640);
    (1835008, "json/collect_140.json", 3080);
    (2097152, "json/collect_160.json", 3520);
    (2097152, "json/collect_180.json", 3960);
  ]

let make_stream (str : 'a ocaml_stream) : ('a ocaml_stream, 'a) stream =
  { state = str; peek_st = (fun _ -> Runtime.ocaml_peek); drop_st = (fun _ -> Runtime.ocaml_drop) }

let build_test (st:'a) (m : 'a -> (char ocaml_stream, char) stream -> int)
               ((_, input, result) : int * string * int)
    : test =
  let file = benchmark_prefix ^ input in
  input >:: (fun _ -> assert_equal
                        (m st (make_stream (Runtime.from_file file)))
                        result)

let test_pjson_opt : test list =
  List.map (build_test ((),()) (P_json.p_full_json_opt))
           json_filenames

let pjson_suite : test list =
  ["pjson_opt" >::: test_pjson_opt]
