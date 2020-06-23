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

open ParTS
open P_json
open Benchmarks

let json_filenames = [
    20,  "json/collect_20.json";
    40,  "json/collect_40.json";
    60,  "json/collect_60.json";
    80,  "json/collect_80.json";
    100, "json/collect_100.json";
    120, "json/collect_120.json";
    140, "json/collect_140.json";
    160, "json/collect_160.json";
    180, "json/collect_180.json";
  ]

let json_args : int list =
  List.map fst json_filenames

let make_stream (str : 'a ocaml_stream) : ('a ocaml_stream, 'a) stream =
  {
    state = str;
    peek_st = (fun _ -> Runtime.ocaml_peek);
    drop_st = (fun _ -> Runtime.ocaml_drop);
    lookahead_st = (fun _ -> Runtime.ocaml_lookahead);
  }

(* A runner for any of the benchmarks *)
let run_test (n:int)
             (filenames : (int*string) list)
             (p : 'a -> (char ocaml_stream, char) ParTS.P_json.stream -> 'out)
             (init_state : 'a) =
  (* XXX the way we hard code this location here is brittle.  Would be better
     to do with a command line argument, but core_bench has its own scheme for
     arguments that I'm not sure how to futz with *)
  let filename = "src/benchmarks/data/" ^ (List.assoc n filenames) in
  Core.Staged.stage
    (fun () ->
      let stream = filename |> Runtime.from_file |> make_stream in
      try ignore (p init_state stream)
      with
      | Runtime.Parse_fail _ ->
         Printf.printf "Warning - a test on file %s failed.\n" filename)


let run_json (n:int) =
  run_test n json_filenames (P_json.p_full_json_opt) ((),())

open Core
open Core_bench

let () =
  Command.run (Bench.make_command [
    Bench.Test.create_indexed ~name:"json" ~args:json_args run_json
  ])
