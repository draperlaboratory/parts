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
open Benchmarks

let as_filenames = [
    (10000,  "as/as.10000");
    (20000,  "as/as.20000");
    (30000,  "as/as.30000");
    (40000,  "as/as.40000");
    (50000,  "as/as.50000");
    (100000, "as/as.100000");
    (200000, "as/as.200000");
    (300000, "as/as.300000");
    (400000, "as/as.400000");
    (500000, "as/as.500000");
  ]

let as_args : int list =
  List.map fst as_filenames

let run_as_opt (n:int) =
  run_test n as_filenames (Example_parsers.JustAs.p_count_as_opt) ()

let run_as_state_opt (n:int) =
  run_test n as_filenames (Example_parsers.JustAs.p_count_as_state_opt) (0)

open Core
open Core_bench

let () =
  Command.run (Bench.make_command [
    Bench.Test.create_indexed ~name:"count_as_opt"       ~args:as_args run_as_opt;
    Bench.Test.create_indexed ~name:"count_as_state_opt" ~args:as_args run_as_state_opt
  ])
