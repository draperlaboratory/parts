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

let ppm_filenames = [
    (10*10,   "ppm/popl2019_twitter_avatar_10x10.ppm");
    (14*14,   "ppm/popl2019_twitter_avatar_14x14.ppm");
    (20*20,   "ppm/popl2019_twitter_avatar_20x20.ppm");
    (28*28,   "ppm/popl2019_twitter_avatar_28x28.ppm");
    (40*40,   "ppm/popl2019_twitter_avatar_40x40.ppm");
    (56*56,   "ppm/popl2019_twitter_avatar_56x56.ppm");
    (80*80,   "ppm/popl2019_twitter_avatar_80x80.ppm");
    (113*113, "ppm/popl2019_twitter_avatar_113x113.ppm");
    (160*160, "ppm/popl2019_twitter_avatar_160x160.ppm");
    (226*226, "ppm/popl2019_twitter_avatar_226x226.ppm");
  ]

let ppm_args : int list =
  List.map fst ppm_filenames

let run_ppm (n:int) =
  run_test n ppm_filenames (Example_parsers.PPM.p_ppm_opt) ((),())

open Core
open Core_bench

let () =
  Command.run (Bench.make_command [
    Bench.Test.create_indexed ~name:"ppm" ~args:ppm_args run_ppm
  ])
