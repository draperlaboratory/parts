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

Require Import Machine Evaluators.
From stdpp Require Import base.


Unset Guard Checking.
(**

    These definitions allow us to specify the unoptimized and optimized versions of a parser,
    respectively.

    Note that we use eval_M_stream to generate code that gets evaluated at runtime, since
    the eval_M_prop version does more work, it will *fail* at runtime before even getting
    its input.

*)

Definition IsUnOpt `(t : Machine _ st tok tag out) `{BInfo tok tag} e :=
  forall (state : st)
         (input : stream (ocaml_stream tok) tok),
    eval_m_stream t (fun out _ _ => out) state input = e state input.

Definition IsOpt `(t : Machine _ st tok tag out) `{BInfo tok tag} e :=
  forall (state : st)
         (input : stream (ocaml_stream tok) tok),
    eval_m_prop_stream t (fun out _ _ => out) state input = e state input.

Hint Unfold eval_m_stream.
Hint Unfold eval_m_prop_stream.

(* For a given term t, Opt t is the type of all the machines which are
   optimizations of t. Thus, building an instance of `Opt t` is
   equivalence to generating an optimized version of t. *)
Definition Opt {st tag tok out} `{BInfo tok tag} (t : Machine _ st tok tag out) := { m | IsOpt t m }.

Definition UnOpt {st tag tok out} `{binfo : BInfo tok tag} (t : Machine _ st tok tag out) := { m | IsUnOpt t m }.



(* This tactic introduces the target machine as a meta-variable, and
   unfolds and simplifies t, such that we end up with the version we
   probably want to extract, barring additional optimizations.

  Note that reflexivity always solves an IsOpt goal created using this
  tactic, unifying the introduced meta-variable.  *)
Ltac unfold_opt := eexists; intro; intros;
                   autounfold; simpl; autounfold; simpl.


Ltac compile :=  eexists;
                 cbv -[Byte.eqb Ascii.eqb Ascii.ascii_dec parse_exact_error_msg eof];
                 simpl; auto.
