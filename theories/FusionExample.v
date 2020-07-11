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

From stdpp Require Import strings countable list.
From ParTS Require Import Machine Opt Evaluators.
Import Byte.

(* I'm going to build a recognizer for:

     "strings of 'a's and 'b's with at most 3 'a's"

   I'll do this in 3 steps to provide some opportunities to explore fusion.

   First I'll "tokenize" a stream of characters into tokens for just 'a' and
   'b', rejecting streams where other characters are present (but maybe it would
   be more interesting to drop the other characters?).

   Second I'll parse streams of these tokens into a number - the number of 'a's.

   Third I'll accepts numbers less than 4 (?).  Is this parsing in any sense?
   Also early failure will require some understanding that the intermediate
   number never decreases, which seems hard.
*)

Inductive ab_tok := A | B.

From stdpp Require Import base tactics.

Instance eqat : EqDecision ab_tok.
Proof.
  solve_decision.
Defined.

Definition encode_ab : ab_tok -> () + () :=
  fun ab => match ab with
            | A => inl ()
            | B => inr ()
            end.

Definition decode_ab : () + () -> option ab_tok :=
  fun sum => match sum with
             | inl _ => Some A
             | inr _ => Some B
             end.

Instance count_ab : Countable ab_tok.
Proof.
  apply inj_countable with (f := encode_ab)(g := decode_ab).
  intros x; destruct x; simpl; auto.
Defined.

Lemma to_N_inj : forall x y, to_N x = to_N y <-> x = y.
Proof.
  intros; split; intros.
  Check of_to_N.
  - generalize (f_equal of_N H).
    intros.
    repeat rewrite of_to_N in *.
    congruence.
    
  - congruence.
Qed.

Definition rewrite_dec : forall A B : Prop, (A <-> B) -> (Decision A -> Decision B).
Proof.
  intros A B H D.
  destruct D.
  - left; rewrite <- H; auto.
  - right; rewrite <- H; auto.
Defined.

Local Open Scope byte_scope.

Instance eqdec_byte : EqDecision byte.
Proof.
  intro x; intro y.
  case_eq (x =? y).
  - intros; left.
    apply byte_dec_bl; done.
  - intros; right; apply eqb_false; done.
Defined.


Eval cbv in (fun x y : byte => decide (x = y)).

Eval cbv in bool_decide ("a"%byte = "b"%byte).


(**************)
(* Tokenizing *)
(**************)
Definition parse_tok {rv} : Machine rv () byte byte ab_tok :=
       (^ "a" @> return_ A)
   <|> (^ "b" @> return_ B).

Definition tokenizer {rv} : Machine rv () _ _ (list ab_tok) :=
  parse_list parse_tok.

(**************)
(* Parsing    *)
(**************)


Definition parse_exact_ab {st rv} : Machine rv st _  _ ab_tok := ^ A @> ^ B.

(* Goal here is to parse a list of ab_toks into a maximum number of A's that
   appear in a row.  Because we have a writer monad rather than state, I don't
   think we can do this with "parse_list" because it doesn't update the state of
   the subsequent elements.

   Instead I'm building all the logic into a custom parse_list in a way that
   feels gross.

 *)

(* Here we define the state for our parser.  We need to track the how many As
   immediately precede the current token, the max number of consecutive As overall,
   and the last token.
 *)
Record MaxState : Set := MkMaxState
                           { current_run : nat;
                             overall_max  : nat }.

(* How to update the state based on what token is next. *)
Definition A_updater (st : MaxState) :=
  match st with
  | MkMaxState cr om => MkMaxState (S cr) (max (S cr) om)
  end.

Definition B_updater (st : MaxState) :=
  match st with
  | MkMaxState cr om => MkMaxState 0 om
  end.

(* The parser itself - reimplementing some of the work of parse_list but
   explicitly passing on the state. *)
Definition count_As {rv} : Machine rv MaxState ab_tok ab_tok nat :=
  parse_fix (fun rec_f =>
               peek (singleton A)
                    (write A_updater (drop (Var rec_f)))
                    (* We don't check that it's a B here, as that's the only possiblity *)
                    (write B_updater (drop (Var rec_f)))
                    (read (fun state => return_ (overall_max state)))).

Definition initial_MaxState := MkMaxState 0 0.


Definition CountState := nat.

Definition A_counter (st : CountState) := S st.

Definition B_counter (st : CountState) := 0.

Definition initial_CountState := 0.

(* Definition halt_if_gt (max : nat) (n : nat) : Machine CountState ab_tok () := *)
(*   parse_fix n (validate_step *)
(*                  (fun t state => match t with A => bool_decide (state < max) | _ => true end) *)
(*                  (fun t state => match t with A => A_counter state | B => B_counter state end)). *)

(* Some examples of parsing lists all the way, except I don't understand how to
    compose...

   Can almost do it with bind, but for the problem that the states don't match.

   Thinking about Parsec: parsec folks don't even usually separate parsing and
   lexing.  The programmer kind of manually fuses these phases.  So is this kind
   of optimization even needed with parser combinators?  Now I'm a little concerned
   about our motivation...
 *)
Definition max_one := ["a"; "b"; "b"; "a"].
Definition max_two := ["a"; "a"; "b"; "a"].
Definition max_three := ["a"; "a"; "b"; "a"; "a"; "a"; "b"; "a"; "b"].

Definition max_runner (l : list byte) : ErrorT nat :=
  match eval_m 10 tokenizer () l with
  | (inr l', _, _) => (eval_m 10 (count_As) initial_MaxState l').1.1
  | (inl err,_,_) => inl err
  end.


Eval vm_compute in (eval_m 10 parse_tok () ["b"]).
Eval vm_compute in (eval_m 10 tokenizer () max_three).

Eval vm_compute in max_runner max_one.
Eval vm_compute in max_runner max_two.
Eval vm_compute in max_runner max_three.


Eval vm_compute in (eval_m 10 tokenizer () max_three).

(* good! *)
Eval cbv in (eval_m_prop_stream parse_tok (fun o _ _ => o)).

(* not good! *)
Eval cbn in (eval_m_prop_stream parse_tok (fun o _ _ => o)).



Require Import Extraction.
Require Import Coq.extraction.ExtrOcamlNativeString Coq.extraction.ExtrOcamlNatInt Coq.extraction.ExtrOcamlZInt.

Eval cbv in fun t => decide (A = t).
Eval simpl in  _ : EqDecision ab_tok.

Extract Inlined Constant eqat => "(=)".

(*
Definition dump_fix : Machine unit _ _ _ := fun _ =>
  parse_fix () (fun v => ^ A  ).
Definition compile_dump_fix : { f | f =  fun s => (eval_m_prop_stream (dump_fix _) None Unknown  (fun o _ _ => o) tt (dummy_stream s))}. compile. Defined.
Extraction compile_dump_fix.
*)


Definition parse_fix_ab {rv} : Machine rv unit _ _ ab_tok :=
  parse_fix (fun v => ^ A <|> ^ B @> (Var v)).

Unset Guard Checking.

Definition compile_fix_ab : { f | f =  fun s => (eval_m_prop_stream parse_fix_ab (fun o _ _ => o) tt (dummy_stream s))}. vm_compute. compile. Defined.


Extraction compile_fix_ab.

Lemma foo : forall st' ,{ f | f =  eval_stream (st':=st') parse_tok A tt }. compile. Defined.

Lemma foo'' : { f | f =
                    fun s =>
                      (eval_m_prop_stream
                         parse_tok
                         (fun o m_st' st' =>
                            (eval_m_prop_stream parse_exact_ab)
                              (fun o _ _ => o)
                              ()
                              (eval_stream parse_tok o m_st' (dummy_stream st'))))
                        ()
                        (dummy_stream s)
              }.
Proof.
  compile.
Defined.

Extraction foo''.

Lemma foo''' : { f | f =
                     fun s =>
                       compose_parser
                         parse_tok
                         parse_exact_ab
                         () ()
                         (dummy_stream s)}.
Proof.
  compile.
Defined.

Extraction foo'''.

Definition tokenize_opt : Opt tokenizer.
Proof.
  compile.
Defined.
