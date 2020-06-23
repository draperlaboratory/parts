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

Require Import Machine Json Evaluators ExampleParsers.
From stdpp Require Import base.
Require Extraction.
Require Import Coq.extraction.ExtrOcamlString Coq.extraction.ExtrOcamlNatInt Coq.extraction.ExtrOcamlZInt.

Unset Guard Checking.

Require Import Opt FusionExample.

Extract Inlined Constant fix_ => "Runtime.fix".

Extract Inlined Constant failwith => "Runtime.failwith_".
Extract Inlined Constant let_ => "Runtime.let_".
Extract Inlined Constant ocaml_peek => "Runtime.ocaml_peek".
Extract Inlined Constant ocaml_drop => "Runtime.ocaml_drop".
Extract Inlined Constant ocaml_lookahead => "Runtime.ocaml_lookahead".
Extract Inlined Constant ocaml_eq => "(=)".
Extract Inlined Constant ocaml_or => "(||)".
Extract Inlined Constant ocaml_plus => "(+)".
Extract Inlined Constant ocaml_lte => "(<=)".

Extract Inlined Constant ocaml_gte => "(>=)".
Extract Inlined Constant ocaml_and => "(&&)".
Extract Constant ocaml_stream "'a" => "'a Runtime.stream_t".
(*
Variable ocaml_stream_fromfile : string -> ocaml_stream byte.
*)

Definition id_k {A B C} : A -> B -> C -> A := fun o _ _ => o.

Require Import Ascii.
Require Import stdpp.base stdpp.strings.

Eval cbv in parse_exact.
Eval cbv -[decide] in eval_m_prop_stream (parse_exact _ A).
Eval cbv in (fun _ => ^ "a" <|> ^ "b" ).
Eval cbv in fun s => eval_m_prop_stream  (^ "a" <|> ^ "b" ) id_k () (dummy_stream s).
Eval cbv -[orb] in fun s => eval_m_prop_stream  (^ "a" <|> (^ "b" <|>  (^ "c" <|>  (^ "d" <|>  ^ "e")))) id_k () (dummy_stream s).
Eval cbv -[orb] in fun s => eval_m_prop_stream  (^ "a" <|> ^ "b" <|>  ^ "c" <|>  ^ "d" <|>  ^ "e") id_k () (dummy_stream s).
(*


Ok, we can hide orb, or we could make it an axiom.

I want equalities to sometimes compute and sometimes not
The dynamic equality can always be not computed.

vm_compute and native_compute would be preferable


*)


Definition compile_whitespace : { f | f =  fun s => (eval_m_prop_stream Common.whitespace_char id_k () (dummy_stream s))}.
Proof.
  vm_compute.  eexists. auto. Defined.
Print compile_whitespace.
Extraction compile_whitespace.

Definition compile_whitespace'' : { f | f =  fun s => (eval_m_prop_stream (call Common.whitespace_char (fun _ => Common.whitespace_char)) id_k () (dummy_stream s))}.
Proof.
  vm_compute. eexists. auto. Defined.
Print compile_whitespace.
Extraction compile_whitespace''.


Definition compile_lower_ : { f | f =  fun s => (eval_m_prop_stream Common.lower_ id_k () (dummy_stream s))}.
Proof.
  vm_compute.  eexists. auto. Defined.
Print compile_whitespace.
Extraction compile_lower_.

Definition compile_alpha_ : { f | f =  fun s => (eval_m_prop_stream Common.alpha_ id_k () (dummy_stream s))}.
Proof.
  vm_compute.  eexists. auto. Defined.
Extraction compile_alpha_.

Definition compile_alphanum : { f | f =  fun s => (eval_m_prop_stream Common.alphanum id_k () (dummy_stream s))}.
Proof.
  vm_compute.  eexists. auto. Defined.
Extraction "compile_alphanum.ml" compile_alphanum.

Eval cbv in Common.whitespace.
Definition compile_whitespace' : { f | f =  fun s => (eval_m_prop_stream Common.whitespace id_k () (dummy_stream s))}.
Proof.
  cbv. eexists. auto. Defined.
Extraction compile_whitespace'.

Definition compile_staralphanum : { f | f =  fun s => (eval_m_prop_stream (Common.star (Common.alphanum)) id_k () (dummy_stream s))}.

  vm_compute. eexists. auto. Defined.

Extraction compile_staralphanum.
Definition compile_lex_one : { f | f =  fun s => (eval_m_prop_stream Sexp.lex_one id_k () (dummy_stream s))}.
Proof.
  vm_compute.  eexists. auto. Defined.
Print compile_lex_one.


Extraction "lex_one.ml" compile_lex_one.
Definition compile_lexer : { f | f =  fun s => (eval_m_prop_stream Sexp.lexer id_k () (dummy_stream s))}.
Proof.
  vm_compute. eexists. auto.
Defined.

Extraction "lexer.ml" compile_lexer.

(*


Print compile_lex_one.

Extract Constant ocaml_eq => "(=)".
Extraction  "compile_lex_one.ml" compile_lex_one .
Extraction compile_lex_one.



Definition compile_whitespace2 : { f | f =  fun s => (eval_M_prop_stream' (Common.whitespace_char @> Common.whitespace_char) None Unknown id_k () (dummy_stream s))}.
  cbv -[ascii_eq_dec]. simpl.  eexists. auto. Defined.

Extraction compile_whitespace2.

Definition compile_lex_one : { f | f =  fun s => (eval_M_prop_stream' (Sexp.lex_one) None Unknown id_k () (dummy_stream s))}. simpl.  Defined.
*)

(* Definition p_full_json_opt n := eval_compose (` (p_lex_opt n)) (` (p_json_opt n)). *)
(* Definition p_full_json_star_opt n := eval_compose (`(p_lex_opt n)) (`(p_json_star_opt n)). *)

(* Fully evaluate the parser before extraction *)
Set Extraction File Comment "   Auto generated by coq.  Do not modify. ".
Definition compile_parse_3_2 := Eval cbv in fun s => (eval_m_prop_stream parse_3_2 id_k () (dummy_stream s)).

Print compile_parse_3_2.

Extraction "src/simple_parser.ml" compile_fix_ab.


Extraction "src/parse_3_2.ml" compile_parse_3_2.


Definition compile_parse_3_or_4 := Eval cbv in fun s => (eval_m_prop_stream parse_3_or_4 id_k () (dummy_stream s)).

Extraction "src/parse_3_or_4.ml" compile_parse_3_or_4.


Extraction "src/p_json.ml"
    p_json_opt (* p_lex_opt *)  p_full_json_opt
    (* (* p_full_json *) *)
    (* (* p_full_json_star *) p_full_json_star_opt *)
.
(* Separate Extraction  p_full_json_opt. *)

Extraction "src/example_parsers.ml"
           Sexp.p_sexp_opt
           JustAs.p_count_as_opt JustAs.p_count_as_state_opt
           PPM.p_ppm_opt.
