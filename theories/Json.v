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

From stdpp Require Import strings fin_sets gmap countable.
From ParTS Require Import Machine ExampleParsers Opt Evaluators.
Import Ascii Byte.

(* Example JSON parser here: *)

Inductive json_tok :=
| LCURL
| RCURL
| LSQR
| RSQR
| COMMA
| COL
| STRING : list ascii -> json_tok
| TRUE
| FALSE
| NULL
| NUMBER : list ascii -> json_tok
.

(* Because json_tok is not itself a finite type, it needs to be characterized by another type. This is one option where we merely allow branching upon the case but do not allow partial evaluation on the held `list ascii` at compile time.
These tags will completely partially evaluate away.
*)
Inductive json_tok_tag :=
| LCURLT
| RCURLT
| LSQRT
| RSQRT
| COMMAT
| COLT
| STRINGT
| TRUET
| FALSET
| NULLT
| NUMBERT
.
(* Obvious correspondence function  *)
Definition tag_match (t : json_tok) (tag : json_tok_tag) : bool :=
  match t, tag with
| LCURL, LCURLT => true
| RCURL, RCURLT => true
| LSQR, LSQRT => true
| RSQR, RSQRT => true
| COMMA, COMMAT => true
| COL, COLT => true
| STRING _ , STRINGT => true
| TRUE , TRUET => true
| FALSE, FALSET => true
| NULL, NULLT => true
| NUMBER _ , NUMBERT => true
| _ , _ => false
end.


Instance eqdec_json_tok : EqDecision json_tok.
Proof.
  solve_decision.
Defined.

Instance eqdec_json_tok_tag : EqDecision json_tok_tag.
Proof.
  solve_decision.
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

Instance eqdec_byte : EqDecision byte.
Proof.
  intro; intros.
  eapply rewrite_dec.
  apply to_N_inj.
  solve_decision.
Defined.

Instance countable_byte : Countable byte.
Proof.
  eapply inj_countable.
  intros.
  apply of_to_N.
  Unshelve.
  apply _.
  apply _.
Defined.

Lemma ascii_inj : forall x : ascii, (Some ∘ ascii_of_byte) (byte_of_ascii x) = Some x.
Proof.
  intros.
  simpl.
  f_equal.
  apply ascii_of_byte_of_ascii.
Qed.

Instance countable_ascii : Countable ascii.
Proof.
  eapply inj_countable.
  intros.
  apply ascii_inj.
  Unshelve.
  apply _.
  apply _.
Defined.


(* similar to mem_compl?  A little different I think though *)
Definition in_set_compl {a} f (x : SetCompl a) : bool :=
  match x with
    | is_set l => existsb f l
    | is_compl l => negb (existsb f l)
  end.

Global Instance binfo_json_tok `{EqDecision json_tok_tag} : BInfo json_tok json_tok_tag | 30 :=
  {|

    take_branch := fun t tag =>
                     (* let simple_test t := (mem_compl static_in_set t tag) in *)
                     let test t' := in_set_compl (fun tg => tag_match t' tg) tag in
                     match t with
                       | LCURL =>  test LCURL
                       | RCURL =>  test RCURL
                       | LSQR =>  test LSQR
                       | RSQR =>   test RSQR
                       | COMMA =>   test COMMA
                       | COL =>  test COL
                       | STRING _ =>  test (STRING [])
                       | TRUE =>  test TRUE
                       | FALSE =>   test FALSE
                       | NULL =>   test NULL
                       | NUMBER _ => test (NUMBER [])
                     end;
    intersect := intersect_compl;
    union := union_compl;
    compl := rev_compl;
    subset := subset_compl;

   |}.

Eval vm_compute in (eval_m (BI:=static_fin_set_binfo)
                           42 ($LCURL <|> $RCURL) ([], None) [LCURL]).


Eval vm_compute in (eval_m (BI:=static_fin_set_binfo)
                      42 (parse_list_until ( $LCURL <|> $RCURL <|> $COMMA)
                                             (is_set [])
                                             (return_ []))
                      ([], None)
                      [LCURL; LCURL; RCURL; COMMA]).

(*
Definition baz {rv} :=
  (parse_list_until_queue (rv:=rv) (st:=list ())
                          ( $LCURL <|> $RCURL <|> $COMMA)
                          (is_set [])
                          (pop_queue)
                          ()).

*)
Definition test_parse_list_queue :=
  (eval_m (BI := static_fin_set_binfo)
           42
           (parse_list_until_queue
              (st:=list ())
              ( $LCURL <|> $RCURL <|> $COMMA)
              (is_set [])
              ( pop_queue))
           []
           [LCURL; LCURL; RCURL; COMMA]).

(* Horray! *)
Eval vm_compute in test_parse_list_queue.



Inductive json_val : Type :=
| json_bool : bool -> json_val
| json_null : json_val
| json_string : (list ascii) -> json_val
(* This should be a float, of course *)
| json_num : (list ascii)  -> json_val
| json_list : list json_val -> json_val
| json_obj : list ((list ascii) * json_val) -> json_val
.

Definition parse_maybe_error_msg := "parse_maybe: Expected Json String".


(* A partial function for extracting string from json_toks. To be used internally with care *)
Definition extract_string (x : json_tok) : list ascii :=
   match x with
   | STRING s => s
   | NUMBER s => s
   |  _  => []
   end.

(* helper function to extract contents for Number and String *)
Definition p_json_content {st} {rv} (tag : json_tok_tag) : Machine rv st json_tok json_tok_tag (list ascii) :=
  peek_fail (is_set [tag]) (extract_string <$$> return_drop_tok)  (raise parse_exact_error_msg).

Definition p_json_num {st} {rv} : Machine rv st json_tok json_tok_tag json_val :=  json_num <$$> p_json_content NUMBERT.

Definition p_json_string {st} {rv} : Machine rv st json_tok json_tok_tag json_val :=  json_string <$$> p_json_content STRINGT.


(* p_case is a tagged version of  (fun _ => r) <$$>  ^ c  *)
Definition p_case {tag tok st rv out} (cr : tag * out) : Machine rv st tok tag out :=
  let (c,r) := cr in
  Peek (is_set [c]) (drop (return_ r)) (raise eof) (raise parse_exact_error_msg).


Global Instance first_case (st : Type) {rv tag out} `{BInfo tok tag}`{EqDecision tok} (cr : tag * out) :
  First tok (p_case (rv:=rv) (st:=st) (out:=out) cr).
Proof.
  refine
  {| first_set := is_set [fst cr] |}.
Defined.


Global Instance first_json_content (st : Type) {rv} (tag : json_tok_tag) :
  First json_tok (p_json_content (rv:=rv) (st:=st) tag).
Proof.
  refine
  {| first_set := is_set [tag] |}.
Defined.


Notation "# p" := (p_case p)(at level 10).

Check or_machine.

Eval cbn in #(TRUET, json_bool true).
(* Definition p_json_atom {st : Type}{rv}
  : Machine rv st json_tok json_tok_tag json_val :=
  #(TRUET, json_bool true) <|> #(FALSET, json_bool false) <|>  #(NULLT, json_null)  <|> p_json_num <|> p_json_string.
*)
Definition p_json_atom {st : Type}{rv}
  : Machine rv st json_tok json_tok_tag nat :=
  #(TRUET, 1) <|> #(FALSET, 1) <|>  #(NULLT, 1)  <|> ((fun _ => 1) <$$> p_json_num ) <|> ((fun _ => 1) <$$> p_json_string).


Locate "$ ".
Check parse_dump.
(*
Definition p_json_field {st} {rv} (p_json : Machine rv st json_tok json_tok_tag json_val)
  : Machine rv st json_tok json_tok_tag ((list ascii) * json_val) :=
  ((p_json_content STRINGT) @< parse_dump [COLT]) @* p_json.
 *)
Definition p_json_field {st} {rv} (p_json : Machine rv st json_tok json_tok_tag nat)
  : Machine rv st json_tok json_tok_tag nat := (fun x => 1 + x) <$$> 
  (((p_json_content STRINGT) @> parse_dump [COLT]) @> p_json).


Definition p_cons {st tok A} {rv} `{BInfo tok tag} (p : Machine rv st tok tag A) (ps : Machine rv st tok tag (list A))
  := (fun ap => fst ap :: snd ap) <$$> (p @* ps).

Notation "p @: q":=(p_cons p q)(at level 32).

Definition foobarbaz : forall {tok out} {rv} `{EqDecision tok} (t : tok),
    First (rv:=rv) (st:=()) tok (# (t, @nil out)) := _.


Instance first_pound {tok st A : Type}{rv} `{EqDecision tok}
         (t : tok) (a : A) : First (rv:=rv) (st:=()) tok (#(t, a)) :=_.


(* This will end at end of file! We need a notion of nullable... *)

Instance first_drop {tok tag st out out'} {rv}
         (p : Machine rv st tok tag out')
         (q : Machine rv st tok tag out)
         `{EqDecision tok}
         `{BInfo tok tag}
         {_ : First tok p}
  : First tok (p @> q) := _.

(*
  This is a bit messy... Is there some way to clean this up?
 *)
Print parse_list.
Print First.
Definition parse_list_sep {st tok tag A}{rv}
           `{EqDecision tag}
           `{EqDecision tok}
           `{BInfo tok tag}
           (p : Machine rv st tok tag A)
           (sep list_start list_end : tag)
           : Machine rv st tok tag (list A)
  :=
    (parse_dump [list_start]) @>
     ( ((fun _ => @nil A) <$$> parse_dump [list_end])
        <|>
        ((p @: parse_list ( (parse_dump [sep]) @> p))) @< (parse_dump [list_end] )).

Check parse_list_sep.
Definition p_json_list {st} {rv}
           (p_json : Machine rv st json_tok json_tok_tag nat)
  : Machine rv st json_tok json_tok_tag nat :=
  (foldl ocaml_plus 0) <$$> (parse_list_sep (rv:=rv) p_json COMMAT LSQRT RSQRT).


Definition p_json_dict {st} {rv}
           (p_json : Machine rv st json_tok json_tok_tag nat)
  : Machine rv st json_tok json_tok_tag nat :=
  (foldl ocaml_plus 0) <$$> (parse_list_sep (p_json_field p_json) COMMAT LCURLT RCURLT).



(* It probably can't find First for p_json_atom. I moved p_json to the back so that it doesn't have to *)

Definition p_json {st rv} : Machine rv st json_tok json_tok_tag nat :=
  parse_fix
      (fun parse_json =>
         p_json_atom <|> p_json_dict (Var parse_json) <|> p_json_list (Var parse_json))
.

Compute (eval_m 42 (p_json_atom) tt [ FALSE ]).
Compute (eval_m 42 (p_json) tt [ LSQR; RSQR ]).
Compute (eval_m 42 (p_json) tt [ LSQR;  FALSE ; COMMA ; FALSE; RSQR ]).
Compute (eval_m 42 (p_json) tt [ LSQR; RSQR ; RSQR ]). (* accepted? with tail? *)

Open Scope char_scope.

Definition p_lcurl {st} {rv} : Machine rv st ascii ascii json_tok :=
  #("{", LCURL).
Check p_lcurl.

Definition p_rcurl {st} {rv} : Machine rv st ascii ascii json_tok :=
  #("}", RCURL).

Definition p_lsqr {st} {rv} : Machine rv st ascii ascii json_tok :=
  #("[", LSQR).

Definition p_rsqr {st} {rv} : Machine rv st ascii ascii json_tok :=
  #("]", RSQR).

Definition p_comma {st} {rv} : Machine rv st ascii ascii json_tok :=
  #(",", COMMA).

Definition p_col {st} {rv} :  Machine rv st ascii ascii json_tok :=
  #(":", COL).

Definition parse_exact_list {st tok}{rv}
           {_ : EqDecision tok}
           (ts : list tok) : Machine rv st tok tok () :=
  let fix parse_aux (ts : list tok) : Machine rv st tok tok () :=
      match ts with
      | [] => raise "Cannot parse empty token list!"
      | [t] => $t
      | t::ts => $t @> (parse_aux ts)
      end
  in
  parse_aux ts.


(* If we had nullable here we could mandate that parse exact list take a non
   empty p! *)
Instance first_exact_list {st tok : Type} {rv}
         `{_ : EqDecision tok}
           (ts : list tok) : First (st:=st) tok (parse_exact_list (rv:=rv) ts).
Proof.
  refine {| first_set := is_set (match ts with | [] => [] | t::_ => [t] end) |}.
Defined.

Definition p_true {st} {rv} : Machine rv st ascii ascii json_tok :=
  (fun _ => TRUE) <$$> (parse_exact_list ["t"; "r"; "u"; "e"]).

Definition p_false {st} {rv} : Machine rv st ascii ascii json_tok :=
  (fun _ => FALSE) <$$> (parse_exact_list ["f"; "a"; "l"; "s"; "e"]).

Definition p_null {st} {rv} : Machine rv st ascii ascii json_tok :=
  (fun _ => NULL) <$$> (parse_exact_list ["n" ; "u" ;"l" ; "l"]).

Print parse_list_until.
Print peek_fail.
(* Definition p_char {st} {rv} : () -> Machine rv st ascii () := fun _ =>
  Drop (return_ ()). *)

(* We're copying the TAAP paper in handling escape characters by throwing away
   the "\" and just taking the next character, though this feels maybe wrong in
   some cases.

  Also the ASP paper implements this differently, constructing a big nested <|>
  with all characters execept "\" and """".  Is there a performance impact? *)
(*Definition p_string_char {st} {rv} : () -> Machine rv st ascii () :=
  fun _ => (* this is wrong *)
    peek_fail (is_set ["\"]) (p_char ()) (return_ ()).
*)
(*
Definition p_string {st} {rv}
           (u : unit) : Machine rv st ascii json_tok :=
  let p_string_aux :=
       parse_exact _ """"
    @> parse_list_until (p_string_char ()) (is_set [""""]) (raise eof) u
    @< parse_exact _ """"
  in
  (fun _ => STRING) <$$> p_string_aux
 *)

Definition p_string {st} {rv}
           : Machine rv st ascii ascii json_tok :=
  let p_string_aux : Machine rv st _ _ (list ascii) :=
       ^ """"
           @> parse_fix (out := list ascii) (fun p => (parse_dump [""""] @> return_ nil)
           <|>  (parse_dump ["\"] @> Drop (Var p) )
           <|>  (return_drop_tok @: (Var p)))
  in
  STRING <$$> p_string_aux.


(* We're not treating decimals points yet *)
Definition p_number {st} {rv} : Machine rv st ascii ascii json_tok :=
  NUMBER <$$> (Common.digit @: (parse_list Common.digit)).




Definition p_lex_1 {rv st} : Machine rv st ascii ascii json_tok :=
        p_lcurl
    <|> p_rcurl <|> p_lsqr <|> p_rsqr <|> p_comma <|> p_col
    <|> p_true <|> p_false <|> p_null <|> p_string <|> p_number.



Definition p_lex_2 {rv st} : Machine rv st ascii ascii json_tok :=
  p_lex_1 @< Common.whitespace.



(*
  p_lex_2 does not have a useful first set because the first set of p_whitespace_many is any token

  Instance first_p_lex_2 (u : unit) : First (p_lex_2 n) := _.
*)

Definition eval_m_test {st tok out} `{EqDecision tok} :=
  eval_m (st:=st) (tok:=tok) (out:=out) (BI:=static_fin_set_binfo (tok:=tok)).


Compute eval_m_test 5 Common.whitespace [] (list_ascii_of_string "   true" ).

Compute eval_m_test 42 p_lex_2 [] (list_ascii_of_string "    " ).
(*Compute eval_m_test 42 p_lex [] (list_ascii_of_string "  [true, false, true:]    " ).
(* TODO: Something funky about this one! *)
Compute eval_m_test 1000 p_lex [] (list_ascii_of_string """hello world""" ).
Compute eval_m_test 42 p_number [] (list_ascii_of_string "42" ).
(* Something funky about this one! *)
Compute eval_m_test 1000 p_lex [] (list_ascii_of_string  "{ ""name"":""John"", ""age"":30, ""car"":""red"" }").
Compute eval_m_test 42 p_lex [] (list_ascii_of_string "[true,false,true]   ").
*)


(* To use TAAP's data set, we need to parse json files that contain multiple
   top-level objects.

   I want to use parse_list for this, which means I need a First instance for
   p_json.

   Here is the instance.
 *)
Definition json_first_set : list json_tok_tag := [LCURLT; LSQRT; STRINGT; TRUET; FALSET; NULLT; NUMBERT].

Instance first_p_json {st: Type} {rv} :
  First (rv:=rv) (st := st) json_tok p_json.
Proof.
  refine {| first_set := is_set json_first_set |}.
Defined.

(* And here is the parser and composed lexer/parser for multiple top-level json
   values *)

Definition p_json_star {rv} : Machine rv unit json_tok json_tok_tag nat :=
  (foldl ocaml_plus 0) <$$> parse_list p_json.

Require Import Ascii.
Unset Guard Checking.

Definition p_json_opt : Opt (st := unit) (p_json).
Proof.
  compile.
Defined.
(*
Definition p_lex_opt : Opt (p_lex ()).
Proof.
  eexists.
  intro; intros.
  unfold p_lex.
  unfold parse_list.
  unfold parse_list_until.
  unfold parse_fix.
  unfold eval_M_prop_stream.
  unfold eval_m_prop_stream.
  unfold bind.
  vm_compute. (*cbv beta iota zeta. *)
  reflexivity.
Defined.
*)

Definition p_json_star_opt : Opt p_json_star.
Proof.
  compile.
Defined.

(* This composition is not treating whitespace quite correctly. p_lex_2 does not accept beginning whitespace  *)
Definition p_full_json_opt : {f  | f = fun st (input : stream (ocaml_stream ascii) ascii) =>
                                       compose_parser (st1 := unit) (st2 := unit) p_lex_2 p_json_star (fst st) (snd st) (dummy_stream (input.(state)))}.
    eexists;  vm_compute. reflexivity.
Defined.
