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

Require Import Machine Opt Evaluators.
Require Import Coq.Strings.String Ascii.
From stdpp Require Import base propset.

Unset Guard Checking.

(* This is a collection of example parsers.  We reimplement the same examples as
   the TAAP paper for comparison. *)

(* NOTE: These were written before we had a general-purpose <|> that didn't
   require First sets.  Several of the combinators should be rewritten once we
   do - search for first_set_decide.  *)

Module Common.

  (*******************************)
  (****** Basic combinators ******)

  Locate "^".
  Check parse_exact.

  Definition one_of `{EqDecision tok} `{EqDecision tag}
                    `{BInfo tok tag}
                    {rv st}
                    (l : list tag)
                  : Machine rv st tok tag tok :=
      let fix one_of' l :=
              match l with
              | [] => raise "Expected token from provided list."
              | [x] => ^ x (* subtle. Makes <|> optimization go through *)
              | x::xs => ^x <|> one_of' xs
              end
      in
      one_of' l
  .

  Definition one_of_ `{EqDecision tok} `{EqDecision tag}
                     `{BInfo tok tag}
                     {rv st}
                    (l : list tag)
                  : Machine rv st tok tag unit :=
    parse_dump l.

  Instance first_one_of {rv st tag}
          `{EqDecision tag}
          `{EqDecision tok}
          `{BInfo tok tag}
          (l : list tag) :
    First (rv:=rv) (st:=st) tok (one_of l) := {| first_set := is_set l |}.

  Instance first_one_of_ {st tag rv}
          `{EqDecision tag}
          `{EqDecision tok}
          `{BInfo tok tag}
          (l : list tag) :
    First (rv := rv) (st := st) tok (one_of_ l).
  Proof.
    refine {| first_set := is_set l; |}.
  Defined.

  (* Observation: When not everything has first sets, we need to implement this
     in terms of <|> or some other way that doesn't explicitly check
     first_set_decide to decide whether to recurse. *)

  Definition star {tok st A} {rv} `{EqDecision tok}
                  `{BInfo tok tok}
                  (p : Machine rv st tok tok A)
                  {_ : First tok p}
                : Machine rv st tok tok (list A) :=
    parse_fix (fun star' =>
            peek (first_set (m:=p))
                 (call p (fun a => cons a <$$> (Var star')))
                 (return_ []) (return_ [])).

  Instance first_star {tok st A} {rv} `{EqDecision tok}
                      (p : Machine rv st _  _ A)
                      {_ : First tok p}
                    : First tok (star p).
  Proof.
    refine {| first_set := first_set (m := p); |}.
  Defined.

  Definition star_ {tok st A} {rv} `{EqDecision tok} {_ : BInfo tok tok}
                   (p : Machine rv st tok tok A)
                   {_ : First tok p}
                 : Machine rv st tok tok unit :=
    parse_fix (fun star' =>
      peek (first_set (m:=p))
           (p @> (Var star')) (return_ ()) (return_ ())).

  Instance first_star_ {tok st A} {rv} `{EqDecision tok} `{BInfo tok tok}
                       (p : Machine rv st _  _ A)
                       {_ : First tok p}
                    : First tok (star_ p).
  Proof.
    refine {| first_set := first_set (m := p); |}.
  Defined.

  Definition star1 {tok tag st A} {rv} `{BInfo tok tag}
                   (p : Machine rv st tok tag A)
                   {_ : First tok p}
                 : Machine rv st tok tag (list A) :=
    p >>= fun a1 => cons a1 <$$>
      parse_fix (fun star' =>
        peek (first_set (m:=p))
             (call p (fun a => cons a <$$> (Var star')))
             (return_ []) (return_ [])).

  (*****************************)
  (****** Character stuff ******)


  Definition charset (s : string) {st rv}
                   : Machine rv st ascii ascii ascii :=
    one_of (list_ascii_of_string s).

  Definition charset_ (s : string) {st rv}
                   : Machine rv st ascii ascii unit :=
    one_of_ (list_ascii_of_string s).

  Definition lower {st rv} : Machine rv st ascii ascii ascii :=
    charset "abcdefghijklmnopqrstuvwxyz".

  Definition lower_ {st rv} : Machine rv st ascii ascii unit :=
    charset_ "abcdefghijklmnopqrstuvwxyz".

  Definition upper {st rv} : Machine rv st ascii ascii ascii :=
    charset "ABCDEFGHIJKLMNOPQRSTUVWXYZ".

  Definition upper_ {st rv} : Machine rv st ascii ascii unit :=
    charset_ "ABCDEFGHIJKLMNOPQRSTUVWXYZ".

  Definition alpha {st rv} : Machine rv st ascii ascii ascii :=
    charset "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".

  Definition alpha_ {st rv} : Machine rv st ascii ascii unit :=
    charset_ "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".

  Definition digit {st rv} : Machine rv st ascii ascii ascii :=
    charset "0123456789".

  Definition digit_ {st rv} : Machine rv st ascii ascii unit :=
    charset_ "0123456789".

  (* We could implement this in Coq, but it would be really inefficient due to
     Coq's horrible ascii type.  Instead we axiomatize it, as we do for many
     things where Coq has inefficient internal representations.

     The ocaml version will throw an exception in the case where the arg isn't a
     valid digit char, so guard its use. *)
  Axiom ascii_to_digit_value : ascii -> nat.

  Definition digit_list_to_nat : list ascii -> nat :=
    let fix loop (acc:nat) (l:list ascii) :=
        match l with
        | [] => acc
(*        | (d::ds) => loop ((ascii_to_digit_value d) + (10 * acc)) ds *)
        | (d::ds) => loop (ocaml_plus (ascii_to_digit_value d) (ocaml_times 10 acc)) ds
        end
    in loop 0.

  Definition integer {st rv} : Machine rv st Ascii.ascii Ascii.ascii nat :=
    digit_list_to_nat <$$> star1 digit.

  Definition alphanum {st rv} : Machine rv st ascii ascii ascii :=
    charset "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".

  Definition whitespace_char {st rv}
                           : Machine rv st ascii ascii _ :=
    one_of_ [" "; "009"; "010"; "011"; "012"; "013"]%char.

  Definition whitespace {st rv} : Machine rv st ascii ascii _ :=
    star_ (H := ascii_dynamic_fin_set_binfo) whitespace_char.

  Instance first_peek_compl `{BInfo tok tok}
                            {st rv out}
                            {p1 p2 p3 : Machine rv st tok tok out}
                            (tl : list tok)
    : First tok (Peek (is_compl tl) p1 p2 p3).
  Proof.
    refine {| first_set := is_compl tl |}.
  Defined.

  (* Drops tokens until it encounters the provided one, which is also dropped. *)
  Definition drop_until_tok `{EqDecision tok} {st rv} (t : tok)
                          : Machine rv st tok tok unit :=
    star_ (Peek (is_compl [t]) (Drop (return_ ())) (Error "") (Error "")).
End Common.

(********************************************************************)
(********************************************************************)

Module Sexp.
  Import Common.

  (* This is a parser for s expressions that duplicates the behavior of the TAAP
     benchmark.  In particular, it's implemented with separate lexing and
     parsing phases, and it reutrns the maximum depth of the s-expression.  *)

  (**** Lexing ****)
  Inductive sexp_tok : Set :=
  | Atom : sexp_tok
  | LParen : sexp_tok
  | RParen : sexp_tok.

  Instance eqdec_sexp_tok : EqDecision sexp_tok.
  Proof.
    solve_decision.
  Defined.
(*
  Definition lex_one {st : Type} {rv}
    : machine rv st ascii sexp_tok := fun _ =>
        (^"("%char @> Return LParen)
    <|> (^")"%char @> Return RParen)
    <|> ((alpha >>= (fun c => ((cons c) <$$> star alphanum))) @> return_ Atom)
 .
 *)
  Definition lex_one {st : Type} {rv}
    : Machine rv st ascii ascii sexp_tok := 
        (^"("%char @> Return LParen)
    <|> (^")"%char @> Return RParen)
    <|> (alpha @> (star_ alphanum) @> return_ Atom)
  .

  Definition lexer {st rv} : Machine rv st ascii ascii sexp_tok :=
    lex_one @< whitespace.

  Eval vm_compute in (eval_m (BI:=static_fin_set_binfo) 42 lexer () (list_ascii_of_string "()")).

  Eval vm_compute in (eval_m (BI:=static_fin_set_binfo) 42 lexer () (list_ascii_of_string ") ( ")).

  (**** Parsing ****)

  (* This is gross: I can't use star in the definition of parser below because I
     need a first instance for the recursive variable.  We need to have a hard
     look at that situation.
   *)
  Definition delimited_list {st tok A rv} `{EqDecision tok}
             (start : tok)
             (p : Machine rv st tok tok A)
             (finish : tok)
           : Machine rv st tok tok (list A) :=
    ^start @>
      parse_fix (fun star_until' =>
        peek (is_compl [finish])
             (p >>= (fun a => (cons a) <$$> Var star_until'))
             (Drop (return_ [])) (raise eof)).

  Definition sum (l : list nat) : nat := fold_left ocaml_plus l 0.

  Definition parser {st rv} : Machine rv st sexp_tok sexp_tok nat :=
    parse_fix (fun sexp =>
          (^Atom @> return_ 1)
      <|> (sum <$$> delimited_list LParen (Var sexp) RParen)
    ).
(*
  (* This helper function isn't finding a needed First sets or BInfo for some reason. *)
  Definition string_to_sexp_tok (s : string) :=
    let l := list_ascii_of_string s in
    let res := eval_M (BI:=static_fin_set_binfo) 42
                      (fun rv => parse_list (lexer rv))
                      () l
    in match res with
       | (inl err, _, _) => []
       | (inr ts, _, _) => ts
       end.

  Eval vm_compute in (eval_M (BI:=static_fin_set_binfo) 42
                             parser
                             ()
                             (string_to_sexp_tok "( (a) b (d) c)")).

*)
  (**** Composition and optimization ****)
  (* Definition p_sexp : Machine (unit*unit) ascii (nat*list sexp_tok) := *)
  (*   Machine.compose lexer parser. *)

  (* CJC: we should build a nicer compose operator so that this thing has a nice
     type like:

     Machine unit ascii nat
   *)

  Definition lexer_opt : Opt (st := unit) lexer.
  Proof.
    eexists; intro; intros.
    autounfold.
    vm_compute.
    reflexivity.
  Defined.

  Definition parser_opt : Opt (st := unit) parser.
  Proof.
    eexists; intro; intros; autounfold.
    vm_compute.
    reflexivity.
  Defined.

  Definition p_sexp_opt : {f  | f = fun st (input : stream (ocaml_stream ascii) ascii) =>
                                      compose_parser (st1 := unit) (st2 := unit) lexer parser (fst st) (snd st) (dummy_stream (input.(state)))}.
    eexists; autounfold. unfold compose_parser. autounfold. vm_compute. (*cbv  -[Init.Nat.add].*) reflexivity.
  Defined.


End Sexp.

(********************************************************************)
(********************************************************************)
Module JustAs.
  Import Common.

  (* Here we have two parsers that just count a sequence of 'a's, for
     benchmarking purposes.  No compose.  We define two variants: one that adds
     1 to the result of its recursive call, and one that builds an accumulator
     using the parser's state. *)

  (* count is similar to star but we count the number of elements rather than
     building a list. *)
  Definition count {tok st A} {rv} `{EqDecision tok}
             (p : Machine rv st tok tok A)
             {_ : First tok p}
    : Machine rv st tok tok nat :=
    parse_fix (fun count' =>
      peek (first_set (m:=p))
           (call p (fun a:A => S <$$> Var count'))
           (return_ 0)
           (return_ 0)).


  (* XXX I had to give this a specific state type because of the value restriction
     in the extract ocaml! We should look into that maybe. *)
  Definition count_as {rv} : Machine rv unit ascii ascii nat :=
    count (^"a"%char).

  Definition p_count_as' : UnOpt (binfo := static_fin_set_binfo) count_as.
  Proof.
    eexists.
    intro; intros.
    reflexivity.
  Defined.

  Definition p_count_as := `p_count_as'.

  Definition p_count_as_opt' : Opt count_as.
  Proof.
    compile.
  Defined.

  Definition p_count_as_opt := `p_count_as_opt'.


  (* Variant 2: using state.  Would be interesting to compate with a version
     that could do less state assumptions by making more requirements for p's
     state or just inline ^"a". *)
  Definition count_state {tok A rv} `{EqDecision tok}
             (p : Machine rv nat tok tok A)
             {_ : First tok p}
           : Machine rv nat tok tok nat :=
    parse_fix (fun count' =>
      peek (first_set (m:=p))
           (call p
                 (fun _ => Write (fun s => S s) (Var count')))
           (read (fun s => return_ s))
           (read (fun s => return_ s))).

  Definition count_as_state {rv} : Machine rv nat ascii ascii nat :=
    count_state (^"a"%char).

  Definition p_count_as_state' : UnOpt (binfo := static_fin_set_binfo) count_as_state.
  Proof.
    eexists; intro; intros; reflexivity.
  Defined.

  Definition p_count_as_state := `p_count_as_state'.

  Definition p_count_as_state_opt' : Opt count_as_state.
  Proof.
    compile.
  Defined.

  Definition p_count_as_state_opt := `p_count_as_state_opt'.

End JustAs.

(********************************************************************)
(********************************************************************)

Module PPM.
  Import Common.

  (* This is a parser for the PPM image format that duplicates the behavior of
     the TAAP parser.  PPM is documented nicely on wikipedia:

       https://en.wikipedia.org/wiki/Netpbm

     The TAAP parser returns a boolean indicating whether the file obeys the
     constraints of its header, having the correct number of entries all of
     which are below the maximum.
   *)

  (**** Lexing ****)
  Inductive ppm_tok : Set :=
  | P3 : ppm_tok
  | Val : nat -> ppm_tok.

  Instance eqdec_ppm_tok : EqDecision ppm_tok.
  Proof.
    solve_decision.
  Defined.

  Definition lex_tok {rv st}
    : Machine rv st ascii ascii ppm_tok :=
        (^"P"%char @> ^"3"%char @> Return P3)
    <|> (Val <$$> Common.integer)
  .

  Definition ppm_comment {rv st}
    : Machine rv st ascii ascii () :=
    ^"#"%char @> drop_until_tok "010"%char.

  Definition lexer {st rv} : Machine rv st ascii ascii ppm_tok :=
      lex_tok @< (star_ (whitespace <|> ppm_comment)).

  (**** Parsing ****)

  (* Following TAAP, we begin by parsing the header, then while parsing the
     body we keep track of the maximum number seen and the total number of
     entries seen.  Once finished, we return true unless the maximum number
     we've seen is above the header-specified maximum or the number of entries
     is wrong. *)
  Inductive ppm_tok_tag :=
  | P3_T
  | Val_T.

  Instance eqdec_ppm_tok_tag : EqDecision ppm_tok_tag.
  Proof.
    solve_decision.
  Defined.

  Definition tag_match (tok : ppm_tok) (tag : ppm_tok_tag) : bool :=
    match tok,tag with
    | P3,    P3_T  => true
    | Val _, Val_T => true
    | _    , _     => false
    end.

  (* TODO: This definition copied from Json and should be moved to a shared place *)
  Definition in_set_compl {a} f (x : SetCompl a) : bool :=
    match x with
    | is_set l => existsb f l
    | is_compl l => negb (existsb f l)
    end.

  Global Instance binfo_ppm_tok `{EqDecision ppm_tok_tag}
    : BInfo ppm_tok ppm_tok_tag | 30 :=
    {| take_branch :=
         fun t tag =>
           let test t' := in_set_compl (fun tg => tag_match t' tg) tag in
           match t with
           | P3 => test P3
           | Val _ => test (Val 0)
           end;
       intersect := intersect_compl;
       (* TODO: something is shadowing union causing this ugliness .  fix *)
       Machine.union := union_compl;
       compl := rev_compl;
       subset := subset_compl
    |}.

  (* Only to be called when we know we have a val *)
  Definition extract_ppm_nat (t : ppm_tok) : nat :=
    match t with
    | Val n => n
    | _     => 0
    end.

  Definition parse_val {st rv}
    : Machine rv st ppm_tok ppm_tok_tag nat :=
    peek_fail (is_set [Val_T]) (extract_ppm_nat <$$> return_drop_tok)
              (raise parse_exact_error_msg).

  (* TODO: Ugly that I have to define parse_P3 here.  It's needed because
        parse_exact P3 : machine var st ppm_tok (SetCompl ppm_tok) _
     and I need something where the tag is (SetCompl ppm_tok_tag) to play nice
     with parse_val in parse_header (I think). *)
  Definition parse_P3 {st rv} : Machine rv st ppm_tok ppm_tok_tag unit :=
    peek_fail (is_set [P3_T]) (Machine.drop (return_ ()))  (raise parse_exact_error_msg).

  Definition parse_header {st rv}
    : Machine rv st ppm_tok ppm_tok_tag (nat*nat*nat) :=
       parse_P3 @>
       parse_val >>= fun width =>
       parse_val >>= fun height =>
       parse_val >>= fun max_val =>
                       return_ (width,height,max_val).

  Definition parse_body {st rv}
    : Machine rv st ppm_tok ppm_tok_tag (nat*nat) :=
    parse_fix (fun rec_body =>
      peek (is_set [Val_T])
        (parse_val >>= fun v1 =>
           call (Var rec_body) (fun (rec_result:(nat*nat)) =>
              let (max_val,count) := rec_result in
              return_ (max v1 max_val, S count)))
        (return_ (0,0)) (return_ (0,0))).

  Definition parse_ppm {st rv}
    : Machine rv st ppm_tok ppm_tok_tag bool :=
    parse_header >>= fun hdr => 
    parse_body >>= fun bdy =>
    match hdr,bdy with
    | (width,height,max_allowed),(max_actual,count) =>
      return_ (   ocaml_eq count (ocaml_times 3 (ocaml_times width height))
               && ocaml_lte max_actual max_allowed)
    end.


  Check lexer.
  Definition lex_opt' : Opt (st := ()) lexer.
  Proof.
    eexists; intro; intros.
    autounfold.
    vm_compute.
    reflexivity.
  Qed.

  Definition ppm_lex_opt := `lex_opt'.

  Definition parse_opt' : Opt (st := ()) parse_ppm.
  Proof.
    eexists; intro; intros.
    autounfold.
    vm_compute.
    reflexivity.
  Qed.

  Definition ppm_parse_opt := `parse_opt'.

  Definition p_ppm_opt : {f  | f = fun st (input : stream (ocaml_stream ascii) ascii) =>
                                     compose_parser (st1 := unit) (st2 := unit) lexer parse_ppm
                                                    (fst st) (snd st) (dummy_stream (input.(state)))}.
    eexists; autounfold. unfold compose_parser. autounfold. vm_compute. (*cbv  -[Init.Nat.add].*) reflexivity.
  Defined.

End PPM.

(********************************************************************)
(********************************************************************)
