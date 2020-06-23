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
From ParTS Require Import Machine.

(*

  The class of generic streams, where the destructors are in CPS form,
  for convenience in the evaluator definitions.

 *)
Class stream  (str : Type) (a : Type) : Type :=
  {
    state : str;
    peek_st : forall b, str -> (option a -> b) -> b;
    drop_st : forall b, str-> (str -> b) -> b;
    lookahead_st : forall b, str -> (str -> b) -> b;
  }.

Arguments peek_st {str} {a}.
Arguments drop_st {str} {a}.
Arguments lookahead_st {str} {a}.
Arguments state {str} {a}.

Definition update_stream {str a} (x : stream str a) (state' : str) : stream str a :=
  {|
    state := state';
    peek_st := x.(peek_st);
    drop_st := x.(drop_st);
    lookahead_st := x.(lookahead_st);
  |}.


(*

  These axioms represent ocaml runtime functions, which we leave
  abstract for now, since partial evaluation should not try to unfold
  them.

*)
Axiom failwith : forall b, string -> b.
Arguments failwith {b}.
Axiom ocaml_stream : Type -> Type.
Axiom ocaml_peek :  ∀ a b : Type, ocaml_stream a → (option a → b) → b.
Axiom ocaml_drop : ∀ a b : Type, ocaml_stream a → (ocaml_stream a → b) → b.
Axiom ocaml_lookahead : ∀ a b : Type, ocaml_stream a → (ocaml_stream a → b) → b.
Axiom ocaml_stream_fromfile : string -> ocaml_stream Byte.byte.

Arguments ocaml_peek {a}.
Arguments ocaml_drop {a}.
Arguments ocaml_lookahead {a}.

Axiom let_ : forall (a b : Type), a -> (a -> b) -> b.
Arguments let_ {a} {b}.

Definition dummy_stream {tok }s : stream _  tok :=
  {|
    state := s;
    peek_st := ocaml_peek;
    drop_st := ocaml_drop;
    lookahead_st := ocaml_lookahead;
  |}.

Inductive Tok (A : Type) := Known : A -> Tok A | Unknown | EOF.

Arguments Known {_}.
Arguments Unknown {_}.
Arguments EOF {_}.

(* This is how we trick the partial evaluation to do something reasonable with
   Fix constructors:
   We expect a "non-failing" recursive call, since the failure case is handled by an
   exception, and the remainder is discarded: the recursive call is to be at the tail.
 *)
Axiom fix_ : forall {a : Type}, (a -> a) -> a.

(* CPSed Evaluation *without* propagation. This will be used to run
   un-optimized machines in OCaml. *)
(* We keep the lambdas on the inside of the pattern match purposefully,
   since we do not want the pattern match to call [failwith] before being passed in the
   current stream state (otherwise it fails immediately). *)
Fixpoint eval_m_stream {st str tag out b}
         `{BInfo tok tag}
         (m : Machine (fun st tag out => (out -> st -> str -> b) -> st -> str -> b) st tok tag out)
         (k : out -> st -> str -> b) :
  forall
         (m_st : st)
         (input : stream str tok), b :=
  match m with
  | Var e => fun m_st input => e k m_st input.(state)
  | Error msg => fun m_st input => failwith msg
  | Return out0 => fun m_st input => k out0 m_st input.(state)
  | Drop m0 =>  fun m_st input =>
                  (input.(drop_st))
                    _
                    (input.(state))
                    (fun state_str =>
                       let input' := update_stream input state_str  in
                       eval_m_stream m0 k m_st input')
  | Call out' r f =>
    fun m_st input =>
      eval_m_stream r
                    (fun o m_st' st' =>
                       let input' := update_stream input st' in
                       eval_m_stream (f o) k m_st' input')
                    m_st input
  | Peek b m_true m_false m_eof =>
    let prop_rec t :=
        if take_branch t b
        then eval_m_stream m_true k
        else eval_m_stream m_false k
    in
    let prop_eof := eval_m_stream m_eof k in
    fun m_st input =>
      (input.(peek_st))
        _
        (input.(state))
        (fun ot =>
           match ot with
           | Some t => prop_rec t m_st input
           | None   => prop_eof m_st input
           end)
  | Lookahead m_b m_true m_false m_eof =>
    fun m_st input =>
      (input.(lookahead_st)) _
        (input.(state))
        (fun old_str =>
           let old_input := update_stream input old_str in
           eval_m_stream
             m_b
             (fun ob m_st' _ =>
                match ob with
                | None => eval_m_stream m_eof k m_st' old_input
                | Some true => eval_m_stream m_true k m_st' old_input
                | Some false => eval_m_stream m_false k m_st' old_input
                end
        ) m_st input)
  | Return_Drop_Tok g => fun m_st input =>
      (input.(peek_st))
        _
        (input.(state))
        (fun ot =>
           match ot with
           | Some t => (input.(drop_st))
                    _
                    (input.(state))
                    (fun state_str =>
                        k (g t) m_st state_str
                      )

           | None   => let_ (tt) (fun u => failwith "Incorrect usage of return_tok")
           end)
  | Read f => fun m_st input => eval_m_stream (f m_st) k m_st input
  | Write f m0 =>
    fun m_st input =>
      eval_m_stream m0 k (f m_st) input
  | Fix m_f => fun m_st input =>
        fix_
          (fun (rec_v : (out -> st -> str -> b) -> st -> str -> b)
               k' (m_st : st) (stream_st : str) =>
               let input' := update_stream input stream_st in
               eval_m_stream
                 (m_f rec_v)
                 k' m_st input') k m_st input.(state)
  end.

(*
Definition eval_M_stream {st tok br out str b} `{BInfo tok br} :
  Machine st tok br out → (out → st → str → b) → st → stream str tok → b :=
  fun m k state input =>
  eval_m_stream (m _) k state input.

Hint Unfold eval_M_stream. *)

(*

   This is the cps-ed, stream generic version of eval_m_stream, with
   added propagation for partial evaluation goodness.

*)

Unset Guard Checking.

Fixpoint eval_m_prop_stream_gen {st str tag out b}
         `{BInfo tok tag}
         (m : Machine (fun st tag out => forall b', (out -> st -> str -> b') -> st -> str -> b')
                      st tok tag out)
         (known_br : option (SetCompl tag))
         (known_tok : Tok tok)
         (k : out -> st -> str -> b)
         (m_st : st)
         (input : stream str tok) :  b :=
  match m with
  | Var e => e _ k m_st input.(state)
  | Error msg => failwith msg
  | Return out0 => k out0 m_st input.(state)
  | Drop m0 =>  (input.(drop_st))
                    _
                    (input.(state))
                    (fun state_str =>
                       let input' := update_stream input state_str  in
                       eval_m_prop_stream_gen m0 None Unknown k m_st input')
  | Call out' r f =>
    let_ (eval_m_prop_stream_gen
            r
            known_br
            known_tok
            (fun o m_st' st' => (o , m_st' , st')) m_st input)
         (fun omstst => let '(o , m_st',  st') := omstst in
                        (* Frozen let bind the o? *)
                        let input' := update_stream input st' in
                        eval_m_prop_stream_gen (f o) None Unknown k m_st' input')
  | Peek b m_true m_false m_eof =>
    let prop_rec t :=
    match known_br with
    | None => if take_branch t b
             then  eval_m_prop_stream_gen m_true (Some  b) (Known t) k m_st input
             else  eval_m_prop_stream_gen m_false (Some (compl b)) (Known t) k m_st input
    | Some known => if subset known b then
                      eval_m_prop_stream_gen m_true (Some known) (Known t) k m_st input
                    else if subset b (compl known) then
                            eval_m_prop_stream_gen m_false (Some known) (Known t) k m_st input
                   else if take_branch t (intersect known b)
                        then
                          eval_m_prop_stream_gen m_true (Some (intersect known b)) (Known t) k m_st input
                        else
                          eval_m_prop_stream_gen m_false
                                             (Some (intersect known (compl b)))
                                             (Known t)
                                             k m_st input
    end in
    let prop_eof := eval_m_prop_stream_gen m_eof None EOF k m_st input in
    match known_tok with
    | Known a => prop_rec a
    | Unknown =>
      (input.(peek_st))
        _
        (input.(state))
        (fun ot =>
           match ot with
           | Some t => prop_rec t
           | None   => prop_eof
           end)
    | EOF => prop_eof
    end
  (* TODO: should we doing any propagation here? *)
  | Lookahead m_b m_true m_false m_eof =>
    (input.(lookahead_st))
      _
      (input.(state))
      (fun old_str =>
         let old_input := update_stream input old_str in
         eval_m_prop_stream_gen
           m_b
           None
           Unknown
           (fun ob m_st' _ =>
              match ob with
              | None => eval_m_prop_stream_gen m_eof None Unknown k m_st' old_input
              | Some true => eval_m_prop_stream_gen m_true None Unknown k m_st' old_input
              | Some false => eval_m_prop_stream_gen m_false None Unknown k m_st' old_input
              end
           ) m_st input)
  | Return_Drop_Tok g =>
    let drop_helper t :=  (input.(drop_st))
                    _
                    (input.(state))
                    (fun state_str =>
                        k (g t) m_st state_str
                      ) in
    match known_tok with
    | Known a => drop_helper a
    | Unknown => (* This case should never occur. Return_Tok should be guarded by a peek? *)
        (input.(peek_st))   _
        (input.(state))
        (fun ot =>
           match ot with
           | Some t =>  drop_helper t
           | None   => failwith "improper Return_Tok usage"
           end)
    | EOF => failwith "improper Return_Tok usage"
    end
  | Read f => eval_m_prop_stream_gen (f m_st) known_br known_tok k m_st input
  | Write f m0 => eval_m_prop_stream_gen m0 known_br known_tok k (f m_st) input
  | Fix m_f =>
    let fix rec_v
            _ k' (m_st : st) (stream_st : str) {struct m_st} :=
        let input' := update_stream input stream_st in
        eval_m_prop_stream_gen
          (m_f rec_v)
          None Unknown k' m_st input' in
    rec_v _ k m_st input.(state)
  end.

Definition eval_m_prop_stream  {st str tag out b}
         `{BInfo tok tag}
         (m : Machine _ st tok tag out)
         ( k : out -> st -> str ->  b)
         (m_st : st)
         (input : stream str tok) : b :=
  eval_m_prop_stream_gen m None Unknown k m_st input.

(* eval_stream takes a machine [m] and creates the stream that
   repeatedly calls [m] to produce [out]s.  This can then be used as
   the input to another machine.

   The main subtlety is that the equivalent of "drop" for the output
   stream is a call to [m] which discards its result, and the
   equivalent of "peek" is a call to [m] which then *reverts* back to
   the original position in the input stream.

   This is in general impossible without [lookahead], which we do not
   assume is always implemented. Our solution is to use a buffer which
   is filled at each call to [drop], which then can be examined on a
   call to [peek]. This requires the buffer to be "primed", i.e. an
   initial call to the machine [m] at the beginning of an
   [eval_stream] invocation.

 *)
Definition eval_stream {st st' tag out } `{BInfo tok tag} (m : Machine _ st tok tag out) (x : out) (m_st : st) (xs : stream st' tok) : stream ((option out) * st' * st) out :=
  {|
    state := (Some x, xs.(state), m_st);

    drop_st :=
      fun _ st k =>
        let '(_, str, m_st') := st in
        xs.(peek_st)
             _
             str
             (fun ot => match ot with
                        | None => k (None, str, m_st')
                        | Some _ =>
                          let xs' := update_stream xs str in
                          (eval_m_prop_stream m (fun o m_st' st'' =>
                                                   k (Some o, st'', m_st'))
                                              m_st xs')
                        end);

    peek_st := fun _ st k => let '(o, _, _) := st in
                             k o;
    lookahead_st :=
      fun _ st k =>
        let '(buf, str, m_st') := st in
        xs.(lookahead_st)
             _
             str
             (fun old_str => k (buf, old_str, m_st'))
        ;
   |}.


Definition compose_parser {str st1 st2 tok0 tok1 tag1 tag2 out }
           `{BInfo tok0 tag1}
           `{BInfo tok1 tag2}
           (m1 : Machine _ st1 tok0 tag1 tok1)
           (m2 : Machine _ st2 tok1 tag2 out )
           (m_st1 : st1)
           (m_st2 : st2)
           (input : stream str tok0) : out
  := (eval_m_prop_stream
        m1
        (fun o m_st1' st' =>
           (eval_m_prop_stream m2)
             (fun o _ _ => o)
             m_st2
             (let input' := update_stream input st' in
              eval_stream m1 o m_st1' input'))
        m_st1 input
      ).


Global Instance list_stream {a} : list a -> stream (list a) a :=
  fun l =>
    {|
      state := l;
      peek_st := fun b l k => k (List.head l);
      drop_st := fun b l k => k (List.tail l);
      lookahead_st := fun b l k =>
                        (* Just to emphasize that this is a "saved" value *)
                        let old_l := l in
                        k old_l;
    |}.
