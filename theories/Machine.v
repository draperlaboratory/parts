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

From stdpp Require Import base list strings option lexico sorting.
(* From stdpp Require Import fin_sets gmap. *)
Open Scope string_scope.
Require Import Ascii.
Require Import Coq.extraction.ExtrOcamlNativeString.


(* Should we be using a generic set type here, to keep things flexible? *)
Inductive SetCompl (A : Type) : Type :=
| is_set : list A -> SetCompl A
| is_compl : list A -> SetCompl A.

Arguments is_set {A}.
Arguments is_compl {A}.


Definition RecVar := Type -> Type -> Type -> Type.

(* The type of parsing Machines: The input stream is left implicit, it
   takes a stream of `tok` which can be branched on using `br`, and
   returns an error, or an `out` and the remaining input.

   Uses the reader state `st`.  *)
Inductive Machine (rv : RecVar) (st tok tag out : Type) : Type :=

| Var : rv st tag out -> Machine rv st tok tag out

(* Immediately halt, raising an error *)
| Error : string -> Machine rv st tok tag out

(* Immediately halt, returning a concrete output *)
| Return :  out -> Machine rv st tok tag out

(* Drop a token of input from the token stream *)
| Drop : Machine rv st tok tag out -> Machine rv st tok tag out

(* In TAAP, this is RecVar out' -> (out' -> Machine out) -> Machine out *)
(* In the code, this is simply (Machine out -> Machine out) -> Machine out *)
| Call : forall out', Machine rv st tok tag out' -> (out' -> Machine rv st tok tag out)
                      -> Machine rv st tok tag out

| Fix :  (rv st tag out -> Machine rv st tok tag out) -> Machine rv st tok tag out
(* In TAAP, this is Peek : CharSet -> (Yes|No|EOF -> Machine out) -> Machine out *)
(* The first argument is on success, the second is on failure, the third is on eof *)
| Peek : (SetCompl tag)
      -> Machine rv st tok tag out
      -> Machine rv st tok tag out
      -> Machine rv st tok tag out
      -> Machine rv st tok tag out

(* Lookahead does not exist in TAAP. It's semantics is to run the
  lookahead machine, (returning None if EOF is encountered) and use the
  resulting boolean to dynamically decide which branch to take.
*)
| Lookahead : Machine rv st tok tag (option bool)
              -> Machine rv st tok tag out
              -> Machine rv st tok tag out
              -> Machine rv st tok tag out
              -> Machine rv st tok tag out

(* This constructor gives us direct access to the dynamic token. To be used with care. Do not attempt to match on the token, consider it only an opaque value. This will also Drop the token. This choice was made in order to make optimizations easier. If stream is empty, this will throw an error. *)
| Return_Drop_Tok : (tok -> out) ->  Machine rv st tok tag out

(* We probably should be dependent on st here, and have a type of queries,
     that depends on the current state. *)
| Read :  (st -> Machine rv st tok tag out) -> Machine rv st tok tag out

(* TAAP doesn't have this, of course *)
| Write : (st -> st) -> Machine rv st tok tag out -> Machine rv st tok tag out

(* It might make sense to allow for this explicitely instead of defining it later. *)
(* | Compose : forall tok' , Machine st tag (list tok') -> Machine st (set tok') out -> Machine st tag (out*(list tok')) *)
.


Arguments Var {rv} {st} {tok} {tag} {out}.
Arguments Error {rv} {st} {tok} {tag} {out}.
Arguments Return {rv} {st} {tok} {tag} {out}.
Arguments Drop {rv} {st} {tok} {tag} {out}.
Arguments Call {rv} {st} {tok} {tag} {out}.
Arguments Peek {rv} {st} {tok} {tag} {out}.
Arguments Lookahead {rv} {st} {tok} {tag} {out}.
Arguments Return_Drop_Tok {rv} {st} {tok} {tag} {out}.
(* Arguments Peek_Drop_Tok {rv} {st} {tok} {tag} {out}. *)
Arguments Read {rv} {st} {tok} {tag} {out}.
Arguments Write {rv} {st} {tok} {tag} {out}.
Arguments Fix {rv} {st} {tok} {tag} {out}.

Definition return_ {st tok tag out : Type} {rv} : out -> Machine rv st tok tag out :=
  fun o => Return o.

Definition raise {st tok tag out : Type} {rv} : string -> Machine rv st tok tag out :=
  fun s => Error s.

Definition drop {st tok tag out : Type} {rv} : Machine rv st tok tag out -> Machine rv st tok tag out :=
  fun m => Drop m.

Definition return_drop_tok {st tok tag : Type} {rv} : Machine rv st tok tag tok :=
  Return_Drop_Tok id.

Definition call {st tok tag out out' : Type}{rv} (m : Machine rv st tok tag out') (f : out' -> Machine rv st tok tag out) :=
  Call _ m f.

Definition peek {st tok tag out : Type} {rv} : SetCompl tag -> Machine rv st tok tag out -> Machine rv st tok tag out
                                     -> Machine rv st tok tag out
                                     -> Machine rv st tok tag out :=
  fun b m n p => Peek b m n p.

Definition lookahead {st tok tag out : Type} {rv} : Machine rv st tok tag (option bool) -> Machine rv st tok tag out -> Machine rv st tok tag out
                                     -> Machine rv st tok tag out
                                     -> Machine rv st tok tag out :=
  fun b m n p => Lookahead b m n p.

Definition eof : string := "Unexpected EOF!"%string.

Definition peek_fail {st tok tag out : Type} {rv} : (SetCompl tag) -> Machine rv st tok tag out -> Machine rv st tok tag out
                                                    -> Machine rv st tok tag out :=
  fun b m n => peek b m n (raise eof).

Definition lookahead_fail {st tok tag out : Type} {rv} : Machine rv st tok tag (option bool) -> Machine rv st tok tag out -> Machine rv st tok tag out
                                                         -> Machine rv st tok tag out :=
  fun b m n => lookahead b m n (raise eof).

Definition read {st tok tag out} {rv} (m : st -> Machine rv st tok tag out) : Machine rv st tok tag out :=
  Read (fun st => m st).

Definition write {st tok tag out} {rv} (f : st -> st) : Machine rv st tok tag out -> Machine rv st tok tag out :=
  fun m => Write f m.


(* We use this when we get lazy with proofs *)
Axiom magic : forall A, A.

Definition ErrorT (T : Type) := (string + T)%type.

Definition write_err {T : Type} (s : string) : ErrorT T := inl T s.
Definition is_err {T} (a : ErrorT T) : bool := if a then true else false.


Definition lift_err {A B} : (A -> B) -> (ErrorT A -> ErrorT B) :=
  fun f ea =>
    match ea with
    | inl s => inl s
    | inr a => inr (f a)
    end.

Definition bind_err {A B} : ErrorT A -> (A -> ErrorT B) -> ErrorT B :=
  fun e f =>
    match e with
    | inl s => inl s
    | inr a => f a
    end.

(* An instance of [BInfo tag tok] means [tag] is a type of static
   branching information for tokens [tok].

   - [take_branch t b] is true if based on the token, the branch
     should be taken, false otherwise. This is the only "dynamic"
     semantics of [b], namely the only part which actually (usually)
     needs the concrete input token in order to return a result. The
     hope is that this often gets turned into a trivial constant
     function by propagation.

   - [propagate_true b] is the information to propagate if [b] was
     taken for the current token. It is typically [b] itself.

   - [propagate_false b] is the information to propagate if [b] was
   *not* taken for the current token. it is typically the negation or
   complement of the predicate b.

   - [impl b1 b2] creates a new branching condition which is the
     condition [b2], *conditioned* on the fact that [b1] was taken.

Phil : I think most of these functions except take branch should be taken out of here and we use the stdpp typeclasses for sets and lattices as superclasses of BInfo.

 *)

Class BInfo tok tag : Type :=
  {
    take_branch : tok -> (SetCompl tag) -> bool;
    intersect : SetCompl tag -> SetCompl tag -> SetCompl tag;
    union : SetCompl tag -> SetCompl tag -> SetCompl tag;
    compl : SetCompl tag -> SetCompl tag;
    subset : SetCompl tag -> SetCompl tag -> bool
  }.

Definition EvalRes (st tok out : Type) : Type := ErrorT out * list tok * st.


(* It's actually unclear we need the input stream at all!  we could
   just wrap it up in the state, and have one of the writers be
   "consume" of a token, which puts the required information into the
   state!
 *)

Definition out_of_gas : string := "Out of gas!".

Fixpoint eval_m
         {tag st tok out}
         `{BI : BInfo tok tag}
         (n : nat)
         (m : Machine (fun st tag out => st -> list tok -> EvalRes st tok out) st tok tag out)
         (state : st)
         (input : list tok)
         {struct n}
  : EvalRes st tok out :=
  match n with
  | 0 => (write_err out_of_gas, input, state)
  | S n =>
    match m with
    | Var e => e state input
    | Error msg => (write_err msg, input, state)
    | Return out => (inr out, input, state)
    (* This is an issue if errors are raised by exception! *)
    | Drop m => eval_m n m state (tail input)
    | Call _ r f =>
      let '(o, input', state') := eval_m n r state input in
      match o with
      | inl s => (write_err s, input', state')
      | inr o' =>
        eval_m n (f o') state' input'
      end
    | Peek b m_true m_false m_eof =>
      match hd_error input with
      | None => eval_m n m_eof state input
      (* No propagation here! This is only notional semantics. *)
      | Some t => if take_branch t b then
                    eval_m n m_true state input
                  else
                    eval_m n m_false state input
      end
    | Lookahead b m_true m_false m_eof =>
      match hd_error input with
      | None => eval_m n m_eof state input
      | Some _ =>
        (* Throw away the updated stream but propagate state, which may be useful *)
        let '(o, _, state') := (eval_m n b state input) in
        match o with
        | inl err => (write_err err, input, state')
        | inr t => if t then
                     eval_m n m_true state' input
                   else
                     eval_m n m_false state' input
        end
      end
    | Return_Drop_Tok f =>
            match hd_error input with
            | None =>  (write_err "Unexpected EOF for Return_Drop_Tok", input, state)
            | Some t => (inr (f t), tail input, state)
            end
    | Read m_st =>
      eval_m n (m_st state) state input
    | Write f m =>
      let state' := f state in
      eval_m n m state' input
    | Fix f => eval_m n (f (eval_m n (Fix f))) state input
    end
  end.


(* This is useless, since all the set operations are type classe-d *)
(* Coercion is_set : gset >-> SetCompl. *)

Definition is_empty {A} : list A -> bool :=
  fun l => match l with [] => true | _ => false end.

Axiom ocaml_eq : forall a, a -> a -> bool.
Arguments ocaml_eq {a}.
Axiom ocaml_or : forall {a}, a -> a -> bool.
Axiom ocaml_and : forall {a}, a -> a -> bool.

Axiom ocaml_lte : forall a, a -> a -> bool.
Arguments ocaml_lte {a}.

Axiom ocaml_gte : forall a, a -> a -> bool.
Arguments ocaml_gte {a}.
Axiom ocaml_plus : nat -> nat -> nat.

(* The next section is building a smart interval condition checker for
 consecutive ascii characters, which appears to give a performance boost compared
to tagute force equality checker *)

(* assumes xs is sorted *)
Fixpoint intervals_helper (a : nat) (b : nat) (xs : list nat) : list (nat * nat) :=
  match xs with
  | x :: xs' => if decide (x <= 1 + b) then intervals_helper a x xs' else (a,b) :: intervals_helper x x xs'
  | [] => [(a,b)]
  end.

(* This function assumes xs is sorted. It collects up consecutive elements into
   tuples of intervals *)
Definition intervals (xs : list nat) : list (nat * nat) :=
  match xs with
  | x :: xs' => intervals_helper x x xs'
  | [] => []
  end.

(* Smartly use intervals to build dynamic branching condition for ascii  *)
Fixpoint build_brancher (xs : list (ascii * ascii)) : ascii -> bool :=
  fun t =>
    match xs with
  | [(a,b)] => if decide (a = b) then (ocaml_eq t a) else ocaml_and (ocaml_gte t a) (ocaml_lte t b)
  | (a,b) :: xs' =>
    let bs :=  (build_brancher  xs' t) in
    if decide (a = b) then ocaml_or (ocaml_eq t a) bs else ocaml_or ( ocaml_and (ocaml_gte t a) (ocaml_lte t b)) bs
  | []  => false
  end.

Definition smart_ascii_dynamic_in_set (t : ascii) (xs : list ascii) : bool :=
  let natxs := map nat_of_ascii xs in
  let sorted := merge_sort lexico natxs in
  let intervaled := intervals sorted in
  let asciiinterval := map (fun ab : nat * nat=> let (a,b) := ab in ( ascii_of_nat a ,ascii_of_nat  b )) intervaled in
   build_brancher asciiinterval t.

Eval cbv in fun t => smart_ascii_dynamic_in_set t ["b" ;  "a" ; "c" ; "e" ; "b" ; "d"]%char.

(* We use the opaque ocaml_eq but compile time unroll the list checking *)
Fixpoint dynamic_in_set {A} (t : A) (xs: list A) : bool :=
  match xs with
  | [] => false
  | [x] => ocaml_eq t x
  | x :: xs' => ocaml_or (ocaml_eq t x) (dynamic_in_set t xs')
  end.

(* Duplicated code, to have the dynamic check when debugging.
   TODO: handle this with type classes.
 *)
Fixpoint static_in_set `{EqDecision A} (t : A) (xs : list A) : bool :=
  match xs with
  | [] => false
  | [x] => bool_decide (t = x)
  | x :: xs' => (bool_decide (t = x)) || (static_in_set t xs')
  end.

(* Membership function for SetCompl type *)
Definition mem_compl {A} (in_set : A -> list A -> bool)
  : A -> SetCompl A -> bool :=
  fun a s => match s with
             | is_set s =>
               if is_empty s then false else
                  (in_set a s)
             | is_compl s =>
               if is_empty s then true else
               negb (in_set a s)
             end.

Definition rev_compl {A} : SetCompl A -> SetCompl A :=
  fun s => match s with
           | is_set s => is_compl s
           | is_compl s => is_set s
           end.

(* use \setminus to write A ∖ B *)
(* The algebra for this is awful btw! *)
(* Phil: Currently unused? *)
Definition impl_compl `{EqDecision A} : SetCompl A -> SetCompl A -> SetCompl A :=
  fun s1 s2 => match s1, s2 with
               | is_set s1, is_set s2 => is_compl (list_difference s1 s2)
               | is_compl s1, is_set s2 => is_set (list_union s2 s1) (* phil: should this be list_difference? *)
               | is_set s1, is_compl s2 => is_compl (list_intersection s1 s2)
               | is_compl s1, is_compl s2 => is_set (list_difference s2 s1) (* phil: the variance seems fishy here  *)
               end.


Definition intersect_compl `{EqDecision A} : SetCompl A -> SetCompl A -> SetCompl A :=
    fun s1 s2 => match s1, s2 with
               | is_set s1, is_set s2 => is_set (list_intersection s1 s2)
               | is_compl s1, is_set s2 => is_set (list_difference s2 s1)
               | is_set s1, is_compl s2 => is_set (list_difference s1 s2)
               | is_compl s1, is_compl s2 => is_compl (list_union s1 s2)
               end.

Definition subset_list `{EqDecision A} (x y : list A) := is_empty (list_difference x y).

(*  This is does not exactly decide subset for SetCompl. If returns true, yes, it is a subset. If it returns false it may or may not be a subset. This is due to the difficulty encountered in the second case, which is resolvable with an additional finiteness condition  *)
Definition subset_compl `{EqDecision A} : SetCompl A -> SetCompl A -> bool :=
    fun s1 s2 => match s1, s2 with
               | is_set s1, is_set s2 => subset_list s1 s2
               | is_compl s1, is_set s2 => false (* is_set (list_difference s2 s1) *) (* This is semidecidable? *)
               | is_set s1, is_compl s2 => is_empty (list_intersection s1 s2)
               | is_compl s1, is_compl s2 => is_empty (list_difference s2 s1)
               end.



Definition union_compl `{EqDecision A} : SetCompl A -> SetCompl A -> SetCompl A :=
    fun s1 s2 => match s1, s2 with
               | is_set s1, is_set s2 => is_set (list_union s1 s2)
               | is_compl s1, is_set s2 => is_compl (list_difference s1 s2)
               | is_set s1, is_compl s2 => is_compl (list_difference s2 s1)
               | is_compl s1, is_compl s2 => is_compl (list_intersection s1 s2)
               end.


(* We set the level high on resolution search, so that it has to be passed explicitely if we want
   it to be used. *)
Global Instance static_fin_set_binfo {tok} `{EqDecision tok} : BInfo tok tok | 100 :=
  {|
    take_branch := fun t b => mem_compl static_in_set t b;
    intersect := intersect_compl;
    union := union_compl;
    compl := rev_compl;
    subset := subset_compl
  |}.

Global Instance dynamic_fin_set_binfo {tok} `{EqDecision tok} : BInfo tok tok | 50 :=
  {|
    take_branch := fun t b => mem_compl dynamic_in_set t b;
    intersect := intersect_compl;
    union := union_compl;
    compl := rev_compl;
    subset := subset_compl
  |}.

(* We have given the specialized fast ascii interval instance priority. *)
Global Instance ascii_dynamic_fin_set_binfo `{EqDecision ascii} : BInfo ascii ascii | 0 :=
  {|
    take_branch := fun t b => mem_compl smart_ascii_dynamic_in_set t b;
    intersect := intersect_compl;
    union := union_compl;
    compl := rev_compl;
    subset := subset_compl
  |}.

Definition parse_exact_error_msg :=  "parse_exact: Unexpected Token!".

Global Instance set_compl_singl (A : Type) `{EqDecision A} : Singleton A (SetCompl A) :=
  fun a => is_set ([a]).

(*
There are now 2 possibilities for what should be the default parse_exact behavior.
 *)


Definition parse_exact (st : Type) {tok}{rv} `{EqDecision tok} (t : tok) :
  Machine rv st tok tok tok :=
  peek_fail ({[t]}) (drop (return_ t)) (raise parse_exact_error_msg).

Definition parse_exact' (st : Type) {tok tag} {rv} `{BInfo tok tag} `{EqDecision tag} (t : tag) :
  Machine rv st tok tag tok :=
  peek_fail ({[t]}) return_drop_tok (raise parse_exact_error_msg).



Notation "^ t" := (parse_exact' _ t)(at level 10).

Definition parse_dump {st tok tag : Type} {rv} (b : list tag ) `{BInfo tok tag}: Machine rv st tok tag unit :=
    peek_fail (is_set b) (drop (Return ())) (raise parse_exact_error_msg).


Eval cbv in parse_dump.

Fixpoint bind {st tok tag out out' : Type} {rv}
         (m : Machine rv st tok tag out')
         (f : out' -> Machine rv st tok tag out) : Machine rv st tok tag out := call m f.

Fixpoint bind_inline {st tok tag out out' : Type} {rv}
         (m : Machine rv st tok tag out')
         (f : out' -> Machine rv st tok tag out) : Machine rv st tok tag out :=
  match m with
  | Var v => Call _ m f
  | Return o => f o
  | Error err => raise err
  | Drop m => Drop (bind_inline m f)
  (* We forsake the full optimization here, by necessity *)
  | Call _ m g => Call _ (bind_inline m g) f
  | Peek tag m_yes m_no m_empty =>
    Peek tag (bind_inline m_yes f) (bind_inline m_no f) (bind_inline m_empty f)
  | Lookahead m_dec m_yes m_no m_empty =>
    Lookahead m_dec (bind_inline m_yes f) (bind_inline m_no f) (bind_inline m_empty f)
  | Return_Drop_Tok g => Call _ (Return_Drop_Tok g) f
  | Read m_read => Read (fun state => bind_inline (m_read state) f)
  | Write update m' => Write update (bind_inline m' f)
  | Fix m_f => Call _ m f
  end.


Notation "m >>= f" := (bind m f)(at level 30).

Definition p_map {st tok tag out out' : Type} {rv} :
  (out -> out') -> Machine rv st tok tag out -> Machine rv st tok tag out'
  :=
  fun f m => m >>= (fun o => return_ (f o)).

Notation "f <$$> p" := (p_map f p) (at level 61, left associativity).

Definition prod {st tok tag out out' : Type} {rv} :
  Machine rv st tok tag out -> Machine rv st tok tag out' -> Machine rv st tok tag (out * out') :=
  fun m1 m2 =>
    m1 >>= (fun o => (fun o' => (o, o')) <$$> m2).

Notation "m1 @* m2" := (prod m1 m2)(at level 20).

Notation "m1 @> m2" := (m1 >>= (fun _ => m2))(at level 20).

Notation "m1 @< m2" := ((fun p => fst p) <$$> (m1 @* m2))(at level 20).

Definition parse_3_2 {rv} : Machine rv () _ _ _ := (^ 3 @* ^ 2).

Definition eval_test `(BI : BInfo nat nat) := eval_m (BI := BI) 6 parse_3_2 ().


Eval vm_compute in mem_compl static_in_set 3 {[3]}.
Eval vm_compute in mem_compl dynamic_in_set 3 {[3]}.

Eval cbn in (fun x => eval_m 42 (^ 3) () [x]).

Eval vm_compute in (fun x => eval_m (BI := static_fin_set_binfo) 42 (^ 3) () [3]).

Eval vm_compute in eval_test static_fin_set_binfo [3; 2; 4].
Eval vm_compute in eval_test static_fin_set_binfo [3; 3; 4].
Eval vm_compute in eval_test dynamic_fin_set_binfo [3].

Definition parse_fix {st tok tag out} {rv} :
  (rv st tag out -> Machine rv st tok tag out) -> Machine rv st tok tag out :=
  fun rec_f => Fix rec_f.

(* We originally had this definition: *)
(* fun rec_f => *)
(*    match n with *)
(*    | 0 => call (return_ tt) (fun _ => raise out_of_gas) *)
(*    | S n' => rec_f (call (return_ tt) (fun _ => (parse_fix n' rec_f))) *)
(*    end. *)



Class First (tok : Type) {st out}
   `{BInfo tok tag} {rv} (m : Machine rv st tok tag out) : Type :=
  {
    first_set : (SetCompl tag);
    (* (* This is the notional property we want *) *)
    (* first_set_prop : forall (s : st) (t : tok) (ts : list tok), *)
    (*     t ∉ first_set -> is_err (fst (eval_M m s (t :: ts))) *)
  }.

Global Instance first_exact (st : Type) {rv} `{BInfo tok tok} `{EqDecision tok} (t : tok) :
  First tok (parse_exact (rv:=rv) st t).
Proof.
  refine
  {| first_set := is_set [t] |}.
Defined.


Global Instance first_exact' (st : Type) {rv} `{BInfo tok tag} `{EqDecision tag} (t : tag) :
  First tok (parse_exact' (rv:=rv) st t).
Proof.
  refine
  {| first_set := is_set [t] |}.
Defined.

Global Instance first_dump (st : Type) {rv} `{BInfo tok tag} `{EqDecision tok} (ts : list tag) :
  First tok (parse_dump (rv:=rv) (st:=st) ts).
Proof.
  refine
  {| first_set := is_set ts |}.
Defined.


Global Instance first_prod {rv} `{p : Machine rv st tok tag out} `{EqDecision tok} `{BInfo tok tag}
         (_ : First tok p) : forall (q : Machine rv st tok tag out'), First tok (p @* q).
Proof.
  refine
  (fun out' q => {| first_set := first_set (m := p) |}).
Defined.


Global Instance first_bind {tok tag st out out'} {rv} `{EqDecision tok} `{BInfo tok tag}
         (p : Machine rv st tok tag out') (q : out' -> Machine rv st tok tag out)
         {F : First tok p}
  : First tok (p >>= q).
Proof.
  refine {| first_set := first_set (m := p) |}.
Defined.


Definition or_machine {rv}
           `{EqDecision tok}
           `{BInfo tok tag}
           `(m1 : Machine rv st tok tag out) {_ : First tok m1}
           `(m2 : Machine rv st tok tag out)
  : Machine rv st tok tag out :=
  match m1, m2 with
  | Peek tag1 (Return_Drop_Tok coerce ) (Error msg1) (Error msg2),
    Peek tag2 (Return_Drop_Tok _) (Error _) (Error _) => Peek (union tag1 tag2) (Return_Drop_Tok coerce) (Error msg1) (Error msg2)
  | _ , _ =>  peek_fail (first_set (m:=m1)) m1 m2
  end.

(*

match m1, m2 with
| Peek (Return_Drop_Tok (secret return?) ) (Error) (Error), Peek (Peek_Drop_Tok _) (Error) (Error) => Peek (Peek_Drop_Tok) Error Error
| _, _ => peek_fail () m1 m2
end

*)

Notation "m1 <|> m2" := (or_machine m1 m2)(at level 32, right associativity).

Global Instance first_or
       {st tok out} {rv}
       `{_ : EqDecision tok}
       `{_ : BInfo tok tag}
         (m1 : Machine rv st tok tag out) {_ : First tok m1}
         (m2 : Machine rv st tok tag out) {_ : First tok m2} : First tok (m1 <|> m2).
Proof.
  refine {| first_set := union (first_set (m := m1)) (first_set (m := m2)) |}.
Defined.




Check (^ 3 <|> ^ 4).


Eval cbv in ((parse_exact' _ 3) <|> (parse_exact' _ 4)).

Definition parse_3_or_4 {rv} : Machine rv () nat nat nat:= (^ 3 <|> ^ 4).

Check parse_3_or_4.

Eval vm_compute in (eval_m 42 (^ 3 <|> ^ 4) () [4;3;2]).
Eval vm_compute in (eval_m 42 (^ 3 <|> ^ 4) () [2;4;3]).


(* We need a bunch of axioms for first and follow etc here *)
Definition parse_empty {st tok tag} {rv} : Machine rv st tok tag () := return_ tt.

Definition embed_token {st tok tag out} {rv} `{BInfo tok tag} `{EqDecision tag}
  : tag * out -> Machine rv st tok tag out :=
  fun p => (fun _ => snd p) <$$> (parse_dump [fst p]).


Global Instance first_map {st tok tag out out'}{rv}
       `{EqDecision tok} `{BInfo tok tag} (f : out -> out')
         (m : Machine rv st tok tag out) {_ : First tok m} : First tok (p_map f m).
Proof.
  refine
  {| first_set := first_set (m := m) |}.
Defined.

Notation "$ t" := (embed_token (st:=_) (t, ()))(at level 10).

Definition apply_fun_pair {A B C st tok tag} {rv} (f : A -> B -> C) :
  Machine rv st tok tag A -> Machine rv st tok tag B -> Machine rv st tok tag C :=
  fun m1 m2 => (fun p => f (fst p) (snd p)) <$$> (m1 @* m2).


Definition parse_list_until {A st tok tag : Type} {rv}
           (p : Machine rv st tok tag A)
           (done : SetCompl tag)
           (on_eof : Machine rv st tok tag (list A))
           : Machine rv st tok tag (list A) :=
  parse_fix (fun rec_f =>
               peek done (return_ [])
                    (call p (fun a => (cons a) <$$> Var rec_f))
                    on_eof).


Definition one_to_7 : SetCompl nat := is_set ([1;2;3;4;5;6;7]).

Definition eight_to_inf := compl one_to_7.


Definition parse_list_until_3_or_4 {rv} : Machine rv () nat nat (list nat) :=
  parse_list_until parse_3_or_4 eight_to_inf (return_ []).


Check (eval_m 42 parse_list_until_3_or_4 () [3;4;3;4;4;5;6;3]).

Eval vm_compute in
    (eval_m 5 parse_list_until_3_or_4 () [3]).

Eval vm_compute in
    (eval_m  5 parse_list_until_3_or_4 () [3;4;3;4;4;5;6;3]).

Eval vm_compute in
    (eval_m 5 parse_list_until_3_or_4 () [3;4;3;4;4;8;5;6;3]).

Instance first_dollar : forall st (rv : RecVar)
                               `(t : tok)
  `{EqDecision tok},
    First (rv:=rv) (st:=st) tok ( $t).
Proof.
  intros ? ? ? t ?.
  apply first_map.
  now apply first_dump.
Defined.


Class Lens (A B : Type) := { view : A -> B; set : B -> A -> A}.


Definition Stack A B := Lens A (list B).


Instance lens_triv {A} : Lens A A :=
  {| view := id; set := fun a b => a |}.

Instance lens_pair_fst {A B} : Lens (A * B) A :=
  {| view := fun p => fst p; set := fun a p => (a, snd p) |}.

Definition parse_push {st tok tag A out} {rv}
           `{Lens st (list A)} (a : A) (p : Machine rv st tok tag out) :=
  write (fun s => set (a :: view s) s) p.


Definition parse_pop {st tok tag A : Type} {rv}
           `{Lens st (list A)} : Machine rv st tok tag (option A) :=
  read (fun s => return_ (hd_error (view s))).

Definition pop_queue {st tok tag A : Type} {rv}
           `{Lens st (list A)} : Machine rv st tok tag (list A) :=
  read (fun s => return_ (List.rev (view s))).

Definition parse_list_until_queue {A st tok tag : Type} {rv}
           `{Lens st (list A)}
           (p : Machine rv st tok tag A)
           (done : SetCompl tag)
           (on_eof : Machine rv st tok tag (list A))
           :  Machine rv st tok tag (list A) :=
  parse_fix (fun rec_f => peek done
                                 (pop_queue)
                                 (call p (fun a => parse_push a (Var rec_f)))
                                 on_eof).



Ltac what_the_block t :=
  match t with
  | ?f ?g =>                    (* reduction is blocked because of [f] *)
    what_the_block f
  | match ?v with | _ => _ end => (* reduction is blocked because of [v] *)
    what_the_block v
  | _ =>                        (* reduction is blocked because of [t] itself *)
    constr:(t)
  end.

Axiom test_block : nat.

Example test_what_the_block := Eval vm_compute in
((match test_block return nat -> nat with 0 => fun x => x | S _ => fun _ => 1 end) 5).

Goal unit.
let body_of_t := eval unfold test_what_the_block in test_what_the_block in
    let b := what_the_block body_of_t in idtac b. done.
Qed.

Definition err_equiv {A} : ErrorT A -> ErrorT A -> Prop :=
  fun ea eb =>
    match ea, eb with
    | inl _, inl _ => True
    | inr a, inr b => a = b
    | _, _         => False
    end.

Notation "o1 ≃ₑ o2" := (err_equiv o1 o2)(at level 50).

Instance equiv_err_equiv : forall A, Equivalence (@err_equiv A).
Proof.
  intros; constructor.
  - intro x; destruct x; simpl; auto.
  - intros x y; destruct x; destruct y; simpl; auto.
  - intros x y z; destruct x; destruct y; destruct z; simpl; intros; subst; firstorder.
Qed.

Definition ParseEquiv {st tag tok out}
           `{BInfo tok tag}
           (p q : Machine _ st tok tag out)
  := forall n (state : st) (s : list tok), (eval_m n p state s).1.1 ≃ₑ (eval_m n q state s).1.1
(* This doesn't hold in the case of fusion! *)
(* /\ *)
(* (eval_M p state s).2 = (eval_M q state s).2 *)
.

Notation "p ≃ₘ q" := (ParseEquiv p q) (at level 70).

Instance equiv_p_equiv : forall st tag tok out B, Equivalence (@ParseEquiv st tag tok out B).
Proof.
  intros st tag tok out B; destruct (equiv_err_equiv out).
  constructor; unfold ParseEquiv; intros; eauto.
Qed.

Definition is_push_like {st tag tok out} `{BInfo tok tag}
           `{Lens st (list out)} (p : Machine _ st tok tag out) (q : Machine _ st tok tag out) a :=
  p ≃ₘ parse_push a q.

(* Can't write this! is this an issue? *)
(* Definition parse_head  {st tok : Type} : Machine rv st tok tok := *)
(*   peek_fail (fun t' => drop (return_ t')). *)


Definition pop_stack {st tok tag A} {rv}
           {_ : Lens st (list A)}
  : Machine rv st tok tag (list A) :=
  read (fun s => return_ (view s)).


Instance snd_lens {A B} : Lens (B*A) A := {| view := snd; set:= fun a p => (p.1, a) |}.

Definition parse_list {st tok tag A}{rv} `{EqDecision tag} `{EqDecision tok}
           `{BInfo tok tag}
           (p : Machine rv st tok tag A) {F : First tok p} :
  Machine rv st tok tag (list A) :=
    parse_list_until p (rev_compl (first_set (tok:=tok) (m:=p))) (return_ []).
