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

(* Borrowed with kind permission from Sam Lasser *)
Require Import List.

Ltac sis := simpl in *.

Ltac inv H := inversion H; subst; clear H.

Ltac tc := try congruence.

(* destruct a match in a hypothesis *)
Ltac dmh := match goal with
             | H : context[match ?x with | _ => _ end] |- _ => destruct x
             end.

(* destruct a match in the goal *)
Ltac dmg := match goal with
             | |- context[match ?x with | _ => _ end] => destruct x
             end.

Ltac dm  := (first [dmh | dmg]); auto.

Ltac dms := repeat dm.

(* destruct a match in a hypothesis, and save the equality in the context *)
Ltac dmheq s := let Heq := fresh s in
                match goal with
                | H : context[match ?x with | _ => _ end] |- _ =>
                  destruct x eqn:Heq
                end.

(* destruct a match in the goal, and save the equality in the context *)
Ltac dmgeq s := let Heq := fresh s in
                match goal with
                | |- context[match ?x with | _ => _ end] => destruct x eqn:Heq
                end.

Ltac dmeq s := (first [dmheq s | dmgeq s]); auto.

Ltac dmeqs s := repeat dmeq s.

Ltac apps := try solve [ repeat rewrite app_assoc; auto
                       | repeat rewrite <- app_assoc; auto
                       | repeat rewrite app_nil_r; auto].

Ltac rew_anr := repeat rewrite app_nil_r in *.
