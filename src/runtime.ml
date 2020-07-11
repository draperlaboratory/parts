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

(*******************************************************************

These are the functions required to actually execute parsers generated
   using the Opt type constructor.


********************************************************************)

(** The type of stream internals *)
type 'a stream_t = { mutable pos : int; byte_stream : bytes }

let from_file file =
  let ic = open_in file in
  let n = in_channel_length ic in
  let byte_stream = Bytes.create n in
  really_input ic byte_stream 0 n;
  close_in ic;
  { pos = 0; byte_stream = byte_stream }

let from_string string =
  let n = String.length string in
  let byte_stream = Bytes.create n in
  Bytes.blit_string string 0 byte_stream 0 n;
  { pos = 0; byte_stream = byte_stream }

(**  This was just for error messages. We should try to extract to just strings?
     picking a buffer of 128 may be insufficient. I dunno. A quick hack
*)
let string_of_chars chars =
  let buf = Buffer.create 128 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf


let rec fix (f : (('a -> 'b) -> 'a -> 'b)) : 'a -> 'b =
  fun a -> f (fix f) a

let let_ : 'a -> ('a -> 'b) -> 'b =
  fun x f -> f x

let ocaml_peek : 'a stream_t -> ('a option -> 'b) -> 'b  =
  fun st k ->
  if st.pos < Bytes.length st.byte_stream then
    let head = Obj.magic (Bytes.unsafe_get st.byte_stream st.pos) in
    k (Some head)
  else
    k None

let ocaml_drop : 'a stream_t -> ('a stream_t -> 'b) -> 'b  =
  fun st k -> st.pos <- st.pos + 1; k st

let ocaml_lookahead : 'a stream_t -> ('a stream_t -> 'b) -> 'b =
  fun st k ->
  let old_st = { pos = st.pos; byte_stream = st.byte_stream } in
  k old_st

exception Parse_fail of string

let failwith_ : string -> 'a =
  fun msg ->
  let err_str = Printf.sprintf "Error: %s\n" msg in
  raise (Parse_fail err_str)
