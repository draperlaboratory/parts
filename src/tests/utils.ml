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
open P_json
open Example_parsers

let explode s = List.init (String.length s) (String.get s)


let make_stream (str : 'a ocaml_stream) : ('a ocaml_stream, 'a) stream =
  { state = str; peek_st = (fun _ -> Runtime.ocaml_peek); drop_st = (fun _ -> Runtime.ocaml_drop) }

(* stream takes care of cleanup of in_channel? *)
let stream_file filename : char Stream.t = Stream.of_channel (open_in filename)

let rec json_to_string json = match json with
| Json_bool bool -> Bool.to_string bool
| Json_null -> "null"
| Json_string  charlist -> "\"" ^ Runtime.string_of_chars charlist ^ "\""
| Json_num charlist -> (Runtime.string_of_chars charlist)
| Json_list json_vallist -> "[" ^ String.concat " , " (List.map json_to_string json_vallist ) ^"]"
| Json_obj listobj  -> "{" ^ (String.concat " , " (List.map 
  (fun  (charlist, jval) ->  (Runtime.string_of_chars charlist)
      ^ ( " : " ) ^  (json_to_string jval) )
     listobj )) ^ "}"
(**

type json_val =
| Json_bool of bool
| Json_string of char list
| Json_num of char list
| Json_list of json_val list
| Json_obj of (char list * json_val) list 

let json_to_string json = match json with
| Json_bool bool -> Bool.to_string bool
| Json_string  charlist -> List.
| Json_num charlist -> String.concat "" (List.map Runtime.string_of_chars list)
| Json_list json_vallist ->
| Json_obj listobj  ->
*)
