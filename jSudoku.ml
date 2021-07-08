(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(** link code **)

open Js_of_ocaml
open Sudoku

let rec n2nat n = if n = 0 then O else S (n2nat (n - 1))

let rec nat2n n = match n with O -> 0 | S n -> 1 + (nat2n n)

let string2l s =
  let le = String.length s in
  let rec iter i = if i = le then Nil else
      Cons (n2nat (Char.code (String.get s i) - 48), iter (i + 1)) in
  iter 0

let rec l2stringr s l =
  match l with
    Nil -> s
  | Cons (n,l) ->  l2stringr (s ^ (Char.escaped (Char.chr (nat2n n + 48)))) l

let l2string l = l2stringr "" l

let main s =
  let l = string2l s in
  match find_just_one (S (S (S O))) (S (S (S O))) l with
  | JNone -> "N"
  | JOne l -> "O" ^ (l2string l)
  | JMore (l1,l2)  -> "M" ^ (l2string l1) ^ "M" ^ (l2string l2)

let _ =
  Js.export_all
    (object%js
      method solve s = Js.string (main (Js.to_string s))
    end)
