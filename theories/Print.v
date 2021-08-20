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

Require Import List.
Require Import String.

(* Printing function *)

Fixpoint is_eq (n m: nat) {struct n} :=
 match n, m with
  0, 0 => true | (S n1), (S m1) => is_eq n1 m1 | _ ,_ => false end.

Fixpoint adiv (n m p: nat) {struct p} :=
  match p with 0 => false | (S p1) =>
    if (is_eq n m) then true else adiv (n - m) m p1
  end.

Definition div n m :=
match m with 0 => true | _ => adiv m n m end.

Fixpoint print_line (n m: nat) (l: list nat) {struct n}:
  string * list nat :=
let v := if (div m n) then "|"%string else ""%string in
match n, l with
    O  ,    _ => (v, l)
|  (S n1), (0 :: l1) =>
    let (s1, l2) := print_line n1 m l1 in
                 (append v (append " " s1),
                  l2)
|  (S n1), (n :: l1) =>
    let (s1, l2) := print_line n1 m l1 in
                 (append v
                  (String (Ascii.ascii_of_nat (n + 48)) s1),
                  l2)
| _,_ => ("error"%string , l)
end.

Fixpoint paux (m n p q: nat) (s: string) (l: list nat) {struct m}:
  string :=
let v := if (div p m) then s else ""%string in
append v
match m with
    O      => ""%string
|  (S m1)  =>
    let (s1, l1) := print_line n q l in
      append s1 (String (Ascii.ascii_of_nat 10) (paux m1 n p q s l1))
end.

Fixpoint print_sep (n: nat): string :=
  match n with 0 => ""%string | S n1 => append "-" (print_sep n1) end.

Definition print n m s :=
  let lf := Ascii.ascii_of_nat 10 in
  let nm := n * m in
  let s1 := (append
               (print_sep (1 + n + nm))
               (String lf ""%string))
 in
  String lf (paux nm nm n m s1 s).
