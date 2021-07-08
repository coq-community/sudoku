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

Require Import String.
Import Ascii.
Require Import List.
Open Scope string_scope.
Definition sp := 32.
Definition nl := 10.
Definition sep := 124.

Fixpoint beq_nat (a b: nat) {struct a}: bool :=
  match a, b with
    S a1, S b1 => beq_nat a1 b1
 | 0, 0 => true
 | _,_ => false 
  end.

Definition is_num x := beq_nat ((48 - x) + (x - 57)) 0.
Definition  get_num x :=  x - 48.

Fixpoint mkline s acc {struct s} :=
  match s with
    String a s1 =>
       let n := nat_of_ascii a in 
       if beq_nat n sp then
         match acc with 
          Some x =>  mkline s1 (Some (0::x))
        | _ => mkline s1 None
         end 
        else  if beq_nat n nl then mkline s1 None
        else if beq_nat n sep then
         match acc with 
          Some x =>  app (rev x) (mkline s1 (Some nil))
        | None => mkline s1 (Some nil)
         end 
        else if is_num n then
         match acc with 
          Some x =>  mkline s1 (Some  ((get_num n)::x))
        | None => mkline s1 None
         end  else mkline s1 None
   | _ => nil
  end.

Definition parse p := mkline p None.