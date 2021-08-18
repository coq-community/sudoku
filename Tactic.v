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



(**********************************************************************
       Tactic.v

          Useful tactics


                                      Laurent.Thery@inria.fr (2006)
 **********************************************************************)

(**************************************
  A simple tactic to end a proof
**************************************)
Ltac  finish := intros; auto; trivial; discriminate.


(**************************************
 A tactic for proof by contradiction
     with contradict H
         H:  ~A |-   B     gives       |-   A
         H:  ~A |- ~ B     gives  H: B |-   A
         H:   A |-   B     gives       |- ~ A
         H:   A |-   B     gives       |- ~ A
         H:   A |- ~ B     gives  H: A |- ~ A
**************************************)

Ltac  contradict name :=
     let term := type of name in (
     match term with
       (~_) =>
          match goal with
            |- ~ _  => let x := fresh in
                     (intros x; case name;
                      generalize x; clear x name;
                      intro name)
          | |- _    => case name; clear name
          end
     | _ =>
          match goal with
            |- ~ _  => let x := fresh in
                    (intros x;  absurd term;
                       [idtac | exact name]; generalize x; clear x name;
                       intros name)
          | |- _    => generalize name; absurd term;
                       [idtac | exact name]; clear name
          end
     end).


(**************************************
  A tactic to do case analysis keeping the equality
**************************************)

Ltac case_eq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

(**************************************
 A stupid tactic that tries auto also after applying sym_equal
**************************************)

Ltac sauto := (intros; apply sym_equal; auto; fail) || auto.
