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


(******************************************************************************)
(*     Div.v                                                                  *)
(*                                                                            *)
(*     Definitions: div mod                                                   *)
(*                                                                            *)
(*                                                                            *)
(*                                    Laurent.Thery@inria.fr (2006)           *)
(******************************************************************************)

Require Import Arith.
Require Import Tactic.
Require Import Psatz.

Notation "'div'" := Nat.div.
Notation "'mod'" := Nat.modulo.

Theorem div_mod_correct: forall n m, 0 < m -> n = div n m * m + mod n m.
Proof. intros n m H; rewrite Nat.mul_comm; apply Nat.div_mod; lia. Qed.

Theorem mod_lt: forall n m, 0 < m -> mod n m < m.
Proof. intros n m H; apply Nat.mod_upper_bound; lia. Qed.

Theorem div_lt: forall a b c, a < b * c -> div a b < c.
Proof. intros a b c H; apply Nat.div_lt_upper_bound; lia. Qed.

Theorem div_is_0: forall n m, n < m -> div n m = 0.
Proof. intros; now apply Nat.div_small. Qed.

Theorem mult_lt_plus: forall a b c d, a < b -> c < d -> a * d + c < b * d.
Proof. nia. Qed.

Theorem lexico_mult: forall a1 a2 b c1 c2,
    c1 < b -> c2 < b -> a1 * b + c1 = a2 * b + c2 -> a1 = a2.
Proof. nia. Qed.

Theorem div_mult_comp: forall n m p, 0 < p ->  div (p * m + n) p = m + div n p.
Proof.
intros n m p H0.
apply lexico_mult with (b := p) (c1 := mod (p * m + n) p) (c2 := mod n p);
  try apply mod_lt; auto with arith.
rewrite Nat.mul_add_distr_r, <- Nat.add_assoc;
  repeat rewrite <- div_mod_correct; auto with arith.
Qed.

Theorem mod_small: forall n m, n < m -> mod n m = n.
Proof. now intros; apply Nat.mod_small. Qed.

Theorem mod_mult_comp: forall n m p, 0 < p ->  mod (p * m + n) p = mod n p.
Proof.
intros n m p H; apply Nat.add_cancel_l with (div (p * m + n) p * p).
rewrite <- div_mod_correct, div_mult_comp,  Nat.mul_add_distr_r, (Nat.mul_comm p),  <- Nat.add_assoc by assumption.
f_equal. now apply div_mod_correct.
Qed.
