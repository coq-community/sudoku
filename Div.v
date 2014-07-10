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


(***********************************************************************
      Div.v                                                                                       
                                                                                                         
      Definition of division and modulo                                 
                                                                                                         
      Definitions: div mod                                                                         
                                                                                                         
                                     Laurent.Thery@inria.fr (2006)                
************************************************************************)
Require Import Arith.
Require Import Tactic.

Fixpoint div_aux (n m1 m2 p: nat) {struct n}: nat :=
  match m1 with 
    O => 
       match p with
            O => 1 
       | S p1 => 
         match n with 
           0 => 0 (* impossible *) 
         | S n1 => S (div_aux n1 m2 m2 p1) 
         end
       end
   | S m => 
       match p with
        O => 0 
       | S p1  => 
         match n with 
           0 => 0 (* impossible *)
         | S n1 => div_aux n1 m m2 p1
         end
       end
  end.

Definition div n m := match m with O => O | S m1 => div_aux n m m1 n end.

Fixpoint mod_aux (n m1 m2 p r: nat) {struct n}: nat :=
  match m1 with 
    O => 
       match p with
            O => 0 
       | S p1 => 
         match n with 
           0 => 0 (* impossible *) 
         | S n1 => (mod_aux n1 m2 m2 p1 p) 
         end
       end
   | S m => 
       match p with
        O => r
       | S p1  => 
         match n with 
           0 => 0 (* impossible *)
         | S n1 => mod_aux n1 m m2 p1 r
         end
       end
  end.

Theorem div_mod_aux_correct:
forall n m1 m2 p r, p <= n -> m1 <= S m2 -> r + m1 = p + S m2 ->
   div_aux n m1 m2 p * (S m2) + m1 + mod_aux n m1 m2 p r = p + (S m2).
intros n; elim n; simpl; auto.
intros m1 m2 p r; case p.
intros _; case m1; auto with arith.
rewrite mult_1_l; rewrite plus_0_l; rewrite plus_0_r; auto with arith.
intros p1; repeat (rewrite mult_0_l || rewrite plus_0_l || rewrite plus_0_r); auto.
intros p1; repeat (rewrite mult_0_l || rewrite plus_0_l || rewrite plus_0_r); auto.
intros _ H; rewrite <- H; auto with arith.
intros n1 H; contradict H; auto with arith.
intros n1 Rec m1 m2 p; case m1; case p;
 repeat (rewrite mult_1_l || rewrite plus_0_l || rewrite plus_0_r);
 auto with arith.
intros p1 r H1 H2 H3.
match goal with |- ?X = ?Y =>
  replace X with (S ((div_aux n1 m2 m2 p1) * S m2 + m2 + mod_aux n1 m2 m2 p1 (S p1)));
  replace Y with (S (p1 + S m2))
end; auto with arith.
eq_tac; auto with arith.
apply Rec; auto with arith.
rewrite <- plus_n_Sm; auto.
simpl; rewrite plus_0_r; eq_tac; auto with arith.
intros m r _ _ H; rewrite <- H; auto with arith.
intros p1 m r H H1 H2.
match goal with |- ?X = ?Y =>
  replace X with (S (div_aux n1 m m2 p1 * S m2 + m + mod_aux n1 m m2 p1 r));
  replace Y with (S (p1 + S m2))
end; auto with arith.
eq_tac; auto with arith.
apply Rec; auto with arith.
apply eq_add_S.
simpl in H2; rewrite <- H2.
rewrite <- plus_n_Sm; auto.
rewrite <- plus_n_Sm; auto.
Qed.

Theorem mod_aux_lt:
forall n m1 m2 p r, p <= n -> m1 <= S m2 -> r + m1 = p + S m2 ->
   mod_aux n m1 m2 p r < (S m2).
intros n; elim n; simpl; auto.
intros m1 m2 p r; case p.
intros _; case m1; auto with arith.
intros m _ H; rewrite plus_0_l in H; rewrite <- H; auto with arith.
apply le_lt_trans with (r + 0); auto with arith.
intros n1 H; contradict H; auto with arith.
intros n1 Rec m1 m2 p; case m1; case p;
 repeat (rewrite mult_1_l || rewrite plus_0_l || rewrite plus_0_r);
 auto with arith.
intros p1 r H1 H2 H3; apply Rec; auto with arith.
rewrite <- plus_n_Sm; auto.
intros m r _ _ H; rewrite <- H; auto with arith.
apply le_lt_trans with (r + 0); auto with arith.
intros p1 m r H H1 H2.
apply Rec; auto with arith.
apply eq_add_S.
rewrite plus_n_Sm; auto.
Qed.

Definition modulo n m := match m with O => O | S m1 => mod_aux n m m1 n n end.
Notation "'mod'" := modulo.


Theorem div_mod_correct: forall n m, 0 < m -> n = div n m * m + mod n m. 
intros n m; case m; simpl; auto with arith.
intros H; contradict H; auto with arith.
intros m1 H.
apply plus_reg_l with (S m1).
repeat rewrite (plus_comm (S m1)).
rewrite <- (div_mod_aux_correct n (S m1) m1 n n); auto with arith.
repeat rewrite <- plus_assoc; auto with arith.
Qed.

Theorem mod_lt: forall n m, 0 < m -> mod n m < m. 
intros n m; case m; simpl; auto with arith.
intros m1 H; apply mod_aux_lt; auto with arith.
Qed.

Theorem div_lt: forall a b c, a < b * c -> div a b < c.
intros a b c H; rewrite (div_mod_correct a b) in H.
case (le_or_lt c (div a b)); auto; intros H1; contradict H.
apply le_not_lt.
apply le_trans with (b * (div a b) + 0); auto with arith.
rewrite (mult_comm b); auto with arith.
generalize H; case b; auto with arith.
intros H1; contradict H1; auto with arith.
Qed.

Theorem div_is_0: forall n m, n < m -> div n m = 0.
intros n m H; assert (div n m < 1); auto with arith.
apply div_lt; auto with arith.
rewrite mult_1_r; auto with arith.
generalize H0; case (div n m); auto with arith.
intros n1 H1; contradict H1; apply le_not_lt; auto with arith.
Qed.

Theorem mult_lt_plus: forall a b c d, a < b -> c < d -> a * d + c < b * d.
intros a b c d HH HH1.
apply lt_le_trans with ((S a) * d); auto with arith.
simpl; rewrite plus_comm; auto with arith.
apply mult_le_compat_r; auto with arith.
Qed.

Theorem lexico_mult: forall a1 a2 b c1 c2, 
  c1 < b -> c2 < b -> a1 * b + c1 = a2 * b + c2 -> a1 = a2.
intros a1 a2 b c1 c2 H1 H2 H3.
case (le_or_lt a1 a2); intros H4.
case le_lt_or_eq with (1 := H4); auto; clear H4; intros H4.
absurd (a1 * b + c1 < a2 * b + c2); auto with arith.
rewrite H3; auto with arith.
apply lt_le_trans with ((S a1) * b + 0); auto with arith.
rewrite plus_0_r; simpl; rewrite (plus_comm b); auto with arith.
apply plus_le_compat; auto with arith.
apply mult_le_compat_r; auto with arith.
absurd (a2 * b + c2 < a1 * b + c1); auto with arith.
rewrite H3; auto with arith.
apply lt_le_trans with ((S a2) * b + 0); auto with arith.
rewrite plus_0_r; simpl; rewrite (plus_comm b); auto with arith.
apply plus_le_compat; auto with arith.
apply mult_le_compat_r; auto with arith.
Qed.

Theorem div_mult_comp: forall n m p, 0 < p ->  div (p * m + n) p = m + div n p.
intros n m p H0; apply lexico_mult with (b := p) (c1 := mod (p * m + n) p) (c2 := mod n p); 
  try apply mod_lt; auto with arith.
rewrite mult_plus_distr_r; rewrite <- plus_assoc;
  repeat rewrite <- div_mod_correct; auto with arith.
Qed.

Theorem mod_small: forall n m, n < m -> mod n m = n.
intros n m H; pattern n at 2; rewrite (div_mod_correct n m).
rewrite div_is_0; auto.
apply le_lt_trans with (2 := H); auto with arith.
Qed.

Theorem mod_mult_comp: forall n m p, 0 < p ->  mod (p * m + n) p = mod n p.
intros n m p H; apply plus_reg_l with (div (p * m + n) p * p).
rewrite <- div_mod_correct; auto.
rewrite div_mult_comp; auto.
rewrite mult_plus_distr_r; rewrite (mult_comm p); rewrite <- plus_assoc.
eq_tac; apply div_mod_correct; auto.
Qed.

