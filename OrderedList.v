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


(********************************************************)
(*    OrderedList.v                                     *)
(*     Ordered List                                     *)
(*                               thery@sophia.inria.fr  *)
(*                                      (2006)          *)
(********************************************************)
Require Import List.
Require Import Permutation.
Require Import UList.

Section ordered.

(* The type of the elements in the list *)
Variable A: Set.

(* Comparison values *)
Inductive cmp : Set := lt | eq | gt.

(* Opposite *)
Definition opp v := match v with lt => gt | eq => eq | gt => lt end.

(* Weight function *)
Variable weight: A -> A -> cmp.

(* Transitivity *)
Hypothesis weight_trans: 
  forall a b c, weight a b = weight b c -> weight a c = weight a b.

(* Anti symmetry *)
Hypothesis weight_anti_sym: 
  forall a b, weight b a = opp (weight a b).

(* Reflexivity *)
Theorem weight_refl: forall a, weight a a = eq.
intros a; generalize (weight_anti_sym a a); 
  case (weight a a); auto; intros; discriminate.
Qed.

(* Compatibility left *)
Hypothesis weight_compat_l: 
  forall a b c, weight a b = eq -> weight a c = weight b c.

(* Compatibility right *)
Theorem weight_compat_r: 
  forall a b c, weight a b = eq -> weight c a = weight c b.
intros a b c H; repeat rewrite (fun x => weight_anti_sym x c).
rewrite weight_compat_l with (b := b); auto.
Qed.

(* No collision *)
Hypothesis weight_exact: 
  forall a b, weight a b = eq -> a = b.

Theorem weight_equiv:
  forall a b, weight a b = eq <-> a = b.
intros a b; split; intros H; subst; auto.
apply weight_refl.
Qed.

Definition A_dec : forall a b: A, {a = b} + {a <> b}.
intros a b; generalize (weight_equiv a b); 
  case (weight a b); intros (H1, H2); auto.
right; intros H; generalize (H2 H); intros; discriminate.
right; intros H; generalize (H2 H); intros; discriminate.
Defined.

(* Ordered list *)
Inductive olist: list A -> Prop :=
   olist_nil: olist nil
|  olist_one: forall a, olist (a :: nil)
| olist_cons: forall a b l, 
      weight a b = lt -> olist (b::l) -> olist (a::b::l).

(* Removing the first element of an ordered list, the list
   remains ordered 
 *)
Theorem olist_inv: forall a l, olist (a :: l) -> olist l.
intros a l; case l; simpl; auto.
intros H; apply olist_nil.
intros a1 l1 H; inversion H; auto.
Qed.

(* Removing the second element of an ordered list, the list
   remains ordered 
 *)
Theorem olist_skip:
  forall a b l, olist (a :: b :: l) -> olist (a :: l).
intros a b l; generalize a b; elim l; simpl; auto.
intros; apply olist_one.
intros a1 l1 Rec a2 b1 H.
assert (Eq1: weight a2 b1 = lt).
inversion H; auto.
assert (Eq2: weight b1 a1 = lt).
inversion_clear H as [| H0 H1|]; auto.
inversion_clear H1 ; auto.
apply olist_cons; auto.
rewrite weight_trans with (b := b1); auto.
apply trans_equal with (1 := Eq1); auto.
inversion_clear H; auto.
inversion_clear H1; auto.
Qed.


(* All the elements in an ordered list are smaller thant the head *)
Theorem olist_weight:
  forall a b l, olist (a :: l) -> In b l -> weight a b = lt.
intros a b l H; generalize a b H; elim l; clear a b l H.
intros a b _ H1; case H1.
simpl; intros a1 l Rec a b H [H1 | H1]; subst; auto.
inversion H; auto.
assert (Eq1: weight a a1 = lt).
inversion H; auto.
rewrite weight_trans with (b := a1); auto.
rewrite Eq1; apply sym_equal; apply Rec; auto.
inversion_clear H; auto.
Qed.

(* An ordered list is unique *)
Theorem olist_ulist: forall l, olist l -> ulist l.
intros l; elim l; simpl; auto.
intros a l1; case l1; auto.
intros b l2 Rec H; inversion_clear H as [| H0 H1 |].
apply ulist_cons; auto.
simpl; intros [H2 | H2]; subst; auto.
rewrite weight_refl in H0; discriminate.
generalize (weight_anti_sym a b); rewrite H0.
rewrite olist_weight with (l := l2); auto.
intros; discriminate.
Qed.

(* Check if a literal is in a clause *)
Fixpoint is_in (a: A) (l: list A) {struct l}: bool :=
  match l with 
    nil => false
  | b :: l1 => 
     match weight a b with
       eq => true 
     | lt => false
     | gt => is_in a l1
     end
  end.

Theorem is_in_correct: 
  forall a l, olist l -> if is_in a l then In a l else ~ In a l.
intros a l; elim l; simpl; auto.
intros b l1 Rec H.
assert (F0: olist l1); try (apply olist_inv with (1 := H)).
case_eq (weight a b); intros H1; auto.
intros [H3 | H3]; subst; auto.
rewrite weight_refl in H1; discriminate.
generalize (weight_anti_sym b a); rewrite H1.
rewrite olist_weight with (l := l1); simpl; intros; auto;
  discriminate.
rewrite weight_exact with (1 := H1); auto.
generalize (Rec F0); case (is_in a l1); auto.
intros H3 [H4 | H4]; subst; auto.
rewrite weight_refl in H1; discriminate.
Qed.

(* Insert an element in an ordered list with duplication *)
Fixpoint insert (a: A) (l: list A) {struct l}: list A :=
  match l with
    nil => a :: nil
  | b :: l1 =>
      match weight a b with
        lt => a :: l
      | eq => l
      | gt => b :: insert a l1
      end
  end.

(* The inserted element is in the result *)
Theorem insert_in: forall a l, In a (insert a l).
intros a l; elim l; simpl; auto.
intros b l1 H; case_eq (weight a b); auto with datatypes.
intros H1; rewrite weight_exact with (1 := H1); 
  auto with datatypes.
Qed.

(* The initial list is in the result *)
Theorem insert_incl: forall a l, incl l (insert a l).
intros a l; elim l; simpl; auto with datatypes.
intros b l1 H; case_eq (weight a b); auto with datatypes.
Qed.

(* The result contains only the initial list or the inserted element *)
Theorem insert_inv: forall a b l, In a (insert b l) -> a = b \/ In a l.
intros a b l; elim l; simpl; auto with datatypes.
intuition.
intros c l1 H; case_eq (weight b c); simpl; auto with datatypes.
intuition.
intuition.
Qed.

(* If the initial list is ordered so is the result *)
Theorem insert_olist: forall a l, olist l -> olist (insert a l).
intros a l; elim l; simpl; auto.
intros; apply olist_one; auto.
intros b l1 Rec H; case_eq (weight a b); intros H1; auto.
apply olist_cons; auto.
assert (Eq1: olist l1); try apply olist_inv with (1 := H).
generalize (Rec Eq1).
assert (Eq2: forall c, In c (insert a l1) -> weight b c = lt).
intros c H2.
case insert_inv with (1 := H2); auto.
intros; subst; rewrite weight_anti_sym; rewrite H1; auto.
intros H3; apply olist_weight with (1 := H); auto.
generalize Eq2; case (insert a l1); auto.
intros; apply olist_one.
intros c l2 H2 H3; apply olist_cons; auto with datatypes.
Qed.

(* Insert an element in an ordered list l if needed (a does not 
   occur in l) and then call the continuation f with the tail of l 
 *)
Fixpoint insert_cont (f: list A -> list A) (a: A) (l: list A) {struct l}: 
      list A :=
  match l with
    nil => a :: f nil
  | b :: l1 =>
      match weight a b with
        lt => a :: f l
      | eq => a :: f l1
      | gt => b :: insert_cont f a l1
      end
  end.

(* Merge two ordered lists *)
Fixpoint merge (l1 l2: list A) {struct l1}: list A :=
  match l1 with
    nil => l2
  | a :: l3 => insert_cont (merge l3) a l2
  end.

Theorem merge_incl_l: forall l1 l2, incl l1 (merge l1 l2).
intros l1; elim l1; simpl; auto with datatypes; clear l1.
intros l1 a H; case H.
intros a l1 Rec l2 b; simpl; intros [H | H]; subst; auto.
elim l2; simpl; auto; clear l2.
intros c l2 Rec1; case_eq (weight b c); intros H; auto with datatypes.
elim l2; simpl; auto; clear l2.
right; apply (Rec nil b); auto.
intros c l2 Rec1; case_eq (weight a c); intros H1; auto with datatypes.
simpl; right; apply (Rec (c :: l2) b); auto.
simpl; right; apply (Rec l2 b); auto.
Qed.

Theorem merge_incl_r: forall l1 l2, incl l2 (merge l1 l2).
intros l1; elim l1; simpl; auto with datatypes.
intros a l3 Rec l2; elim l2; simpl; auto with datatypes; clear l2.
intros b l2 Rec1; case_eq (weight a b); intros H; auto with datatypes.
intro c; simpl; intros [H1 | H1]; subst. 
left; apply weight_exact; auto.
right; apply (Rec l2 c); auto.
Qed.

Theorem merge_inv: forall a l1 l2, In a (merge l1 l2) -> In a l1 \/ In a l2.
intros a l1; elim l1; simpl; auto; clear l1.
intros b l1 Rec l2; elim l2; simpl; auto; clear l2.
intros [H | H]; auto.
case (Rec nil); auto.
intros c l2 Rec1; case (weight b c); simpl; intros [H | H]; subst; auto.
case (Rec (c :: l2)); auto.
case (Rec l2); auto.
case Rec1; auto.
Qed.

(* Old trick to prove that ordering is preserved we first need
   to prove something stronger 
 *)
Theorem merge_olist_strong: forall a l1 l2, 
  olist (a :: l1) -> olist (a :: l2)  -> olist (a :: merge l1 l2).
intros a l1; generalize a; elim l1; simpl; auto; clear a l1.
intros b l1 Rec a l2 H.
assert (V1: weight a b = lt); try apply olist_weight with (1 := H); auto with datatypes.
assert (V2: olist (b :: l1)); try apply olist_inv with (1 := H).
generalize a V1; elim l2; simpl; clear a l2 H V1; auto.
intros a V1 _; apply olist_cons; auto.
apply Rec; auto.
apply olist_one; auto.
intros c l2 Rec1 a V1 H1; case_eq (weight b c); intros H2.
apply olist_cons; auto.
apply Rec; auto with datatypes.
apply olist_cons; auto.
apply olist_inv with (1 := H1); auto.
apply olist_cons; auto.
apply Rec; auto with datatypes.
rewrite weight_exact with (1 := H2); auto.
apply olist_inv with (1 := H1); auto.
apply olist_cons; auto.
apply olist_weight with (1 := H1); auto with datatypes.
apply Rec1; auto.
rewrite weight_anti_sym; rewrite H2; auto.
apply olist_inv with (1 := H1); auto.
Qed.

(* merge keeps ordering *)
Theorem merge_olist: forall l1 l2, 
  olist l1 -> olist l2  -> olist (merge l1 l2).
intros l1; case l1; clear l1; simpl; auto.
intros a l1 l2; case l2; simpl; auto; clear l2.
intros; apply merge_olist_strong; auto.
apply olist_one; auto.
intros b l2 H H1.
case_eq (weight a b); intros H2; auto.
apply merge_olist_strong; auto.
apply olist_cons; auto.
apply merge_olist_strong; auto.
rewrite weight_exact with (1 := H2); auto.
generalize b H H1 H2; elim l2; simpl; auto; clear l2 b H H1 H2.
intros b H H1 H2; apply olist_cons; auto.
rewrite weight_anti_sym; rewrite H2; auto.
apply merge_olist_strong; auto.
apply olist_one; auto.
intros b l2 Rec c H H1 H2.
case_eq (weight a b); intros H3; auto.
apply olist_cons; auto.
rewrite weight_anti_sym; rewrite H2; auto.
apply merge_olist_strong; auto.
apply olist_cons; auto.
apply olist_inv with (1 := H1); auto.
apply olist_cons; auto.
rewrite weight_anti_sym; rewrite H2; auto.
apply merge_olist_strong; auto.
rewrite weight_exact with (1 := H3); auto.
apply olist_inv with (1 := H1); auto.
apply olist_cons; auto.
apply olist_weight with (1 := H1); auto with datatypes.
apply Rec; auto.
apply olist_inv with (1 := H1); auto.
Qed.


(* Insert an element in an ordered list *)
Fixpoint  ocons (a: A) (l: list A) {struct l}: list A :=
  match l with
    nil => a :: nil
  | b :: l1 =>
      match weight a b with
        lt => a :: l
      | eq => a :: l
      | gt => b :: ocons a l1
      end
  end.

(* ocons always increments the length *)
Theorem ocons_length: forall a l, length (ocons a l) = S (length l).
intros a l; elim l; simpl; auto.
intros b l1 H; case (weight a b); simpl; auto.
Qed.

(* The inserted element is in the result *)
Theorem ocons_in: forall a l, In a (ocons a l).
intros a l; elim l; simpl; auto.
intros b l1 H; case_eq (weight a b); auto with datatypes.
Qed.

(* The initial list is in the result *)
Theorem ocons_incl: forall a l, incl l (ocons a l).
intros a l; elim l; simpl; auto with datatypes.
intros b l1 H; case_eq (weight a b); auto with datatypes.
Qed.

(* The result contains only the initial list or the inserted element *)
Theorem ocons_inv: forall a b l, In a (ocons b l) -> a = b \/ In a l.
intros a b l; elim l; simpl; auto with datatypes.
intuition.
intros c l1 H; case_eq (weight b c); simpl; auto with datatypes.
intuition.
intuition.
intuition.
Qed.

(* Add an element in an ordered list l with possible duplication
   and then call the continuation f with the tail of l 
 *)
Fixpoint add_cont (f: list A -> list A) (a: A) (l: list A) {struct l}: 
      list A :=
  match l with
    nil => a :: f nil
  | b :: l1 =>
      match weight a b with
        lt => a :: f l
      | eq => a :: f l
      | gt => b :: add_cont f a l1
      end
  end.

(* Add two ordered lists with possible duplication *)
Fixpoint add (l1 l2: list A) {struct l1}: list A :=
  match l1 with
    nil => l2
  | a :: l3 => add_cont (add l3) a l2
  end.

Theorem add_length: forall l1 l2, length (add l1 l2) = length l1 + length l2.
intros l1; elim l1; simpl; auto; clear l1.
intros a l1 Rec l2; elim l2; simpl; auto; clear l2.
rewrite Rec; auto.
intros b l2 Rec1; case (weight a b); simpl; auto.
rewrite Rec; simpl; repeat rewrite <- plus_n_Sm; auto with arith.
rewrite Rec; simpl; repeat rewrite <- plus_n_Sm; auto with arith.
rewrite Rec1; simpl; repeat rewrite <- plus_n_Sm; auto with arith.
Qed.

Theorem add_incl_l: forall l1 l2, incl l1 (add l1 l2).
intros l1; elim l1; simpl; auto with datatypes; clear l1.
intros l1 a H; case H.
intros a l1 Rec l2 b; simpl; intros [H | H]; subst; auto.
elim l2; simpl; auto; clear l2.
intros c l2 Rec1; case_eq (weight b c); intros H; auto with datatypes.
elim l2; simpl; auto; clear l2.
right; apply (Rec nil b); auto.
intros c l2 Rec1; case_eq (weight a c); intros H1; auto with datatypes.
simpl; right; apply (Rec (c :: l2) b); auto.
simpl; right; apply (Rec (c :: l2) b); auto.
Qed.

Theorem add_incl_r: forall l1 l2, incl l2 (add l1 l2).
intros l1; elim l1; simpl; auto with datatypes.
intros a l3 Rec l2; elim l2; simpl; auto with datatypes; clear l2.
intros b l2 Rec1; case_eq (weight a b); intros H; auto with datatypes.
Qed.

Theorem add_inv: forall a l1 l2, In a (add l1 l2) -> In a l1 \/ In a l2.
intros a l1; elim l1; simpl; auto; clear l1.
intros b l1 Rec l2; elim l2; simpl; auto; clear l2.
intros [H | H]; auto.
case (Rec nil); auto.
intros c l2 Rec1; case (weight b c); simpl; intros [H | H]; subst; auto.
case (Rec (c :: l2)); auto.
case (Rec (c :: l2)); auto.
case Rec1; auto.
Qed.

(* Remove an element from the list l if needed and then call
   the continuation f on the tail of l 
 *)
Fixpoint rm_cont (f: list A -> list A) (a: A) (l: list A) {struct l}:
          list A :=
  match l with 
    nil => nil
  | b :: l1 => 
     match weight a b with
       eq => f l1
     | lt => f l
     | gt => b :: rm_cont f a l1
     end
  end.

(* Remove all the element of the list l1 from the list l2 *)
Fixpoint rm (l1 l2: list A) {struct l1}: list A :=
  match l1 with
    nil => l2
  | a :: l3 =>
      rm_cont (rm l3) a l2
  end.

Theorem rm_incl: forall l1 l2, incl (rm l1 l2) l2.
intros l1; elim l1; simpl; auto with datatypes; clear l1.
intros a l1 Rec l2; elim l2; simpl; auto with datatypes; clear l2.
intros b l2 H; case_eq (weight a b); auto with datatypes.
Qed.

Theorem rm_not_in: forall (a: A) l1 l2, olist l1 -> olist l2 ->
  In a l1 -> ~ In a (rm l1 l2).
intros a l1; generalize a; elim l1; simpl; auto; clear a l1.
intros b l1 Rec a l2 H1 H2.
assert (O1: olist l1); try apply olist_inv with (1 := H1).
intros [H | H]; subst; auto.
generalize H2; elim l2; simpl; auto with datatypes; clear l2 H2.
intros b l2 Rec1 H2.
assert (O2: olist l2); try apply olist_inv with (1 := H2).
case_eq (weight a b); auto with datatypes; intros H3.
intros H4; absurd (In a (b :: l2)); auto.
simpl; intros [H5 | H5]; subst.
rewrite weight_refl in H3; discriminate.
rewrite weight_anti_sym in H3; rewrite (olist_weight b a l2) in H3;
  try discriminate; auto.
apply (rm_incl l1 (b :: l2) a); auto.
assert (a = b); subst.
apply weight_exact with (1 := H3).
intros H4; absurd (In b l2); auto.
assert (H5: ulist (b :: l2)); try apply olist_ulist; auto.
inversion H5; auto.
apply (rm_incl l1 l2 b); auto.
simpl; intros [H4 | H4]; subst.
rewrite weight_refl in H3; discriminate.
case Rec1; auto.
generalize H2; elim l2; simpl; auto with datatypes; clear l2 H2.
intros c l2 Rec1 H2.
assert (O2: olist l2); try apply olist_inv with (1 := H2).
case_eq (weight b c); auto with datatypes; intros H3.
simpl; intros [H4 | H4]; subst.
rewrite (olist_weight b a l1) in H3; auto; discriminate.
case Rec1; auto.
Qed.

Theorem rm_in: forall (a: A) l1 l2, olist l1 -> olist l2 ->
  ~ In a l1 -> In a l2 -> In a (rm l1 l2).
intros a l1; generalize a; elim l1; simpl; auto; clear a l1.
intros b l1 Rec a l2 H1 H2 H3 H4.
generalize H2 H4; elim l2; simpl; auto; clear l2 H2 H4.
assert (O1: olist l1); try apply olist_inv with (1 := H1).
intros c l3 Rec1 H4 [H5 | H5]; subst.
case_eq (weight b a); auto with datatypes; intros H5.
case H3; rewrite weight_exact with (1 := H5); auto.
assert (O2: olist l3); try apply olist_inv with (1 := H4).
case_eq (weight b c); auto with datatypes; intros H6.
Qed.

Theorem rm_olist_strong: forall a l1 l2, 
  olist (a :: l2) -> olist (a :: rm l1 l2).
intros a l1; generalize a; elim l1; simpl; auto; clear a l1.
intros a l1 Rec c l2; generalize c; elim l2; simpl; auto; clear c l2.
intros b l2 Rec1 c H.
case_eq (weight a b); intros H1; auto.
apply Rec; auto.
apply olist_skip with (1 := H); auto.
apply olist_cons; auto.
apply olist_weight with (1 := H); auto with datatypes.
apply Rec1; auto.
apply olist_inv with (1 := H); auto.
Qed.

Theorem rm_olist: forall l1 l2, olist l2 -> olist (rm l1 l2).
intros l1; elim l1; simpl; auto; clear l1.
intros a l1 Rec l2; case l2; simpl; auto; clear l2.
intros b l2 H; case_eq (weight a b); intros H1; auto.
apply Rec; auto.
apply olist_inv with (1 := H); auto.
generalize b H H1; elim l2; simpl; auto; clear b l2 H H1.
intros b l2 Rec1 c H H1.
case_eq (weight a b); intros H2; auto.
apply rm_olist_strong; auto.
apply rm_olist_strong; auto.
apply olist_skip with (1 := H); auto.
apply olist_cons; auto.
apply olist_weight with (1 := H); auto with datatypes.
apply Rec1; auto.
apply olist_inv with (1 := H); auto.
Qed.

(** Lifting the order to a lexico on list *)

(* Lexico on list  *)
Fixpoint lexico (l1 l2: list A) {struct l1}: cmp :=
  match l1 with
    nil => match l2 with nil => eq | _ => lt end
  | a:: l3 =>
     match l2 with 
       nil => gt 
     | b :: l4 =>
        match weight a b with
          eq => lexico l3 l4
        | X => X
        end
     end
   end.

Theorem lexico_trans: 
  forall a b c, lexico a b = lexico b c -> lexico a c = lexico a b.
intros a; elim a; simpl; auto; clear a.
intros b; case b; auto; clear b.
intros x b c; case c; clear c; simpl; auto. 
intros; discriminate.
intros x a Rec; intros b c; case c; case b; clear b c; simpl; 
 try (intros; discriminate; fail); auto.
intros y b z c.
case_eq (weight x y); auto; intros H1.
case_eq (weight y z); auto; intros H2.
rewrite (weight_trans x y z); rewrite H1; auto.
rewrite <- (weight_compat_r y z x); auto.
rewrite H1; auto.
intros; discriminate.
rewrite (weight_compat_l x y z); auto.
case_eq (weight y z); auto; intros H2.
case_eq (weight y z); auto; intros H2.
intros; discriminate.
rewrite <- (weight_compat_r y z x); auto.
rewrite H1; auto.
rewrite (weight_trans x y z); auto.
rewrite H1; auto.
rewrite H1; auto.
Qed.

Theorem lexico_anti_sym: 
  forall a b, lexico b a = opp (lexico a b).
intros a; elim a; clear a; simpl; auto.
intros b; case b; clear b; simpl; auto.
intros x a Rec b; case b; clear b; simpl; auto.
intros y b; rewrite (weight_anti_sym x y).
case (weight x y); simpl; auto.
Qed.

(* No collision *)
Theorem lexico_exact: 
  forall a b, lexico a b = eq -> a = b.
intros a; elim a; simpl; auto; clear a.
intros b; case b; auto.
intros; discriminate.
intros x a Rec b; case b; auto; clear b.
intros; discriminate.
intros y b.
generalize (weight_exact x y).
case (weight x y); auto.
intros; discriminate.
intros; eq_tac; auto.
intros; discriminate.
Qed.

End ordered.


(* Computable equality test *)
Definition eq_nat: forall x y: nat, {x = y} + {x <> y}.
fix 2; intros x y; case x; case y.
left; auto.
intros y1; right; intros; discriminate.
intros x1; right; intros; discriminate.
intros y1 x1; case (eq_nat x1 y1); intros H.
left; auto.
right; contradict H; injection H; auto.
Defined.

(* Comparison for integers *)
Fixpoint test (n m: nat) {struct n}: cmp :=
  match n with 
       O => match m with O => eq | _ => lt end
  | S n1 => match m with O => gt | S m1 => test n1 m1 end
  end.

Theorem test_trans: forall n1 n2 n3,
  test n1 n2 = test n2 n3 -> test n1 n3 = test n1 n2.
intros n1; elim n1; simpl; auto; clear n1.
intros n2; elim n2; simpl; auto; clear n2.
intros n2 Rec n3; elim n3; simpl; auto; clear n3.
intros; discriminate.
intros n1 Rec n2; elim n2; clear n2; simpl; auto.
intros n3; elim n3; simpl; auto; clear n3.
intros; discriminate.
intros n2 Rec1 n3; elim n3; simpl; auto; clear n3.
Qed.

Theorem test_anti_sym: forall n1 n2, test n1 n2 = opp (test n2 n1).
intros n1; elim n1; simpl; auto; clear n1.
intros n2; elim n2; simpl; auto; clear n2.
intros n1 Rec n2; elim n2; simpl; auto; clear n2.
Qed.

Theorem test_exact: forall n1 n2, test n1 n2 = eq -> n1 = n2.
intros n1; elim n1; simpl; auto; clear n1.
intros n2; elim n2; simpl; auto; clear n2.
intros; discriminate.
intros n1 Rec n2; elim n2; simpl; auto; clear n2.
intros; discriminate.
Qed.

Theorem test_compat_l: 
  forall a b c, test a b = eq -> test a c = test b c.
intros a; elim a; simpl; auto; clear a.
intros b; case b; try (intros; discriminate; fail).
intros c; case c; auto.
intros a Rec b; case b; clear b.
intros; discriminate.
intros b c Hb; case c; simpl; auto.
Qed.