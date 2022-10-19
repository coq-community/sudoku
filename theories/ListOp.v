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
(*            ListOp:                                   *)
(* Create the operations take, jump, take_and_jump      *)
(* these operations are used to represent rows columns  *)
(* and sub rectangles                                   *)
(*                               thery@sophia.inria.fr  *)
(*                                      (2006)          *)
(********************************************************)
Require Import List.
Require Import ListAux.
Require Import UList.
Require Import OrderedList.

Section list_op.

Variable A: Set.
Variable o: A.

(* Take the first n elements of l *)
Definition take n (l : list A) := firstn n l.
Hint Unfold take : core.

(* Taking for an empty list gives an empty list *)
Theorem take_nil: forall n, take n nil = nil.
Proof.
  apply firstn_nil.
Qed.

Theorem take_nth: forall i j r l,
    i < j \/ length l <= i -> nth i (take j l) r = nth i l r.
Proof.
intros i j r l; generalize i j r; elim l; simpl; auto with arith;
  clear i j r l.
intros i j r; case i; auto; intros; rewrite take_nil; auto.
intros a l Rec i j r; case i.
case j; auto.
intros [HH | HH]; contradict HH; auto with arith.
intros n; case j; simpl; auto with arith.
intros [HH | HH].
contradict HH; auto with arith.
apply sym_equal; apply nth_default; auto with arith.
intros n1 HH; apply Rec; case HH; auto with arith.
Qed.

Theorem length_take: forall i l, i <= length l -> length (take i l) = i.
intros i l; generalize i; elim l; clear i l; simpl; auto.
intros i; case i; auto.
intros i1 HH; contradict HH; auto with arith.
intros a l Rec i; case i; simpl; auto with arith.
Qed.

Theorem length_take_small: forall i l, length l <= i -> length (take i l) = length l.
intros i l; generalize i; elim l; clear i l; simpl; auto.
intros; rewrite take_nil; auto.
intros a l Rec i; case i; simpl; auto with arith.
Qed.

Theorem length_take1: forall i s,
    i <= length s -> length (take i s) = i.
Proof.
  intros i s H.
  apply firstn_length_le; auto.
Qed.

(* Jump the first n elements of l *)
Definition jump (n: nat) (l: list A) := skipn n l.
Hint Unfold jump : core.

(* A jump on an empty list is an empty list *)
Theorem jump_nil: forall n, jump n nil = nil.
Proof.
  apply skipn_nil.
Qed.

(* the relation between jump and nth *)
Theorem jump_nth:
  forall l k r, nth k l r = nth 0 (jump k l) r.
intros l; elim l; simpl; auto.
intros k r; rewrite jump_nil; simpl; case k; auto.
intros a l1 Rec k r; case k; simpl; auto.
Qed.

(* If we jump too far we get nil *)
Theorem jump_too_far: forall i l, length l <= i -> jump i l = nil.
intros i l; generalize i; elim l; simpl; auto; clear i l.
intros; apply jump_nil.
intros a l Rec i; case i; simpl; auto with arith.
intros H; contradict H; auto with arith.
Qed.

(* Jump is additive *)
Theorem jump_add: forall a b l, jump (a + b) l = jump b (jump a l).
Proof.
  intros a.
  induction a; auto; intros b l.
  - destruct l; simpl.
    + rewrite jump_nil. reflexivity.
    + apply IHa.
Qed.

Theorem length_jump: forall i s,
    i <= length s -> length s = length (jump i s) + i.
Proof.
  intros i.
  induction i; auto; intros s H; simpl.
  - destruct s.
    + inversion H.
    + simpl. rewrite <- plus_n_Sm; auto with arith.
Qed.

(* Take from l t elements and then jump j elements n times *)
Fixpoint take_and_jump (t j n: nat) (l: list A) {struct n}: list A :=
   match n with
        0 => nil
   | S n1 =>  take t l ++ take_and_jump t j n1 (jump j l)
   end.

(* Taking and jumping on an empty list is an empty list *)
Theorem take_and_jump_nil: forall a b c,
  take_and_jump a b c nil = nil.
intros a b c; elim c; simpl; auto.
intros n H; rewrite jump_nil, take_nil, H; auto with arith.
Qed.

Theorem length_take_and_jump: forall i j (k: nat) s,
  (if k then 0 else i) + pred k * j <= length s -> length (take_and_jump i j k s) = k * i.
intros i j k; generalize i j; elim k; simpl; auto; clear i j k.
intros k Rec i j s H; rewrite app_length, length_take1;
  auto with arith.
f_equal; auto.
apply Rec.
generalize H; case k; clear k H Rec.
intros; simpl; auto with arith.
intros k H; simpl pred.
apply Nat.add_le_mono_l with j.
rewrite (fun x (y: list A) => Nat.add_comm x (length y)).
rewrite <- length_jump; auto with arith.
rewrite Nat.add_shuffle3; auto.
apply Nat.le_trans with (2 := H); auto with arith.
pattern j at 1; replace j with (0 + (j + 0)); auto with arith.
apply Nat.add_le_mono; simpl; auto with arith.
simpl; auto with arith.
apply Nat.le_trans with (2 := H); auto with arith.
Qed.

(* Replace the n th element of the list l with the value v *)
Fixpoint subst (n: nat) (v: A) (l: list A) {struct n} : list A :=
  match l with
    nil => nil
  | a :: l1 => match n with O => v :: l1 | S n1 => a :: subst n1 v l1 end
  end.

(*  Subst does not change the length of a list *)
Theorem length_subst: forall n v l, length (subst n v l) = length l.
intros n; elim n; simpl; auto.
intros v l; case l; simpl; auto.
intros n1 Rec v l; case l; simpl; auto.
Qed.


(* Create a list of o of length n *)
Fixpoint mk_0 (n: nat): list A :=
  match n with O => nil | S n1 => o :: mk_0 n1 end.

Theorem mk_0_length : forall n, length (mk_0 n) = n.
intros n; elim n; simpl; auto.
Qed.

(* Replace all the element after the index n in the list l by o *)
Fixpoint restrict (n: nat) (l: list A) {struct l}: list A :=
  match l with
    nil => nil
  | a :: l1 =>
    match n with
      O => o :: (restrict n l1)
   | S n1 => a :: (restrict n1 l1)
   end
  end.

Theorem restrict_0: forall l, restrict 0 l = mk_0 (length l).
intros l;  elim l; simpl; auto with datatypes.
intros; f_equal; auto.
Qed.

Theorem restrict_all: forall n l, length l <= n -> restrict n l = l.
intros n l; generalize n; elim l; simpl; auto with datatypes; clear n l.
intros a l Rec n; case n; auto with arith.
intros H; contradict H; auto with arith.
intros n1 H; f_equal; auto with arith.
Qed.

Theorem restrict_length: forall n l, length (restrict n l) = (length l).
intros n l; generalize n; elim l; simpl; auto with datatypes; clear n l.
intros a l Rec n; case n; simpl; auto.
Qed.

Theorem restrict_update: forall n l, S n <= length l ->
  restrict (S n) l = subst n (nth 0 (jump n l) o) (restrict n l).
intros n l; generalize n; elim l; auto with datatypes; clear n l.
intros n H; contradict H; auto with arith.
intros a l1 Rec n; case n; auto; clear n.
simpl length; intros n H; simpl; f_equal; auto with arith.
Qed.

Theorem restrict_nth: forall l n m, n < m ->
  nth n (restrict m l) o = nth n l o.
intros l; elim l; simpl; auto; clear l.
intros a l Rec n m; case m; auto; clear m.
intros H; contradict H; auto with arith.
intros m; case n; clear n; auto.
intros n; simpl; auto with arith.
Qed.


Theorem restrict_nth_default: forall l n m, m <= n ->
  nth n (restrict m l) o = o.
intros l; elim l; simpl; auto; clear l.
intros n m; case n; auto with arith.
intros a l Rec n m; case m; auto; clear m.
rewrite restrict_0.
case n; simpl; auto.
intros n1 _; generalize n1; elim (length l); clear n1; simpl; auto.
intros n1; case n1; auto.
intros n2 Rec1 n1; case n1; simpl; auto.
intros n2; case n; simpl; auto with arith.
intros H; contradict H; auto with arith.
Qed.

End list_op.

Arguments jump [A].
Arguments take [A].
Arguments take_and_jump [A].
Arguments subst [A].
Arguments restrict [A].
Arguments mk_0 [A].

(* Build the list [m; m+1; ...; m+n] *)
Fixpoint progression (n m: nat) {struct n}: list nat :=
  match n with O => nil | S n1 => m :: progression n1 (S m) end.

(* A progression is a unique list *)
Theorem  progression_list: forall n m, ulist (progression n m).
assert (E1: forall n m p , In p (progression n m) -> m <= p).
intros n; elim n; simpl; auto with datatypes; clear n.
intros m p H; case H.
intros n Rec m p [H | H]; subst; auto with arith.
apply Nat.le_trans with (S m); auto with arith.
intros n; elim n; simpl; clear n; auto.
intros n Rec m; apply ulist_cons; auto.
intros H; generalize (E1 _ _ _ H); auto with arith.
intros H1; contradict H1; auto with arith.
Qed.

(* Define the element of a progression *)
Theorem in_progression: forall n a i,
  In i (progression n a) <-> a <= i < n + a.
intros n; elim n; simpl; auto.
intros a i; split; try (intros H; case H; fail);
 intros (H1, H2); contradict H1; auto with arith.
intros n1 Rec a i; case (Rec (S a) i); clear Rec; intros H1 H2.
split; intros H.
case H; intros H3; subst; auto with arith.
case H1; try rewrite plus_n_Sm; auto with arith.
case H; intros H3 H4.
case le_lt_eq_dec with (1 := H3); auto with arith.
rewrite plus_n_Sm in H4; auto with arith.
Qed.

Fixpoint list_nat_eq (l1 l2: list nat) {struct l1}: bool :=
  match l1, l2 with nil, nil => true
  | n1::l3, n2::l4 =>
      if Nat.eqb n1 n2 then list_nat_eq l3 l4 else false
  | _, _ => false
  end.

Lemma list_nat_eq_correct l1 l2 :
  if list_nat_eq l1 l2 then l1 = l2 else l1 <> l2.
Proof.
revert l2.
induction l1 as [| n1 l1 Hrec]; destruct l2 as [| n2 l2]; simpl;
  try (intros; discriminate); auto.
destruct (Nat.eqb_spec n1 n2) as [n1En2|H1].
  generalize (Hrec l2); case list_nat_eq; intros H2.
    apply f_equal2 with (f := @cons _); auto.
  intros HH; case H2; injection HH; auto.
intros HH; case H1; injection HH; auto.
Qed.
