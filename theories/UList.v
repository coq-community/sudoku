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
      UList.v

      Definition of list with distinct elements

      Definition: ulist

                                     Laurent.Thery@inria.fr (2006)
************************************************************************)
Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import ListSet.

Section UniqueList.
Variable A : Set.
Variable eqA_dec : forall (a b : A),  ({ a = b }) + ({ a <> b }).
(* A list is unique if there is not twice the same element in the list *)

Definition ulist (l1 : list A) := NoDup l1.
Definition ulist_nil := NoDup_nil.
Definition ulist_cons a l (H : ~ In a l) (H1 : ulist l) := NoDup_cons a H H1.
Hint Unfold ulist : core.
Hint Constructors NoDup : core.

(* Inversion theorem *)

Theorem ulist_inv: forall a l, ulist (a :: l) ->  ulist l.
  intros a l H; inversion H; auto.
Qed.
(* The append of two unique list is unique if the list are distinct *)

Theorem ulist_app:
  forall l1 l2,
    ulist l1 ->
    ulist l2 -> (forall (a : A), In a l1 -> In a l2 ->  False) ->  ulist (l1 ++ l2).
  intros L1; elim L1; simpl; auto.
  intros a l H l2 H0 H1 H2; apply NoDup_cons; simpl; auto.
  red; intros H3; case in_app_or with ( 1 := H3 ); auto; intros H4.
  inversion H0; auto.
  apply H2 with a; auto.
  apply H; auto.
  apply ulist_inv with ( 1 := H0 ); auto.
  intros a0 H3 H4; apply (H2 a0); auto.
Qed.
(* Iinversion theorem the appended list *)

Theorem ulist_app_inv:
  forall l1 l2 (a : A), ulist (l1 ++ l2) -> In a l1 -> In a l2 ->  False.
  intros l1; elim l1; simpl; auto.
  intros a l H l2 a0 H0 [H1|H1] H2.
  inversion H0 as [|a1 l0 H3 H4 H5]; auto.
  case H3; rewrite H1; auto with datatypes.
  apply (H l2 a0); auto.
  apply ulist_inv with ( 1 := H0 ); auto.
Qed.
(* Iinversion theorem the appended list *)

Theorem ulist_app_inv_l: forall (l1 l2 : list A), ulist (l1 ++ l2) ->  ulist l1.
Proof.
  intros l1 l2.
  generalize dependent l1.
  induction l2; intros l1 H.
  - rewrite app_nil_r in H. assumption.
  - apply NoDup_remove_1 in H; auto.
Qed.
(* Iinversion theorem the appended list *)

Theorem ulist_app_inv_r: forall (l1 l2 : list A), ulist (l1 ++ l2) ->  ulist l2.
  intros l1; elim l1; simpl; auto.
  intros a l H l2 H0; inversion H0; auto.
Qed.
(* Uniqueness is decidable *)

Definition ulist_dec: forall l,  ({ ulist l }) + ({ ~ ulist l }).
Proof.
  apply ListDec.NoDup_dec; auto.
Defined.
(* Uniqueness is compatible with permutation *)

Theorem ulist_perm:
  forall (l1 l2 : list A), Permutation l1 l2 -> ulist l1 ->  ulist l2.
Proof.
  apply Permutation_NoDup.
Qed.

Theorem ulist_def:
  forall l a,
    In a l -> ulist l ->  ~ (exists l1 , Permutation l (a :: (a :: l1)) ).
  intros l a H H0 [l1 H1].
  absurd (ulist (a :: (a :: l1))); auto.
  intros H2; inversion_clear H2; simpl; auto with datatypes.
  apply ulist_perm with ( 1 := H1 ); auto.
Qed.

Theorem ulist_incl_permutation:
  forall (l1 l2 : list A),
    ulist l1 -> incl l1 l2 ->  (exists l3 , Permutation l2 (l1 ++ l3) ).
Proof with auto with datatypes.
  intros l1; elim l1; simpl...
  intros l2 H H0; exists l2; simpl...
  intros a l H l2 H0 H1...
  case (in_permutation_ex _ a l2)...
  intros l3 Hl3.
  case (H l3)...
  apply ulist_inv with ( 1 := H0 )...
  intros b Hb.
  assert (H2: In b (a :: l3)).
  apply Permutation_in with ( 1 := Permutation_sym Hl3 )...
  simpl in H2 |-; case H2; intros H3; simpl...
  inversion_clear H0 as [|c lc Hk1]...
  case Hk1; subst a...
  intros l4 H4; exists l4.
  apply perm_trans with (a :: l3)...
  apply Permutation_sym...
Qed.

Theorem ulist_eq_permutation:
  forall (l1 l2 : list A),
    ulist l1 -> incl l1 l2 -> length l1 = length l2 ->  Permutation l1 l2.
Proof with auto with arith.
  intros l1 l2 H1 H2 H3.
  case (ulist_incl_permutation l1 l2)...
  intros l3 H4.
  assert (H5: l3 = @nil A).
  generalize (Permutation_length H4); rewrite app_length, H3.
  rewrite Nat.add_comm; case l3; simpl...
  intros a l H5; absurd (lt (length l2) (length l2))...
  pattern (length l2) at 2; rewrite H5...
  replace l1 with (app l1 l3)...
  apply Permutation_sym...
  rewrite H5, app_nil_end...
Qed.


Theorem ulist_incl_length:
  forall (l1 l2 : list A), ulist l1 -> incl l1 l2 ->  le (length l1) (length l2).
  intros l1 l2 H1 Hi; case ulist_incl_permutation with ( 2 := Hi ); auto.
  intros l3 Hl3; rewrite Permutation_length with ( 1 := Hl3 ); auto.
  rewrite app_length; simpl; auto with arith.
Qed.

Theorem ulist_incl2_permutation:
  forall (l1 l2 : list A),
    ulist l1 -> ulist l2 -> incl l1 l2 -> incl l2 l1  ->  Permutation l1 l2.
  intros l1 l2 H1 H2 H3 H4.
  apply ulist_eq_permutation; auto.
  apply Nat.le_antisymm; apply ulist_incl_length; auto.
Qed.


Theorem ulist_incl_length_strict:
  forall (l1 l2 : list A),
    ulist l1 -> incl l1 l2 -> ~ incl l2 l1 ->  lt (length l1) (length l2).
Proof with auto with arith.
  intros l1 l2 H1 Hi Hi0; case ulist_incl_permutation with ( 2 := Hi )...
  intros l3 Hl3; rewrite Permutation_length with ( 1 := Hl3 )...
  rewrite app_length; simpl...
  generalize Hl3; case l3; simpl...
  rewrite <- app_nil_end...
  intros H2; case Hi0...
  intros a HH; apply Permutation_in with ( 1 := H2 )...
  intros a l Hl0; (rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; auto with arith).
Qed.

Theorem in_inv_dec:
  forall (a b : A) l, In a (cons b l) ->  a = b \/ ~ a = b /\ In a l.
  intros a b l H; case (eqA_dec a b); auto; intros H1.
  right; split; auto; inversion H; auto.
  case H1; auto.
Qed.

Theorem in_ex_app_first:
  forall (a : A) (l : list A),
    In a l ->
    (exists l1 : list A , exists l2 : list A , l = l1 ++ (a :: l2) /\ ~ In a l1  ).
  intros a l; elim l; clear l; auto.
  intros H; case H.
  intros a1 l H H1; auto.
  generalize (in_inv_dec _ _ _ H1); intros [H2|[H2 H3]].
  exists (nil (A:=A)); exists l; simpl; split; auto.
  f_equal; auto.
  case H; auto; intros l1 [l2 [Hl2 Hl3]]; exists (a1 :: l1); exists l2; simpl;
    split; auto.
  f_equal; auto.
  intros H4; case H4; auto.
Qed.

Theorem nth_ulist: forall a i j (l: list A), i < length l -> j < length l ->
                                        ulist l -> nth i l a = nth j l a -> i = j.
  intros a i j l; generalize i j; elim l; simpl; clear l i j.
  intros i j H; contradict H; auto with arith.
  intros b l1 Rec i j; case i; case j; auto with arith; clear i j.
  intros j _ H1 H2 H3; absurd (In b l1); auto.
  inversion H2; auto.
  subst; apply nth_In; auto with arith.
  intros i H1 _ H2 H3; absurd (In b l1); auto.
  inversion H2; auto.
  subst; apply nth_In; auto with arith.
  intros j i H1 H2 H3 H4; inversion H3; auto with arith.
Qed.

End UniqueList.

Arguments ulist [A].
Global Hint Unfold ulist : core.
Global Hint Constructors NoDup : core.

Theorem ulist_map:
  forall (A B : Set) (f : A ->  B) l,
    (forall x y, (In x l) -> (In y l) ->  f x = f y ->  x = y) -> ulist l ->  ulist (map f l).
Proof.
  intros a b f l Hf Hl; generalize Hf; elim Hl; clear Hf;  auto.
  simpl; auto.
  intros a1 l1 H1 H2 H3 Hf; simpl.
  apply ulist_cons; auto with datatypes.
  contradict H1.
  case in_map_inv with ( 1 := H1 ); auto.
  intros b1 [Hb1 Hb2].
  replace a1 with b1; auto with datatypes.
Qed.

Theorem ulist_list_prod:
  forall (A : Set) (l1 l2 : list A),
    ulist l1 -> ulist l2 ->  ulist (list_prod l1 l2).
Proof with auto.
  intros A l1 l2 Hl1 Hl2; elim Hl1; simpl...
  intros a l H1 H2 H3; apply ulist_app...
  apply ulist_map...
  intros x y _ _ H; inversion H...
  intros p Hp1 Hp2; case H1.
  case in_map_inv with ( 1 := Hp1 ); intros a1 [Ha1 Ha2]...
  case in_list_prod_inv with ( 1 := Hp2 ); intros b1 [c1 [Hb1 [Hb2 Hb3]]]...
  replace a with b1...
  rewrite Ha2 in Hb1; injection Hb1...
Qed.
