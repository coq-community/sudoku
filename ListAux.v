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
(*     Aux.v                                                                  *)
(*                                                                            *)
(*    Auxillary functions & theorems for lists                                *)
(*                                                                            *)
(*                                   Laurent.Thery@inria.fr (2006)            *)
(******************************************************************************)
Require Export List.
Require Export Arith.
Require Export Tactic.
Require Import Inverse_Image.
Require Import Wf_nat.

(******************************************************************************)
(*  Some properties on list operators: app, map,...                           *)
(******************************************************************************)
 
Section List.
Variables (A : Set) (B : Set) (C : Set).
Variable f : A ->  B.

(******************************************************************************)
(* An induction theorem for list based on length                              *)
(******************************************************************************)
 
Theorem list_length_ind:
 forall (P : list A ->  Prop),
 (forall (l1 : list A),
  (forall (l2 : list A), length l2 < length l1 ->  P l2) ->  P l1) ->
 forall (l : list A),  P l.
Proof.
  intros P H l;
  apply well_founded_ind with (R := fun (x y : list A) => length x < length y);
  auto.
  apply wf_inverse_image with (R := lt); auto.
  apply lt_wf.
Qed.
 
Definition list_length_induction:
 forall (P : list A ->  Set),
 (forall (l1 : list A),
  (forall (l2 : list A), length l2 < length l1 ->  P l2) ->  P l1) ->
 forall (l : list A),  P l.
Proof.
  intros P H l;
  apply well_founded_induction
        with (R := fun (x y : list A) => length x < length y); auto.
  apply wf_inverse_image with (R := lt); auto.
  apply lt_wf.
Qed.
 
Theorem in_ex_app:
 forall (a : A) (l : list A),
 In a l ->  (exists l1 : list A , exists l2 : list A , l = l1 ++ (a :: l2)).
Proof.
  intros a l; elim l; clear l; simpl; auto.
  intros H; case H.
  intros a1 l H [H1|H1]; auto.
  exists (nil (A:=A)); exists l; simpl; auto.
  eq_tac; auto.
  case H; auto; intros l1 [l2 Hl2]; exists (a1 :: l1); exists l2; simpl; auto.
  eq_tac; auto.
Qed.

(******************************************************************************)
(* Properties of nth                                                          *)
(******************************************************************************)

Theorem nth_nil: forall n (a: A), nth n nil a = a.
Proof.
  intros n; elim n; simpl; auto.
Qed.

Theorem in_ex_nth: forall (a b: A) l,
    In a l <-> exists n, n < length l /\ a = nth n l b.
Proof.
  intros a b l.
  split; intros H.
  - pose proof (In_nth l a b H).
    destruct H0 as [n [H1 H2]].
    exists n; auto.
  - destruct H as [n [H1 H2]].
    pose proof (nth_In _ b H1); subst; auto.
Qed.


Theorem nth_app_l: forall i r (l1 l2: list A),
   i < length l1 -> nth i (l1 ++ l2) r = nth i l1 r.
Proof.
  intros; apply app_nth1; auto.
Qed.

Theorem nth_app_r: forall i r (l1 l2: list A),
   length l1 <= i -> nth i (l1 ++ l2) r = nth (i - length l1) l2 r.
Proof.
  intros; apply app_nth2; auto.
Qed.

Theorem nth_default: forall i r (l: list A), length l <= i -> nth i l r = r.
Proof.
  intros; apply nth_overflow; auto.
Qed.

Theorem list_nth_eq: forall (r: A) l1 l2, 
  length l1 = length l2 ->
  (forall n, nth n l1 r = nth n l2 r) -> l1 = l2.
Proof.
  intros; eapply nth_ext; auto.
Qed.

(******************************************************************************)
(* Properties on app                                                          *)
(******************************************************************************)
 
Theorem length_app:
  forall (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2.
Proof.
  apply app_length.
Qed.
 
Theorem app_inv_app:
 forall l1 l2 l3 l4 a,
 l1 ++ l2 = l3 ++ (a :: l4) ->
  (exists l5 : list A , l1 = l3 ++ (a :: l5) ) \/
  (exists l5 , l2 = l5 ++ (a :: l4) ).
Proof.
  intros l1; elim l1; simpl; auto.
  intros l2 l3 l4 a H; right; exists l3; auto.
  intros a l H l2 l3 l4 a0; case l3; simpl.
  intros H0; left; exists l; eq_tac; injection H0; auto.
  intros b l0 H0; case (H l2 l0 l4 a0); auto.
  injection H0; auto.
  intros [l5 H1].
  left; exists l5; eq_tac; injection H0; auto.
Qed.
 
Theorem app_inv_app2:
 forall l1 l2 l3 l4 a b,
 l1 ++ l2 = l3 ++ (a :: (b :: l4)) ->
  (exists l5 : list A , l1 = l3 ++ (a :: (b :: l5)) ) \/
  ((exists l5 , l2 = l5 ++ (a :: (b :: l4)) ) \/
   l1 = l3 ++ (a :: nil) /\ l2 = b :: l4).
Proof.
  intros l1; elim l1; simpl; auto.
  intros l2 l3 l4 a b H; right; left; exists l3; auto.
  intros a l H l2 l3 l4 a0 b; case l3; simpl.
  case l; simpl.
  intros H0; right; right; injection H0; split; auto.
  eq_tac; auto.
  intros b0 l0 H0; left; exists l0; injection H0; intros; (repeat eq_tac); auto.
  intros b0 l0 H0; case (H l2 l0 l4 a0 b); auto.
  injection H0; auto.
  intros [l5 HH1]; left; exists l5; eq_tac; auto; injection H0; auto.
  intros [H1|[H1 H2]]; auto.
  right; right; split; auto; eq_tac; auto; injection H0; auto.
Qed.
 
Theorem same_length_ex:
 forall (a : A) l1 l2 l3,
 length (l1 ++ (a :: l2)) = length l3 ->
  (exists l4 ,
   exists l5 ,
   exists b : B ,
   length l1 = length l4 /\ (length l2 = length l5 /\ l3 = l4 ++ (b :: l5))).
Proof.
  intros a l1; elim l1; simpl; auto.
  intros l2 l3; case l3; simpl; (try (intros; discriminate)).
  intros b l H; exists (nil (A:=B)); exists l; exists b; (repeat (split; auto)).
  intros a0 l H l2 l3; case l3; simpl; (try (intros; discriminate)).
  intros b l0 H0.
  case (H l2 l0); auto.
  intros l4 [l5 [b1 [HH1 [HH2 HH3]]]].
  exists (b :: l4); exists l5; exists b1; (repeat (simpl; split; auto)).
  eq_tac; auto.
Qed.

(******************************************************************************)
(* Properties on map                                                          *)
(******************************************************************************)
 
Theorem in_map_inv:
 forall (b : B) (l : list A),
   In b (map f l) ->  (exists a : A , In a l /\ b = f a ).
Proof.
  intros b l H.
  rewrite in_map_iff in H.
  destruct H as [x [H1 H2]].
  eauto.
Qed.
 
Theorem in_map_fst_inv:
 forall a (l : list (B * C)),
 In a (map (fst (B:=_)) l) ->  (exists c , In (a, c) l ).
Proof.
  intros a l; elim l; simpl; auto.
  intros H; case H.
  intros a0 l0 H [H0|H0]; auto.
  exists (snd a0); left; rewrite <- H0; case a0; simpl; auto.
  case H; auto; intros l1 Hl1; exists l1; auto.
Qed.
 
Theorem length_map: forall l,  length (map f l) = length l.
Proof.
  apply map_length.
Qed.
 
Theorem map_length_decompose:
 forall l1 l2 l3 l4,
 length l1 = length l2 ->
 map f (app l1 l3) = app l2 l4 ->  map f l1 = l2 /\ map f l3 = l4.
Proof.
  intros l1; elim l1; simpl; auto; clear l1.
  intros l2; case l2; simpl; auto.
  intros; discriminate.
  intros a l1 Rec l2; case l2; simpl; clear l2; auto.
  intros; discriminate.
  intros b l2 l3 l4 H1 H2.
  injection H2; clear H2; intros H2 H3.
  case (Rec l2 l3 l4); auto.
  intros H4 H5; split; auto.
  eq_tac; auto.
Qed.

(******************************************************************************)
(* Properties of flat_map                                                     *)
(******************************************************************************)
 
Theorem in_flat_map:
 forall (l : list B) (f : B ->  list C) a b,
 In a (f b) -> In b l ->  In a (flat_map f l).
Proof.
  intros l g; elim l; simpl; auto.
  intros a l0 H a0 b H0 [H1|H1]; apply in_or_app; auto.
  left; rewrite H1; auto.
  right; apply H with ( b := b ); auto.
Qed.
 
Theorem in_flat_map_ex:
 forall (l : list B) (f : B ->  list C) a,
 In a (flat_map f l) ->  (exists b , In b l /\ In a (f b) ).
Proof.
  intros l g; elim l; simpl; auto.
  intros a H; case H.
  intros a l0 H a0 H0; case in_app_or with ( 1 := H0 ); simpl; auto.
  intros H1; exists a; auto.
  intros H1; case H with ( 1 := H1 ).
  intros b [H2 H3]; exists b; simpl; auto.
Qed.
 
End List.


(******************************************************************************)
(* Propertie of list_prod                                                     *)
(******************************************************************************)
 
Theorem length_list_prod:
 forall (A : Set) (l1 l2 : list A),
  length (list_prod l1 l2) = length l1 * length l2.
Proof.
  intros A l1 l2; elim l1; simpl; auto.
  intros a l H; rewrite length_app; rewrite length_map; rewrite H; auto.
Qed.
 
Theorem in_list_prod_inv:
 forall (A B : Set) a l1 l2,
 In a (list_prod l1 l2) ->
  (exists b : A , exists c : B , a = (b, c) /\ (In b l1 /\ In c l2)  ).
Proof.
  intros A B a l1 l2; elim l1; simpl; auto; clear l1.
  intros H; case H.
  intros a1 l1 H1 H2.
  case in_app_or with ( 1 := H2 ); intros H3; auto.
  case in_map_inv with ( 1 := H3 ); intros b1 [Hb1 Hb2]; auto.
  exists a1; exists b1; split; auto.
  case H1; auto; intros b1 [c1 [Hb1 [Hb2 Hb3]]].
  exists b1; exists c1; split; auto.
Qed.

Definition In_dec:
forall {A : Set},
       (forall x y : A, {x = y} + {x <> y}) ->
       forall (a : A) (l : list A), {In a l} + {~ In a l}.
Proof.
  intros A H a l.
  apply in_dec; auto.
Defined.

Theorem in_fold_map: forall (A: Set) (f: nat -> nat -> A) p l1 l2,
  In p
    (fold_right
       (fun x l =>
          map (f x) l1 ++ l) nil l2) <->
    (exists x, (exists y , In x l2 /\ In y l1 /\ p = f x y)).
Proof.
  intros A f p l1 l2; elim l2; simpl; auto; clear l2.
  split; auto.
  intros H; case H.
  intros (x, (y, (H, _))); auto.
  intros a l2 (Rec1, Rec2); split; intros H.
  case in_app_or with (1 := H); clear H; intros H.
  case (in_map_inv _ _ (f a) p l1); auto.
  intros y (H1, H2).
  exists a; exists y; repeat split; auto.
  case Rec1; auto; clear Rec1 Rec2.
  intros x (y, (U1, (U2, U3))); exists x; exists y; repeat split;
    auto with arith.
  case H; intros x (y, ([U1 | U1], (U2, U3))); subst; auto; clear H.
  apply in_or_app; left; auto.
  apply in_map; auto.
  apply in_or_app; right; auto.
  apply Rec2; auto; clear Rec1 Rec2.
  exists x; exists y; repeat split; auto with arith.
Qed.
