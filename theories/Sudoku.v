(* This program is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public License         *)
(* as published by the Free Software Foundation; either version 2.1           *)
(* of the License, or (at your option) any later version.                     *)
(*                                                                            *)
(* This program is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *)
(* GNU General Public License for more details.                               *)
(*                                                                            *)
(* You should have received a copy of the GNU Lesser General Public           *)
(* License along with this program; if not, write to the Free                 *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA         *)
(* 02110-1301 USA                                                             *)


(******************************************************************************)
(*            Sudoku.v:                                                       *)
(*     Checking and Solving Sudokus                                           *)
(*                               thery@sophia.inria.fr                        *)
(*     Definitions:                                                           *)
(*      sudoku, check, find_one, find_all                                     *)
(*                                      (2006)                                *)
(******************************************************************************)

Require Export List.
Require Import UList.
Require Import Permutation.
Require Import Div.
Require Import OrderedList.
Require Import ListOp.
Require Import Lia.

Section check.

(******************************************************************************)
(* About the encoding:                                                        *)
(*  h represents the number of rows of a little rectangle                     *)
(*  w represents the number of columns of a little rectangle                  *)
(*  size represents the number of cells of a little rectangle                 *)
(* the initial grid is then composed of (size * size) cells                   *)
(* For example for the usual sudoku                                           *)
(*   h = 3, w = 3, size = 9, the grid = 81 cells                              *)
(* The grid is represented by a list of (size * size) cells                   *)
(* at the position (x,y) of the list (i.e at the index (x * size + y))        *)
(* if the cell is empty it contains 0, otherwise its contains one of          *)
(* the numbers 1,2, ..., size                                                 *)
(******************************************************************************)

(* Height h and width w *)
Variable h w: nat.

(* Size *)
Definition size := h * w.

Theorem h_pos x : x < size -> 0 < h.
Proof. cbv; destruct h; lia. Qed.

Theorem w_pos x : x < size -> 0 < w.
Proof. unfold size; destruct w; lia. Qed.

(* The reference list [1; 2; ...; size] *)
Definition ref_list := progression size 1.

Theorem ref_list_ulist : ulist ref_list.
Proof. apply progression_list. Qed.

Theorem ref_list_length: length ref_list = size.
Proof. unfold ref_list; generalize 1; induction size; simpl; auto. Qed.

(* The position indexes [0; 1; 2; ...; size -1] *)
Definition indexes := progression size 0.

(* Defines the indices *)
Theorem in_indexes i : In i indexes <-> i < size.
Proof.
unfold indexes.
destruct (in_progression size 0 i).
rewrite  Nat.add_0_r in H; split; intros; destruct H; auto with arith.
Qed.

(* An element outside the ref_list *)
Definition out := 0.

Theorem out_not_in_refl : ~ In out ref_list.
Proof.
unfold ref_list; intros H.
case (in_progression size 1 out).
intros tmp _; case (tmp H); auto; clear tmp.
intros H1; contradict H1; auto with arith.
Qed.

(* Empty grid (initial grid) *)
Definition init := mk_0 out (size * size).

(* Its length is size * size *)
Theorem length_init : length init = size * size.
Proof. unfold init; induction (size * size); simpl; auto. Qed.

(******************************************************************************)
(*    Positions (x, y)                                                        *)
(******************************************************************************)

(* Define a position *)
Inductive pos: Set := Pos: nat -> nat -> pos.

(* A comparison function for positions *)
Definition pos_test (p1 p2: pos) :=
  match p1 with Pos x1 y1 =>
    match p2 with Pos x2 y2 =>
      match test x1 x2 with
      | eq => test y1 y2
      | r  => r
      end
    end
  end.

(* pos_test is transitive *)
Theorem pos_test_trans p1 p2 p3 :
    pos_test p1 p2 = pos_test p2 p3 -> pos_test p1 p3 = pos_test p1 p2.
Proof.
case p1; case p2; case p3; simpl; auto.
intros x3 y3 x2 y2 x1 y1.
case_eq (test x1 x2); intros H.
- case_eq (test x2 x3); intros H1.
  + rewrite (test_trans x1 x2 x3); rewrite H; auto.
  + assert (x2 = x3); subst.
    * apply test_exact with (1 := H1); auto.
    * rewrite H; auto.
  + intros; discriminate.
- replace x1 with x2; auto.
  + case_eq (test x2 x3); intros H1; auto.
    intros; apply test_trans; auto.
  + apply sym_equal; apply test_exact with (1 := H); auto.
- case_eq (test x2 x3); intros H1.
  + intros; discriminate.
  + assert (x2 = x3); subst.
    * apply test_exact with (1 := H1); auto.
    * rewrite H; auto.
  + rewrite (test_trans x1 x2 x3); rewrite H; auto.
Qed.

(* pos_test is antisymetric *)
Theorem pos_test_anti_sym p1 p2 : pos_test p1 p2 = opp (pos_test p2 p1).
Proof.
case p1; case p2; simpl; auto.
intros x2 y2 x1 y1; rewrite (test_anti_sym x1 x2).
case (test x2 x1); simpl; auto.
apply test_anti_sym.
Qed.

(* pos_test lets us test equality *)
Theorem pos_test_exact p1 p2 : pos_test p1 p2 = eq -> p1 = p2.
Proof.
case p1; case p2; simpl; auto.
intros x2 y2 x1 y1; case_eq (test x1 x2); intros H; auto.
- intros; discriminate.
- intros H1; f_equal; apply test_exact; auto.
- intros; discriminate.
Qed.

Definition pos_dec (p1 p2 : pos) : {p1 = p2} + {p1 <> p2}.
apply (A_dec _ pos_test).
intros; apply pos_test_anti_sym; auto.
exact pos_test_exact.
Defined.

(* Shift a position *)
Definition shift p x y :=
  match p with Pos x1 y1 => Pos (x + x1) (y + y1) end.

(* A position is valid if it is inside the board *)
Definition valid_pos p := match p with Pos x y => x < size /\ y < size end.

(* Turn a position into a jump *)
Definition pos2n p := match p with Pos x y => x * size + y end.

(* Positions are unique *)
Theorem valid_pos_eq p1 p2 :
    valid_pos p1 -> valid_pos p2 -> pos2n p1 = pos2n p2 -> p1 = p2.
Proof.
destruct p1 as (x1, y1); destruct p2 as (x2, y2); simpl.
intros (H1, H2) (H3, H4) H5.
assert (x1 = x2); try f_equal; auto; try subst x2.
- apply lexico_mult with (3 := H5); auto.
- apply Nat.add_cancel_l with (1 := H5).
Qed.

(* Find the next position *)
Definition next p :=
  match p with 
  | Pos x y => if eq_nat (S y) size then Pos (S x) 0 else Pos x (S y)
  end.

Theorem next_pos p : pos2n (next p) = S (pos2n p).
Proof.
destruct p as (x, y); simpl; auto.
unfold pos2n.
case (eq_nat (S y) size); simpl; intros H1.
- rewrite <- H1.
  destruct (eq_nat y y); try lia.
- destruct size.
  + lia.
  + assert (y <> n) by lia.
    destruct (eq_nat y n); try lia.
Qed.

Theorem valid_pos_next p :
  valid_pos p -> pos2n (next p) < size * size -> valid_pos (next p).
Proof.
destruct p as (x, y).
destruct (eq_nat (S y) size); simpl.
- rewrite <- !e.
  intros H H0.
  all: destruct (eq_nat y y); simpl; try nia.
  simpl in *.
  nia.
- intros.
  destruct size eqn:E.
  + lia.
  + destruct (eq_nat y n0); try lia.
    simpl in *.
    lia.
Qed.

Theorem valid_pos2n p (s: list nat) : 
  valid_pos p -> length s = size * size -> pos2n p < length s.
Proof.
destruct p as (x, y); simpl; intros (H1, H2) H3; rewrite H3; clear H3.
apply mult_lt_plus; auto.
Qed.

(* Create the list of positions (x, y) such that 0 <= x < h and 0 <= y < w *)
Definition cross :=
  let p := progression h 0 in
  let q := progression w 0 in
  fold_right (fun x l => (map (fun y => (Pos x y)) q) ++ l) nil p.

Theorem cross_correct p :
    In p cross <-> exists x, exists y, x < h /\ y < w /\ p = Pos x y.
Proof.
case (in_fold_map _ (fun x y => Pos x y) p (progression w 0) (progression h 0)).
intros H1 H2; split; intros H3.
- case H1; auto.
  intros x (y, (U1, (U2, U3))).
  exists x; exists y; repeat split; auto.
  + case (in_progression h 0 x); auto with arith.
    rewrite  Nat.add_0_r; intros H _; case H; auto.
  + case (in_progression w 0 y); auto with arith.
    rewrite  Nat.add_0_r; intros H _; case H; auto.
- case H3; intros x (y, (U1, (U2, U3))); apply H2; clear H2 H3.
  exists x; exists y; repeat split; auto with arith.
  + case (in_progression h 0 x); auto with arith.
  + case (in_progression w 0 y); auto with arith.
Qed.

(* Create the list of pairs (x, y) such that 0 <= x < size and 1 <= y <= size *)
Definition cross1 :=
  let p := indexes in
  let q := ref_list in
  fold_right (fun x l => (map (fun y => (x, y)) q) ++ l) nil p.

Theorem cross1_correct p :
  In p cross1 <-> 
  exists x, exists y, In x indexes /\ In y ref_list /\ p = (x, y).
Proof. exact (in_fold_map _ (fun x y => (x, y)) p ref_list indexes). Qed.

(* Create the list of positions (x, y) such that                              *)
(*   0 <= x < size and 0 <= y < size1                                         *)
Definition cross2 :=
  let p := indexes in
  let q := indexes in
  fold_right (fun x l => (map (fun y => (Pos x y)) q) ++ l) nil p.

Theorem cross2_correct p : In p cross2 <-> valid_pos p.
Proof.
case (in_fold_map _ (fun x y => Pos x y) p indexes indexes).
intros H1 H2; split; intros H3.
- case H1; auto.
  intros x (y, (U1, (U2, U3))).
  rewrite U3; split; auto.
  + case (in_progression size 0 x); auto with arith.
    rewrite  Nat.add_0_r; intros H _; case H; auto.
  + case (in_progression size 0 y); auto with arith.
    rewrite  Nat.add_0_r; intros H _; case H; auto.
- apply H2; clear H1 H2.
  generalize H3; case p; clear p H3; intros x y (H3, H4).
  exists x; exists y; repeat split; auto with arith.
  + case (in_progression size 0 x); auto with arith.
  + case (in_progression size 0 y); auto with arith.
Qed.

(******************************************************************************)
(*    Get                                                                     *)
(******************************************************************************)

(* Get the element of the list l at position (x, y) *)
Definition get p l := nth 0 (jump (pos2n p) l) out.

(* Getting from a nil list always returns 0 *)
Theorem get_nil p : get p nil = out.
Proof. unfold get; rewrite jump_nil; auto. Qed.

(* Relation between get and next *)
Theorem get_next p a s : get (next p) (a :: s) = get p s.
Proof.
induction p.
- simpl.
  destruct (eq_nat (S n0) size).
  + rewrite <- !e.
    destruct (eq_nat n0 n0); try lia.
    unfold get.
    simpl.
    rewrite <- !e.
    simpl. f_equal.
    f_equal. lia.
  + case_eq size.
    * intros. unfold get.
      simpl. rewrite <- plus_n_Sm. simpl. reflexivity.
    * intros.
      destruct (eq_nat n0 n2); try lia.
      unfold get.
      simpl. rewrite <- plus_n_Sm. simpl. reflexivity.
Qed.

(* mk_0 is full of zero *)
Theorem get_mk_0 n p : get p (mk_0 out n) = out.
Proof.
revert p; elim n; unfold get; simpl; auto.
- intros p; case (pos2n p); auto.
- intros n1 Rec p; case p; simpl.
  intros x y; case y.
  + case x; auto.
    intros x1; rewrite  Nat.add_0_r.
    case_eq size.
    * intros _ ; rewrite Nat.mul_0_r; auto.
    * intros n2 Hn2.
      replace (S x1 * S n2) with (S (x1 * size + n2)); simpl.
      --generalize (Rec (Pos x1 n2)); auto.
      --rewrite Hn2; simpl; rewrite (Nat.add_comm n2); auto.
  + intros y1; generalize (Rec (Pos x y1)); simpl; auto.
    rewrite <- plus_n_Sm; auto.
Qed.

(******************************************************************************)
(*    Update                                                                  *)
(******************************************************************************)

(* Update the list l at the position (x, y) with the value v *)
Definition update p v (l: list nat) := subst (pos2n p) v l.

(* The length after an update is unchanged *)
Theorem length_update p v l : length (update p v l) = length l.
Proof.
revert v l; unfold update; elim (pos2n p); simpl; auto.
- intros v l; case l; auto.
- intros n1 Rec v l; case l; simpl; auto.
Qed.

(* Getting the updated cell gives the new value *)
Theorem update_get p v l : pos2n p < length l -> get p (update p v l) = v.
Proof.
unfold get, update; generalize (pos2n p);
    elim l; simpl; clear l p.
- intros n H; contradict H; auto with arith.
- intros a l1 Rec n; case n; clear n; simpl; auto with arith.
Qed.

(* Getting outside the updated cell returns the previous value *)
Theorem update_diff_get p1 p2 v l :
  valid_pos p1 -> valid_pos p2 -> p1 <> p2 -> get p1 (update p2 v l) = get p1 l.
Proof with auto with arith.
intros Hp1 Hp2 H; unfold get, update.
cut (pos2n p1 <> pos2n p2).
- generalize l (pos2n p2); elim (pos2n p1); auto; clear l.
  + intros l n1; case n1; simpl.
    intros U; case U...
    intros n2 _; case l...
  + intros n1 Rec l n2; case n2...
    * case l; simpl...
    * intros n3 U; case l; simpl...
- contradict H; generalize H Hp1 Hp2; clear H Hp1 Hp2; case p1; case p2; simpl.
  intros x2 y2 x1 y1 H (H1, H2) (H3, H4).
  assert (HH: x1 = x2) by nia.
  f_equal; auto; subst...
  apply Nat.add_cancel_l with (x2 * size)...
Qed.

(******************************************************************************)
(*    Restrict till position                                                  *)
(******************************************************************************)

Definition prestrict p := restrict out (pos2n p).

Theorem prestrict_0 l : prestrict (Pos 0 0) l = mk_0 out (length l).
Proof. unfold prestrict; simpl; apply restrict_0. Qed.

Theorem prestrict_all p s : length s <= pos2n p -> prestrict p s = s.
Proof. unfold prestrict; intros H; apply restrict_all; auto. Qed.

Theorem prestrict_length p s : length (prestrict p s) = (length s).
Proof. unfold prestrict; simpl; apply restrict_length. Qed.

Theorem prestrict_update p s :
  pos2n (next p) <= length s ->
  prestrict (next p) s = update p (get p s) (prestrict p s).
Proof.
unfold prestrict, get, update.
rewrite next_pos; intros H; apply restrict_update; auto.
Qed.

Theorem prestrict_get s p q :
  pos2n p < pos2n q -> get p (prestrict q s) = get p s.
Proof.
intros H; unfold get, prestrict.
repeat rewrite <- jump_nth.
apply restrict_nth; auto.
Qed.

Theorem prestrict_get_default s p q :
  pos2n q <= pos2n p -> get p (prestrict q s) = out.
Proof.
intros H; unfold get, prestrict.
repeat rewrite <- jump_nth.
apply restrict_nth_default; auto.
Qed.

(******************************************************************************)
(*    Refine                                                                  *)
(******************************************************************************)

(* A state refines another if it has only substitutes non ref_list element    *)
Definition refine s1 s2 :=
  length s1 = size * size /\
  length s2 = size * size /\
  forall p, valid_pos p -> In (get p s1) ref_list -> get p s1 = get p s2.

(* Refinement is transitive                                                   *)
Theorem refine_trans s1 s2 s3 : refine s1 s2 -> refine s2 s3 -> refine s1 s3.
Proof.
intros (H, (H1, H2)) (H3, (H4, H5)); split; auto.
split; auto.
intros; rewrite H2; auto.
apply H5; auto.
rewrite <- H2; auto.
Qed.

(* Every states refine the initial state *)
Theorem refine_init s : length s = size * size -> refine init s.
Proof.
intros H; split; auto.
- apply length_init.
- split; auto.
  intros p _; unfold init; rewrite get_mk_0.
  intros H1; contradict H1; apply out_not_in_refl.
Qed.

(* update is a refinement *)
Theorem refine_update p v s :
  ~ In (get p s) ref_list -> length s = size * size -> refine s (update p v s).
Proof.
intros H H1; split; auto.
split; auto.
- unfold update; rewrite length_subst; auto.
- intros p1  _.
  generalize H; unfold get, update; generalize (pos2n p) (pos2n p1);
    clear p p1 H.
  elim s; simpl; auto.
  + intros n1 n2; case n1; case n2; auto.
  + intros a s1 Rec n1 n2; case_eq n1; case_eq n2; simpl; auto.
    intros _ _ H2 H3; case H2; auto.
Qed.

(******************************************************************************)
(*    Empty                                                                   *)
(******************************************************************************)

(* A state is empty if it is full of zero *)
Definition empty s := forall p, ~ In (get p s) ref_list.

(* The empty list is empty *)
Theorem empty_nil : empty nil.
Proof. intros p; rewrite get_nil; apply out_not_in_refl. Qed.

Theorem empty_mk_0 n : empty (mk_0 out n).
Proof. intros p; unfold empty; rewrite get_mk_0; apply out_not_in_refl. Qed.

(* Jumping an empty state gives an empty state *)
Theorem empty_jump n s : empty s -> empty (jump n s).
Proof.
revert s; elim n; simpl; auto.
intros n0 Rec s0; case s0; auto.
intros a s1 H; apply Rec.
intros p; case p; intros x y.
generalize (H (Pos x (S y))); unfold get; simpl.
rewrite <- plus_n_Sm; simpl; auto.
Qed.

(* A state that start with an element not in the ref_list
   is empty if its tail is empty *)
Theorem empty_cons a s : ~ In a ref_list -> empty s -> empty (a :: s).
Proof.
intros Ha H p; case p; intros x y; case y; simpl.
- case x; unfold get; simpl; auto.
  intros x1.
  rewrite  Nat.add_0_r.
  generalize (H (Pos x1 (pred size))); unfold get; simpl; case size; simpl.
  + rewrite Nat.mul_0_r; simpl;auto.
  + intros n1; rewrite (Nat.add_comm n1); auto.
- intros y1; generalize (H (Pos x y1)); unfold get; simpl.
  rewrite <- plus_n_Sm; auto.
Qed.

(* Inversion theorem for empty *)
Theorem empty_inv a s : empty (a :: s) -> ~ In a ref_list /\ empty s.
Proof.
intros H; split.
- generalize (H (Pos 0 0)); unfold get; simpl; auto.
- intro p; rewrite <- get_next with (a := a); auto.
Qed.

(* For a take to be empty it is sufficient the state to be empty *)
Theorem empty_take n s : empty s -> empty (take n s).
Proof.
revert s; elim n; simpl; auto.
- intros s; case s; auto.
  intros n1 l1 _ p; apply empty_nil.
- intros n1 Rec s; case s; auto.
  intros n2 s1 H.
  case empty_inv with (1 := H); intros H1 H2; subst.
  apply empty_cons; auto.
Qed.

(******************************************************************************)
(*    Rows                                                                    *)
(******************************************************************************)

Definition row i (l: list nat) := take size (jump (i * size) l).

Theorem length_row i s :
  i < size -> length s = size * size -> length (row i s) = size.
Proof.
intros H H1; unfold row; apply length_take1.
apply Nat.add_le_mono_l with (i * size).
repeat rewrite (Nat.add_comm (i * size)).
rewrite <- length_jump; rewrite H1; try (change ((S i) * size <= size * size));
  apply Nat.mul_le_mono_r; auto with arith.
Qed.

(* Relation between get and row *)
Theorem get_row x y s : y < size -> get (Pos x y) s = nth y (row x s) out.
Proof.
unfold get, row; simpl.
rewrite jump_add.
generalize (jump (x * size) s); intros l.
generalize y size; elim l; simpl; auto; clear y l.
- intros; rewrite jump_nil, take_nil; repeat rewrite nth_nil; auto.
- intros a l Rec y; case y.
  + intros n; case n; simpl; auto.
    intros H; contradict H; auto with arith.
  + intros y1 n; case n; simpl; auto with arith.
    intros H; contradict H; auto with arith.
Qed.

(******************************************************************************)
(*    Columns                                                                 *)
(******************************************************************************)

Definition column i (l : list nat) := take_and_jump 1 size size (jump i l).

Theorem length_column j s :
  j < size -> length s = size * size -> length (column j s) = size.
Proof.
intros H H1; unfold column.
rewrite length_take_and_jump; auto with arith.
generalize H H1; case size; clear H H1.
- simpl; auto with arith.
- intros size1 H H1; apply Nat.add_le_mono_l with j.
  repeat rewrite (Nat.add_comm j).
  rewrite <- Nat.add_assoc, (Nat.add_comm 1), <- Nat.add_assoc.
  rewrite <- length_jump; auto with arith.
  + rewrite H1; auto with arith.
    replace (S size1 * S size1) with (size1 * S size1 + S size1); 
      auto with arith.
    * apply Nat.add_le_mono; simpl; auto with arith.
      rewrite Nat.add_comm; simpl; auto with arith.
    * rewrite Nat.add_comm; simpl; auto.
  + rewrite H1; simpl; auto with arith.
Qed.

(* Relation between get and column *)
Theorem get_column x y s : x < size -> get (Pos x y) s = nth x (column y s) out.
Proof.
unfold get, column; simpl.
rewrite Nat.add_comm, jump_add.
generalize (jump y s); intros l.
assert (Gen:
  forall a x l,
    x < a ->
    nth 0 (jump (x * size) l) out = nth x (take_and_jump 1 size a l) out); auto.
clear x l.
intros a; elim a; simpl; auto; clear a.
- intros a l H; contradict H; auto with arith.
- intros a Rec; intros x; case x; simpl; clear x.
  + intros l; case l; simpl; auto.
    rewrite jump_nil, take_and_jump_nil, nth_nil; auto.
  + intros x l; case l; auto; clear l.
    * repeat rewrite jump_nil; rewrite take_and_jump_nil; rewrite nth_nil; auto.
    * intros n l; case l; simpl; auto.
      --intros H; rewrite <- Rec; auto with arith.
        f_equal; auto; apply jump_add; auto.
      --intros n1 l1 H; rewrite <- Rec; auto with arith.
        f_equal; auto; apply jump_add; auto.
Qed.

(******************************************************************************)
(*    SubRectangles                                                           *)
(******************************************************************************)

(* The subrectangles *)
Definition rect i (l : list nat) :=
  take_and_jump w size h (jump (w * (mod i h) +  h * (div i  h) * size) l).

(* Relation between get and rect *)
Theorem get_rect x y s :
  x < size -> y < size ->
  get (Pos x y) s =
  nth (mod x h * w + mod y w) (rect (div x h * h + div y w) s) out.
Proof with auto with arith.
intros H1 H2; unfold get, rect; simpl.
generalize (h_pos _ H1); intros U1.
generalize (w_pos _ H1); intros U2.
assert (F1: div y w < h).
  {
    apply div_lt; rewrite  Nat.mul_comm...
  }
repeat (rewrite (fun x =>  Nat.mul_comm x h)); rewrite mod_mult_comp...
rewrite div_mult_comp, (mod_small (div y w) h), (div_is_0 (div y w) h),
        Nat.add_0_r...
match goal with
  |- context [take_and_jump _ _ _ (jump ?X _)] =>
    replace (x * size + y) with (X + (mod x h * size + mod y w))
end.
2: {
  apply sym_equal.
  pattern x at 1; rewrite (div_mod_correct x h)...
  pattern y at 1; rewrite (div_mod_correct y w)...
  lia.
  }
rewrite jump_add.
match goal with 
  |- context [jump ?X s] => generalize (jump X s)
end.
intros l; rewrite <- jump_nth; generalize l; clear l.
generalize (mod_lt x h U1).
generalize (mod x h).
cut (w <= size).
- generalize size; intros m.
  intros U3 n; generalize h; elim n; simpl...
  + clear n H1 H2 U1.
    intros h1; case h1; simpl...
    * intros HH; contradict HH...
    * intros n1 _ l.
      case (Nat.le_gt_cases (length l) (mod y w)); intros H1.
      ++rewrite jump_too_far.
        **rewrite take_and_jump_nil.
          rewrite <- app_nil_end.
          apply sym_equal; apply take_nth...
        **pose proof (mod_lt y w).
          lia.
      ++rewrite nth_app_l.
        **apply sym_equal; apply take_nth...
          left; apply mod_lt...
        **case (Nat.le_gt_cases (length l) w); intros H2.
          *** rewrite length_take_small...
          *** rewrite length_take...
              apply mod_lt...
  + intros n1 Rec h1; case h1; simpl.
    * intros HH; contradict HH...
    * intros h2 HH l.
      case (Nat.le_gt_cases (length l) w); intros H3.
      ++rewrite nth_app_r.
        **rewrite length_take_small, jump_too_far...
          *** rewrite take_and_jump_nil.
              repeat rewrite nth_default...
              apply Nat.le_trans with (1 := H3)...
          *** apply Nat.le_trans with (1 := H3)...
        **rewrite length_take_small...
        ++rewrite nth_app_r.
          *** rewrite length_take...
              repeat rewrite <- Nat.add_assoc; 
              rewrite (Nat.add_comm w), Nat.add_sub...
              rewrite jump_nth, jump_add, <- jump_nth...
          *** rewrite length_take...
- unfold size; nia.
Qed.

Theorem length_rect i s :
  i < size -> length s = size * size -> length (rect i s) = size.
Proof with auto with arith.
intros H H1; unfold rect.
generalize (h_pos _ H); intros U1.
generalize (w_pos _ H); intros U2.
rewrite length_take_and_jump...
assert (F1: forall n m, 0 < n -> m < n -> m <= n - 1) by lia.
match goal with 
  |- _ <= length (jump ?X _) =>
    apply Nat.add_le_mono_l with X; repeat rewrite (Nat.add_comm X);
    rewrite <- length_jump; auto with arith
end.
- rewrite H1; clear H1.
  replace (size * size) with  
          (w + ((h - 1) * size) + (w * (h -1)) + h * (w - 1) * size).
  + repeat rewrite Nat.add_assoc.
    repeat (apply Nat.add_le_mono || apply Nat.mul_le_mono_l ||
            apply Nat.mul_le_mono_r);
        auto with arith.
    * generalize U1; case h...
    * apply F1; auto; apply mod_lt...
    * apply F1; auto; apply div_lt...
  + rewrite (Nat.add_comm w).
    repeat (rewrite <- Nat.add_assoc).
    rewrite (Nat.add_assoc w).
    pattern w at 1; rewrite <- Nat.mul_1_r, <- Nat.mul_add_distr_l.
    rewrite (Nat.add_comm _ (h - 1)), Nat.sub_add...
    unfold size.
    ring_simplify.
    destruct (lt_eq_lt_dec h w) as [[Hh|Hh]|Hh].
    * nia.
    * rewrite Hh, Nat.mul_sub_distr_r; nia.
    * nia.
- apply Nat.le_trans with (w * (h - 1) + h * (w - 1) * size).
  + repeat (apply Nat.add_le_mono || apply Nat.mul_le_mono_l ||
            apply Nat.mul_le_mono_r).
    * apply F1; auto; apply mod_lt...
    * apply F1; auto; apply div_lt...
  + rewrite H1; unfold size.
    pattern w at 4; replace w with (1 + (w - 1)) by lia.
    nia.
Qed.

(******************************************************************************)
(*    Sudoku                                                                  *)
(******************************************************************************)


(* To be a sudoku, the list should be of the proper size, rows, columns and   *)
(* subrectangle should be a permutation of the reference list                 *)
Definition sudoku l :=
  length l = size * size /\
  (forall i, i < size -> Permutation (row i l) ref_list) /\
  (forall i, i < size -> Permutation (column i l) ref_list) /\
  (forall i, i < size -> Permutation (rect i l) ref_list).

(******************************************************************************)
(*    A function that check if a grid is a sudoku                             *)
(******************************************************************************)

(* A function that check that a predicate P holds for i smaller than n        *)
Definition check_P (P: nat -> Prop) (P_dec: forall i, {P i} + {~ P i}) n :
    {forall i, i < n -> P i} + {~forall i, i < n -> P i}.
Proof.
revert n; fix check_P 1.
intros n; case n; clear n.
- left; intros i tmp; contradict tmp; auto with arith.
- intros n; case (check_P n); intros H.
  case (P_dec n); intros H1.
  + left; intros i Hi; case (Lt.le_lt_or_eq_stt i n); 
      try intros Hi1; subst; auto with arith.
  + right; intros H2; case H1; auto with arith.
  + right; contradict H; auto with arith.
Defined.

(* A function that checks is a list is a sudoku *)
Definition check l : {sudoku l} + {~sudoku l}.
Proof.
case (eq_nat (length l) (size * size)); intros H1.
- case (check_P (fun i => Permutation (row i l) ref_list)
                (fun i => permutation_dec1 eq_nat (row i l) ref_list) size); 
    intros H2.
  + case (check_P (fun i => Permutation (column i l) ref_list)
                  (fun i => permutation_dec1 eq_nat 
                              (column i l) ref_list) size);
    intros H3.
    * case (check_P (fun i => Permutation (rect i l) ref_list)
                    (fun i => permutation_dec1 eq_nat (rect i l) 
                                ref_list) size); intros H4.
      --left; unfold sudoku; auto.
      --right; intros (_,(_,(_,HH))); case H4; auto.
    * right; intros (_,(_,(HH, _))); case H3; auto.
  + right; intros (_,(HH,_)); case H2; auto.
- right; intros (HH,_); case H1; auto.
Defined.

(******************************************************************************)
(*    Literal, clause, clauses                                                *)
(******************************************************************************)

(* A literal is composed of two coordonates and a value *)
Inductive lit: Set := L (p: pos) (v: nat).

(* A comparison function for literals *)
Definition lit_test (v1 v2: lit) :=
  match v1 with
  | L p1 v1 => 
    match v2 with
    | L p2 v2 =>
      match pos_test p1 p2 with
      | eq =>  test v1 v2
      | r  => r
      end
    end
  end.

(* lit_test is transitive *)
Theorem lit_test_trans l1 l2 l3 :
    lit_test l1 l2 = lit_test l2 l3 -> lit_test l1 l3 = lit_test l1 l2.
Proof with auto.
case l1; case l2; case l3; simpl...
intros p3 z3 p2 z2 p1 z1.
case_eq (pos_test p1 p2); intros H.
- case_eq (pos_test p2 p3); intros H1.
  + rewrite (pos_test_trans p1 p2 p3); rewrite H...
  + assert (p2 = p3); subst.
    * apply pos_test_exact with (1 := H1)...
    * rewrite H...
  + intros; discriminate.
- replace p1 with p2...
  case_eq (pos_test p2 p3); intros H1...
  + intros; apply test_trans...
  + apply sym_equal; apply pos_test_exact with (1 := H)...
- case_eq (pos_test p2 p3); intros H1.
  + intros; discriminate.
  + assert (p2 = p3); subst.
    * apply pos_test_exact with (1 := H1)...
    * rewrite H...
  + rewrite (pos_test_trans p1 p2 p3); rewrite H...
Qed.

(* lit_test is anti symmetric *)
Theorem lit_test_anti_sym l1 l2 : lit_test l1 l2 = opp (lit_test l2 l1).
Proof.
case l1; case l2; simpl; auto.
intros p2 z2 p1 z1; rewrite (pos_test_anti_sym p1 p2).
case (pos_test p2 p1); simpl; auto.
apply test_anti_sym.
Qed.

(* lit_test gives equality *)
Theorem lit_test_exact l1 l2 : lit_test l1 l2 = eq -> l1 = l2.
Proof.
case l1; case l2; simpl; auto.
intros p2 z2 p1 z1; case_eq (pos_test p1 p2); intros H; auto.
- intros; discriminate.
- intros H1; f_equal; try apply pos_test_exact; auto.
  apply test_exact; auto.
- intros; discriminate.
Qed.

(* A clause is a list of literals, most of the time it
   is intepretated as a disjunction *)
Definition clause:= list lit.

(* Check if a literal is in a clause *)
Definition lit_is_in (l : lit) (c : clause) : bool := is_in _ lit_test l c.

(* Insert a literal v in an ordered clause l *)
Definition lit_insert (v : lit) (l : clause) : clause := insert _ lit_test v l.

(* Order the element in clauses by their indexes *)
Definition clause_test (c1 c2 : nat * clause) :=
  match c1 with (n1, _) => match c2 with (n2, _) => test n1 n2 end end.

(* Remove all the literals of the clause c1 from the clause c2 *)
Definition lit_rm (c1 c2 : clause) : clause := rm _ lit_test c1 c2.

(* Merge two ordered clauses *)
Definition clause_merge (c1 c2 : clause) : clause := merge _ lit_test c1 c2.

(* A list of clauses, to each clause we associate its
   length for sorting *)
Definition clauses := list (nat * clause).

(* Insert a clause v of length n in the list of clauses l *)
Definition clause_insert (c : clause) (cs : clauses) : clauses :=
  ocons _ clause_test (length c, c) cs.

(* Add two list of clauses l *)
Definition clauses_merge (cs1 cs2 : clauses) : clauses :=
  add _ clause_test cs1 cs2.

(* Update the list of clauses cs with the fact l that we know that holds
   and the list of literals c that we know that do not hold:
      - clauses that contain l are removed
      - in each clause the literals in c are removed.
 *)
Fixpoint clauses_update (l : lit) (c : list lit) (cs : clauses) 
                        {struct cs} : clauses :=
  match cs with
  | nil => nil
  | (n , c1) :: cs1 =>
    if lit_is_in l c1 then clauses_update l c cs1 else
      let res := lit_rm c c1 in
      clause_insert res (clauses_update l c cs1)
  end.

(******************************************************************************)
(*        Generate constrains                                                 *)
(******************************************************************************)

(* Generate the clause that indicates that the value z appears in
   the row i
 *)
Definition gen_row i z :=
  fold_right (fun y l => lit_insert (L (Pos i y) z) l) nil indexes.

(* Generate the clause that indicates that the value z appears in
   the column i
 *)
Definition gen_column i z :=
  fold_right (fun x l => lit_insert (L (Pos x i) z) l) nil indexes.

(* Generate the clause that indicates that the value z appears in
   the rectangle i
 *)
Definition gen_rect i z :=
  let x := h * div i h in
  let y := w * mod i h in
  fold_right (fun p l => lit_insert (L (shift p x y) z) l) nil cross.

(* Generate the clause that indicates that the cell (x, y) contains
   a value in the ref_list
 *)
Definition gen_cell p :=
  fold_right (fun z l => lit_insert (L p z) l) nil ref_list.

(* Generate the list of clauses that all cells contains a value
  in the reference list
 *)
Definition all_cell :=
  let c0 := cross2 in
  (fold_right (fun p l =>  let res := gen_cell p in
                        clause_insert res l) nil c0).

(* Generate the initial list of clauses:
     - every numbers of the reference list should appear in every rows
     - every numbers of the reference list should appear in every columns
     - every numbers of the reference list should appear in every rectangles
     - every cell should contain a number of the reference list
 *)
Definition init_c :=
  let c1 := cross1 in
  fold_right (fun iz l => let res := gen_row (fst iz) (snd iz) in
                clause_insert res l)
    (fold_right (fun iz l => let res := gen_column (fst iz) (snd iz) in
                  clause_insert res l)
      (fold_right (fun iz l => let res := gen_rect (fst iz) (snd iz) in
                    clause_insert res l)
        all_cell c1) c1) c1.

(* Given a literal that we know that holds generate the list of literals
   that we know cannot hold *)
Definition anti_literals l :=
  let c := l :: nil in
  match l with
  | L ((Pos x y) as k) z =>
      clause_merge (lit_rm c (gen_row x z))
        (clause_merge (lit_rm c (gen_column y z))
          (clause_merge (lit_rm c (gen_rect ((div x h) * h + (div y w))  z))
            (lit_rm c (gen_cell k))))
  end.

(* Auxiliary function that updates the list of clauses c with
   the list s, interpreting the first element of s as in position (x,y)
   the update is performed only for the elements of s that are in l
 *)
Fixpoint gen_init_clauses_aux (s : list nat) (p : pos) (c : clauses)
    {struct s} : clauses :=
  match s with
  | nil => c
  | a :: s1 =>
    let p1 := next p in
    let ll := L p a in
    if (In_dec eq_nat a ref_list) then
      let c1 := clauses_update ll (anti_literals ll) c in
      gen_init_clauses_aux s1 p1 c1
    else gen_init_clauses_aux s1 p1 c
  end.

(* Generate the list of clauses relative to a list s *)
Definition gen_init_clauses s := gen_init_clauses_aux s (Pos 0 0) init_c.


(***************************************************)
(*    Algorithm that finds a solution              *)
(***************************************************)

(* Try to satisfy one of the literal of list l calling after
   the continuation f
 *)
Fixpoint try_one (s: list nat) (c: clause)
         (cs: clauses)
         (f: list nat -> clauses -> option (list nat))
         {struct c}:
  option (list nat) :=
  match c with
    nil => None
  | (L p z) as k:: c1 =>
    let s1 := update p z s in
    let cs1 := clauses_update k (anti_literals k) cs in
    match f s1 cs1 with
      None => try_one s c1 cs f
    | Some c1 => Some c1
    end
  end.

(* An auxiliary function to find a solution by iteratively trying
   to satisfy the first clause of the list of clauses cs
 *)
Fixpoint find_one_aux (n : clauses) (s : list nat) (cs : clauses) {struct n} :
    option (list nat) :=
  match cs with
  | nil => Some s
  | (_, nil) :: _  => None
  | (_, p) :: cs1 =>
    match n with
    | nil => None
    | _ :: n1 => try_one s p cs1 (find_one_aux n1)
    end
  end.

(* Find one solution that refines the state s *)
Definition find_one s := let cs := gen_init_clauses s in find_one_aux cs s cs.

(******************************************************************************)
(*    Algorithm that finds all solutions                                      *)
(******************************************************************************)

(** The merge for the sudoku **)
Definition merges := merge _ (lexico _ test).

(* Find all the literals of list l that can be satisfied calling after
   the continuation f
 *)
Fixpoint try_all (s : list nat) (c : clause) (cs:  clauses)
                 (f : list nat -> clauses -> list (list nat)) {struct c} :
   list (list nat) :=
  match c with
  | nil => nil
  | (L p z) as k:: l1 =>
    let s1 := update p z s in
    let cs1 := clauses_update k (anti_literals k) cs in
    merges (f s1 cs1) (try_all s l1 cs f)
  end.

(* An auxiliary function to find all solutions by iteratively trying
   to satisfy the first clause of the list of clauses c
 *)
Fixpoint find_all_aux (n : clauses) (s : list nat) (cs : clauses) {struct n}:
  list (list nat) :=
  match cs with
  | nil => s :: nil
  | (_, nil) :: _  => nil
  | (_, p) :: cs1 =>
    match n with
    | nil => nil
    | _ :: n1 => try_all s p cs1 (find_all_aux n1)
    end
  end.

(* Find all solutions that refines the state s *)
Definition find_all s := let cs := gen_init_clauses s in find_all_aux cs s cs.

(******************************************************************************)
(*  Algorithm that finds one solution and insures that it is unique           *)
(******************************************************************************)

Inductive jRes : Set := jNone | jOne (_ : list nat) | jMore (_ _ : list nat).

Fixpoint try_just_one (s : list nat) (c : clause) (cs : clauses)
    (f : list nat -> clauses -> jRes) : jRes :=
  match c with
  | nil => jNone
  | (L p v) as k:: c1 =>
    let s1 := update p v s in
    let cs1 := clauses_update k (anti_literals k) cs in
    match f s1 cs1 with
    | jNone => try_just_one s c1 cs f
    | jOne s2 => 
      match try_just_one s c1 cs f with
      | jNone => jOne s2
      | jOne s3 => if list_nat_eq s2 s3 then jOne s2 else jMore s2 s3
      | jMore s1 s2 => jMore s1 s2
      end
    | jMore s1 s2 => jMore s1 s2
    end
  end.

(* An auxiliary function to find a solution by iteratively trying
   to satisfy the first clause of the list of clauses c
 *)
Fixpoint find_just_one_aux (n : clauses) (s : list nat) (cs : clauses) : jRes :=
match cs with
| nil => jOne s
| (_, nil) :: _  => jNone
| (_, p) :: cs1 =>
    match n with
    |  nil => jNone
    | _ :: n1 => try_just_one s p cs1 (find_just_one_aux n1)
    end
end.

(* Find one solution that refines the state s *)
Definition find_just_one s :=
  let cs := gen_init_clauses s in find_just_one_aux cs s cs.

(******************************************************************************)
(*            length                                                          *)
(******************************************************************************)

(* Adding a clause increments the length *)
Theorem length_clause_insert c cs : length (clause_insert c cs) = S (length cs).
Proof. unfold clause_insert; apply ocons_length. Qed.

(* Adding two classes adds their length *)
Theorem length_clauses_merge cs1 cs2 :
  length (clauses_merge cs1 cs2) = length cs1 + length cs2.
Proof. unfold clauses_merge; apply add_length. Qed.

Theorem length_clauses_update l c cs :
  length (clauses_update l c cs) <= length cs.
Proof.
elim cs; simpl; auto.
intros (n1, c1) cs1 Rec; case (lit_is_in l c1); auto with arith.
apply Nat.le_trans with (2 := (le_n_S _ _ Rec)).
rewrite length_clause_insert; auto with arith.
Qed.

Theorem length_indexes : length indexes = size.
Proof.
unfold indexes; generalize 0; induction size; simpl; auto.
Qed.

(******************************************************************************)
(*            Correctness                                                     *)
(******************************************************************************)

(* Specification of lit_insert *)
Theorem lit_insert_in l1 l2 c : In l1 (lit_insert l2 c) <-> l1 = l2 \/ In l1 c.
Proof.
unfold lit_insert; split; intros H.
- apply insert_inv with (1 := H).
- case H; intros H1; subst.
  + apply insert_in; auto.
    exact lit_test_exact.
  + apply insert_incl; auto.
Qed.

Theorem clause_merge_in l c1 c2 :
  In l (clause_merge c1 c2) <-> In l c1 \/ In l c2.
Proof.
unfold clause_merge; split; intros H.
- apply merge_inv with (1 := H); auto.
- case H; intros H1.
  + apply merge_incl_l; auto.
  + apply merge_incl_r; auto.
    exact lit_test_exact.
Qed.

(* Specification of clause_insert *)
Theorem clause_insert_in p c cs :
  In p (clause_insert c cs) <-> p = (length c, c) \/ In p cs.
Proof.
unfold clause_insert; split; intros H.
- case ocons_inv with (1 := H); auto.
- case H; clear H; intros H; subst.
  + apply ocons_in; auto.
  + apply ocons_incl; auto.
Qed.

(* Specification of clauses_merge *)
Theorem clauses_merge_in p cs1 cs2 :
  In p (clauses_merge cs1 cs2) <-> In p cs1 \/ In p cs2.
Proof.
unfold clauses_merge; split; intros H.
- case add_inv with (1 := H); auto.
- case H; clear H; intros H.
  + apply add_incl_l; auto.
  + apply add_incl_r; auto.
Qed.

Theorem gen_row_correct l i z :
    In l (gen_row i z) <-> exists j, l = L (Pos i j) z /\ j < size.
Proof.
unfold gen_row, indexes; revert l i z.
assert (Eq1: 
    forall a l i z,
      In l (fold_right (fun y l => lit_insert (L (Pos i y) z) l)
              nil (progression size a)) <->
      (exists j: nat, l = L (Pos i j) z /\ a <= j < a + size));
    auto.
- elim size; simpl; auto.
  + intros a l i z; split.
    * intros H; case H.
    * intros (j, (_, (H1, H2))); contradict H2; rewrite Nat.add_0_r;
        auto with arith.
  + intros size1 Rec1 a l i z; split.
    * intros H1.
      match type of H1 with 
      | In ?X (lit_insert ?Y ?Z) =>
          case (lit_insert_in X Y Z); intros tmp _; case (tmp H1); clear tmp
      end; intros H2; subst.
      --exists a; split; auto with arith.
        split; auto with arith.
        apply Nat.le_lt_trans with (a + 0); auto with arith.
      --case (Rec1 (S a) l i z); intros tmp _; case tmp; auto; clear tmp.
        intros j (H3, (H4, H5)); exists j; split; auto with arith.
        rewrite <- plus_n_Sm; split; auto with arith.
    * intros (j, (H3, (H4, H5))).
      match goal with 
      |- In ?X (lit_insert ?Y ?Z) =>
        case (lit_insert_in X Y Z); intros _ tmp; apply tmp; clear tmp
      end; auto.
      case Lt.le_lt_or_eq_stt with (1 := H4); clear H4; intros H4; auto.
      --right; case (Rec1 (S a) l i z); intros _ tmp; apply tmp; clear tmp.
        rewrite <- plus_n_Sm in H5; exists j; auto with arith.
      --subst; auto.
- intros l i z; split; intros H.
  + case (Eq1 0 l i z); intros tmp _; case tmp; clear tmp Eq1; auto.
    rewrite  Nat.add_0_l; intros j (H1, (H2, H3)); exists j; auto.
  + case H; intros j (H1, H2); clear H.
    case (Eq1 0 l i z); intros _ tmp; apply tmp; clear tmp; exists j;
    auto with arith.
Qed.

Theorem gen_column_correct l j z :
    In l (gen_column j z) <-> exists i, l = L (Pos i j) z /\ i < size.
Proof.
unfold gen_column, indexes; revert l j z.
assert (Eq1: 
    forall a l j z,
      In l (fold_right (fun x l => lit_insert (L (Pos x j) z) l)
                            nil (progression size a)) <->
      (exists i: nat, l = L (Pos i j) z /\ a <= i < a + size));
    auto.
- elim size; simpl; auto.
  + intros a l j z; split.
    * intros H; case H.
    * intros (i, (_, (H1, H2))); contradict H2; rewrite Nat.add_0_r;
        auto with arith.
  + intros size1 Rec1 a l j z; split.
    * intros H1.
      match type of H1 with
      | In ?X (lit_insert ?Y ?Z) =>
        case (lit_insert_in X Y Z); intros tmp _; case (tmp H1); clear tmp
      end; intros H2; subst.
      --exists a; split; auto with arith.
        split; auto with arith.
        apply Nat.le_lt_trans with (a + 0); auto with arith.
      --case (Rec1 (S a) l j z); intros tmp _; case tmp; auto; clear tmp.
        intros i (H3, (H4, H5)); exists i; split; auto with arith.
        rewrite <- plus_n_Sm; split; auto with arith.
    * intros (i, (H3, (H4, H5))).
      match goal with 
      |- In ?X (lit_insert ?Y ?Z) =>
        case (lit_insert_in X Y Z); intros _ tmp; apply tmp; clear tmp
      end; auto.
      case Lt.le_lt_or_eq_stt with (1 := H4); clear H4; intros H4; auto.
      --right; case (Rec1 (S a) l j z); intros _ tmp; apply tmp; clear tmp.
        rewrite <- plus_n_Sm in H5; exists i; auto with arith.
      --subst; auto.
- intros l j z; split; intros H.
  + case (Eq1 0 l j z); intros tmp _; case tmp; clear tmp Eq1; auto.
    rewrite  Nat.add_0_l; intros i (H1, (H2, H3)); exists i; auto.
  + case H; intros i (H1, H2); clear H.
    case (Eq1 0 l j z); intros _ tmp; apply tmp; clear tmp; exists i;
      auto with arith.
Qed.

Theorem fold_insert1 (A : Set) (f : A -> lit) a l :
  In a l -> In (f a) (fold_right (fun p l => lit_insert (f p) l) nil l).
Proof.
elim l; simpl; auto with arith; clear l.
intros b l1 Rec [H | H]; subst;
  match goal with
  |- In ?X (lit_insert ?Y ?Z) =>
    case (lit_insert_in X Y Z); intros _ tmp; apply tmp; clear tmp; auto
  end.
Qed.

Theorem fold_insert2 (A : Set) (f : A -> lit) a l :
  In a (fold_right (fun p l => lit_insert (f p) l) nil l) ->
  (exists b, In b l /\ a = f b).
Proof.
elim l; simpl; auto with arith; clear l.
- intros H; case H.
- intros b l1 Rec H1.
  match goal with 
  | H1 : In ?X (lit_insert ?Y ?Z) |- _ =>
    case (lit_insert_in X Y Z); intros tmp _; case (tmp H1); clear tmp H1; auto;
    intros H1; subst
  end.
  + exists b; auto with arith.
  + case Rec; auto with arith.
    intros b1 (Hb, Hb1); subst.
    exists b1; auto.
Qed.

Theorem gen_rect_correct l i z :
  i < size ->
  (In l (gen_rect i z) <->
  exists i1, exists j1, l = L (Pos (h * div i h + i1) (w * mod i h + j1)) z
    /\ i1 < h /\ j1 < w).
Proof.
destruct l as ((x, y), z1); intros H; unfold gen_rect; split; intros H1.
- generalize (fold_insert2 _
      (fun p => (L (shift p (h * div i h) (w * mod i h)) z))  _ _ H1).
  clear H1; intros (b, (Hb, Hb1)).
  match type of Hb with
  | In ?X cross =>
    case (cross_correct X); intros tmp _; case (tmp Hb); clear tmp
  end.
  intros i1 (j1, (H4, (H5, H6))); exists i1; exists j1;
    intros; subst; auto with arith.
- case H1; intros i1 (j1, (H2, (H3, H4))); clear H1.
  rewrite H2.
  match goal with
  |- In (L (Pos (?X + ?Y) (?Z + ?T)) ?U) ?V =>
    change (In (L (shift (Pos Y T) X Z) U) V)
  end.
  apply fold_insert1 with 
    (f := (fun p => (L (shift p (h * div i h) (w * mod i h)) z))); auto.
  case (cross_correct (Pos i1 j1)); intros _ tmp; apply tmp; clear tmp.
  exists i1; exists j1; auto.
Qed.

Theorem gen_cell_correct l x y :
  (In l (gen_cell (Pos x y)) <->
  exists z, l = L (Pos x y) z /\ (In z ref_list)).
Proof.
unfold gen_cell; split.
intros H2.
case (fold_insert2 _ (fun p => (L (Pos x y) p))  _ _ H2);
  clear H2; intros b (Hb, Hb1); exists b; auto.
intros (b, (Hb1, Hb2)); rewrite Hb1; clear Hb1.
apply fold_insert1 with (f := (fun p => L (Pos x y) p)); auto.
Qed.

(******************************************************************************)
(*            Ordered                                                         *)
(******************************************************************************)

(* An ordered clauses *)
Definition ordered_clause (c : clause) := olist _ lit_test c.

Definition ordered (cs : clauses) :=
  forall n c, In (n, c) cs -> ordered_clause c.

(*  lit_insert is ordered *)
Theorem lit_insert_ordered c l :
  ordered_clause c -> ordered_clause (lit_insert l c).
Proof.
unfold ordered_clause, lit_insert; intros H; apply insert_olist; auto.
- exact lit_test_trans.
- intros; apply lit_test_anti_sym.
Qed.

(* Specification of clause_merge *)
Theorem clause_merge_ordered c1 c2 : 
  ordered_clause c1 -> ordered_clause c2 -> ordered_clause (clause_merge c1 c2).
Proof.
intros H1 H2; unfold ordered_clause, clause_merge; apply merge_olist; auto.
- exact lit_test_trans.
- intros; apply lit_test_anti_sym.
- exact lit_test_exact.
Qed.

Theorem lit_rm_ordered c1 c2 :
  ordered_clause c1 -> ordered_clause c2 -> ordered_clause (lit_rm c1 c2).
Proof.
unfold ordered_clause, lit_rm; intros H H1; apply rm_olist; auto.
exact lit_test_trans.
Qed.

Theorem clause_insert_ordered c cs :
  ordered_clause c -> ordered cs -> ordered (clause_insert c cs).
Proof.
intros H H1 n1 c1 H2.
case (clause_insert_in (n1, c1) c cs); auto.
intros tmp _; case tmp; clear tmp; auto; intros H3.
- injection H3; intros; subst; auto.
- apply (H1 n1 c1); auto.
Qed.

Theorem clauses_update_ordered l c cs :
  ordered_clause c -> ordered cs -> ordered (clauses_update l c cs).
Proof with auto with datatypes.
elim cs; simpl...
intros (n1, c1) cs1 Rec H H1; case (lit_is_in l c1).
- apply Rec...
  intros n2 c2 H2; apply (H1 n2 c2)...
- apply clause_insert_ordered...
  + apply lit_rm_ordered...
    apply (H1 n1 c1)...
  + apply Rec...
    intros n2 c2 H2; apply (H1 n2 c2)...
Qed.

Theorem gen_row_ordered i z : ordered_clause (gen_row i z).
Proof.
unfold gen_row; elim indexes; simpl; auto.
- red; apply olist_nil.
- intros a s1 Rec.
  unfold ordered_clause, lit_insert; apply insert_olist; auto.
  + exact lit_test_trans.
  + intros; apply lit_test_anti_sym.
Qed.

Theorem gen_column_ordered j z : ordered_clause (gen_column j z).
Proof.
unfold gen_column; elim indexes; simpl; auto.
- red; apply olist_nil.
- intros a s1 Rec.
  unfold ordered_clause, lit_insert; apply insert_olist; auto.
  + exact lit_test_trans.
  + intros; apply lit_test_anti_sym.
Qed.

Theorem gen_rect_ordered i z : ordered_clause (gen_rect i z).
Proof.
unfold gen_rect; elim cross; simpl; auto.
- red; apply olist_nil.
- intros a s1 Rec.
  unfold ordered_clause, lit_insert; apply insert_olist; auto.
  + exact lit_test_trans.
  + intros; apply lit_test_anti_sym.
Qed.

Theorem gen_cell_ordered p : ordered_clause (gen_cell p).
Proof.
unfold gen_cell; revert p; elim ref_list; simpl.
- intros; red; apply olist_nil.
- intros a l Rec p; apply lit_insert_ordered; auto.
Qed.

Theorem fold_clause_insert_ordered (A : Set) (f : A -> clause) l1 l2 :
  (forall l, ordered_clause (f l)) -> ordered l1 ->
  ordered (fold_right (fun p l => clause_insert (f p) l) l1 l2).
Proof.
intros H; generalize l1; elim l2; simpl; auto; clear l1 l2.
intros a l2 Rec l1 H1.
apply clause_insert_ordered; auto.
Qed.

Theorem all_cell_ordered : ordered all_cell.
Proof.
unfold all_cell.
apply fold_clause_insert_ordered; auto.
- intros l; apply gen_cell_ordered.
- red; simpl; intros _ c H; case H.
Qed.

Theorem init_c_ordered : ordered init_c.
Proof.
unfold init_c.
apply fold_clause_insert_ordered with 
    (f := (fun iz => gen_row (fst iz) (snd iz))); auto.
intros; apply gen_row_ordered.
apply fold_clause_insert_ordered with
    (f := (fun iz => gen_column (fst iz) (snd iz))); auto.
- intros; apply gen_column_ordered.
- apply fold_clause_insert_ordered with
    (f := (fun iz => gen_rect (fst iz) (snd iz))); auto.
  + intros; apply gen_rect_ordered.
  + apply all_cell_ordered.
Qed.

Theorem anti_literals_ordered p : ordered_clause (anti_literals p).
Proof.
destruct p as ((x, y), z); simpl.
repeat apply clause_merge_ordered; auto;
    generalize (lit_rm_ordered (L (Pos x y) z :: nil)); simpl;
      intros tmp; apply tmp; clear tmp; auto;
        try (red; apply olist_one).
- apply gen_row_ordered.
- apply gen_column_ordered.
- apply gen_rect_ordered.
- apply gen_cell_ordered.
Qed.

Theorem gen_init_clauses_ordered s : ordered (gen_init_clauses s).
Proof.
unfold gen_init_clauses, gen_init_clauses_aux.
cut (ordered init_c).
2: apply init_c_ordered; auto.
generalize (Pos 0 0) init_c.
elim s; auto; clear s; auto.
intros a s1 Rec p; case (In_dec eq_nat a ref_list); auto.
intros H c H1; apply Rec; auto.
apply clauses_update_ordered; auto.
apply anti_literals_ordered.
Qed.

(******************************************************************************)
(*            Correctness  with order                                         *)
(******************************************************************************)

(* Specification of lit_is_in *)
Theorem lit_is_in_correct l c : 
  ordered_clause c -> if lit_is_in l c then In l c else ~ In l c.
Proof.
intros H; unfold lit_is_in; apply is_in_correct; auto.
- exact lit_test_trans.
- intros; apply lit_test_anti_sym.
- exact lit_test_exact.
Qed.

(* Specification of lit_rm *)
Theorem lit_rm_in l c1 c2 :
  ordered_clause c1 -> ordered_clause c2 ->
  In l (lit_rm c1 c2) <-> ~In l c1 /\ In l c2.
Proof.
unfold ordered_clause, lit_rm; intros H H1; split; intros H2.
- split.
  + contradict H2; apply rm_not_in; auto.
    * exact lit_test_trans.
    * intros; apply lit_test_anti_sym; auto.
    * exact lit_test_exact.
  + apply (rm_incl _ lit_test c1 c2 l); auto.
- case H2; clear H2; intros H2 H3.
  apply rm_in; auto.
  exact lit_test_exact.
Qed.

Theorem anti_literals_in p z1 z2 :
  In z2 ref_list -> z2 <> z1 -> In (L p z2) (anti_literals (L p z1)).
Proof.
destruct p as (x1, y1); intros H H1.
unfold anti_literals.
repeat 
  match goal with
  |- In ?X (clause_merge ?Y ?Z) =>
    case (clause_merge_in X Y Z); intros _ tmp; apply tmp; clear tmp; right
  end.
match goal with
|- In ?X (lit_rm ?Y ?Z) =>
  case (lit_rm_in X Y Z); try (intros _ tmp; apply tmp; clear tmp)
end.
- red; apply olist_one.
- apply gen_cell_ordered.
- split.
  + simpl; intros [H2 | H2]; case H1; try injection H2; auto.
    case H2.
  + case (gen_cell_correct (L (Pos x1 y1) z2) x1 y1); auto;
      intros _ tmp; apply tmp; clear tmp.
    exists z2; auto.
Qed.

(******************************************************************************)
(*            Validity                                                        *)
(******************************************************************************)

(* A valid lit *)
Definition valid_lit l s :=
  match l with 
  | L p z => ~ In (get p s) ref_list /\ valid_pos p /\ In z ref_list
  end.

(* A valid clause *)
Definition valid_clause c s := forall l, In l c -> valid_lit l s.

(* Valid list of clauses *)
Definition valid (cs : clauses) s :=
  forall n c, In (n, c) cs -> valid_clause c s.

(* Validity of literals works the other way than refinement *)
Theorem valid_lit_refine l s1 s2 :
  refine s1 s2 -> valid_lit l s2 -> valid_lit l s1.
Proof.
destruct l as (p, z); intros  H (H0, (H1, H2)); split; auto.
contradict H0.
case H; intros _ (_, H3); rewrite <- H3; auto.
Qed.

(* Validity works the other way than refinement *)
Theorem valid_refine cs s1 s2 : refine s1 s2 -> valid cs s2 -> valid cs s1.
Proof.
intros H H1 n c Hn l Hl.
apply valid_lit_refine with (1 := H).
apply (H1 n c); auto.
Qed.

(* Updating a valid clause gives a valid clause *)
Theorem valid_update p z c s : 
  valid_clause c s -> valid_pos p ->
  (forall z, In z ref_list -> ~ In (L p z) c) -> valid_clause c (update p z s).
Proof.
intros H H1 H2 l Hl.
generalize (H l Hl) Hl; clear H Hl.
case l; simpl.
intros p1 z1 (H3, (H4, H5)) H6; split; auto.
rewrite update_diff_get; auto.
intro tmp; subst; case (H2 z1); auto.
Qed.

Theorem lit_insert_valid l c s :
  valid_lit l s -> valid_clause c s -> valid_clause (lit_insert l c) s.
Proof.
destruct l as (p, z); simpl.
intros (H1, (H2, H3)) H4 l1; case l1; simpl.
intros p1 z1 H5.
unfold lit_insert in H5; case insert_inv with (1 := H5); auto.
- intros tmp; injection tmp; intros; subst; clear tmp; auto.
- intros H6; apply (H4 (L p1 z1) H6).
Qed.

Theorem clause_merge_valid c1 c2 s :
  valid_clause c1 s -> valid_clause c2 s -> valid_clause (clause_merge c1 c2) s.
Proof.
intros H H1 l Hl.
case (clause_merge_in l c1 c2); auto.
intros tmp _; case tmp; auto.
Qed.

Theorem lit_rm_valid c1 c2 s :
  ordered_clause c1 -> ordered_clause c2 ->
  valid_clause c2 s -> valid_clause (lit_rm c1 c2) s.
Proof.
intros H H1 H2 l H3.
case (lit_rm_in l c1 c2); auto.
intros tmp _; case tmp; auto.
Qed.

Theorem clause_insert_valid c cs s :
  valid_clause c s -> valid cs s -> valid (clause_insert c cs) s.
Proof.
intros H H1 n1 c1 Hc1.
case (clause_insert_in (n1, c1) c cs); auto.
intros tmp _; case tmp; clear tmp; auto; intros H2.
- injection H2; intros; subst; auto.
- apply (H1 n1 c1); auto.
Qed.

Theorem clauses_merge_valid cs1 cs2 s :
  valid cs1 s -> valid cs2 s -> valid (clauses_merge cs1 cs2) s.
Proof.
intros H H1 n1 c1 Hc1.
case (clauses_merge_in (n1, c1) cs1 cs2); auto.
intros tmp _; case tmp; clear tmp; auto; intros H2.
- apply (H n1 c1); auto.
- apply (H1 n1 c1); auto.
Qed.

Theorem clauses_update_valid p z c cs s :
  valid_lit (L p z) s -> ordered cs -> ordered_clause c ->
  (forall z1, In z1 ref_list -> z1 <> z -> In (L p z1) c) ->
  valid cs s -> valid (clauses_update (L p z) c cs) (update p z s).
Proof with auto with datatypes.
intros (H1, (H2, H3)) H4 H5 H6; generalize H4;
    elim cs; simpl; auto; clear cs H4.
- intros _ _ n1 c1 H7; case H7.
- intros (n1, c1) cs Rec H4 H7.
  generalize (lit_is_in_correct (L p z) c1);
    case (lit_is_in (L p z) c1); intros H.
  + apply Rec...
    * intros n2 c2 HH; apply (H4 n2 c2)...
    * intros n2 c2 H8; apply (H7 n2 c2)...
  + assert (E1: ordered_clause c1).
    * apply (H4 n1 c1)...
    * assert (E2: valid_clause c1 s).
      --apply (H7 n1 c1)...
      --apply clause_insert_valid...
        ++apply valid_update...
          **apply lit_rm_valid...
          **intros z1 HH; case (eq_nat z z1); intros H8; subst...
            --- intros H8; case H...
                case (lit_rm_in (L p z1) c c1)...
                intros tmp _; case tmp...
            --- intros H9; case (lit_rm_in (L p z1) c c1)...
                intros tmp _; case tmp...
        ++apply Rec...
          **intros n2 c2 H8; apply (H4 n2 c2)...
          **intros n2 c2 H8; apply (H7 n2 c2)...
Qed.

Theorem fold_clause_insert1 (A : Set) (f : A -> clause) l1 l2 a :
  In a (fold_right (fun p l => clause_insert (f p) l) l2 l1) ->
  (exists b, exists n, In b l1 /\ a = (n, f b)) \/ In a l2.
Proof.
destruct a as (n, l); generalize l2; elim l1; simpl; auto; clear l1 l2.
intros a l1 Rec l2 H1.
match goal with
| H : In ?p (clause_insert ?c ?cs) |- _ =>
  case (clause_insert_in p c cs); intros tmp _; case (tmp H); clear tmp H
end.
- intros tmp; left; exists a; exists n; injection tmp; intros; subst; auto.
- intros tmp; case (Rec l2); auto; clear tmp Rec.
  intros (b, (n1, (H1, H2))).
  left; exists b; exists n1; auto.
Qed.

Theorem valid_init_c s : length s = size * size -> empty s -> valid init_c s.
Proof with auto with arith.
unfold init_c; intros H H1 n c Hn l Hl.
case (fold_clause_insert1 _ (fun iz => gen_row (fst iz) (snd iz)))
    with (1 := Hn); clear Hn.
- intros ((x,z), (n1, (HH1, HH2))); simpl in HH2.
  injection HH2; intros; subst; clear HH2.
  case (cross1_correct (x, z)); intros tmp _;
    case (tmp HH1); clear tmp HH1.
  intros x1 (z1, (V1, (V2, V3))); injection V3; intros; subst; clear V3.
  case (gen_row_correct l x1 z1).
  intros tmp _; case (tmp Hl); clear tmp.
  intros y1 (Hl1, Hy); subst.
  repeat (split; auto); case (in_indexes x1)...
- intros Hn; case (fold_clause_insert1 _ 
                    (fun iz => gen_column (fst iz) (snd iz)))
              with (1 := Hn); clear Hn.
  + intros ((y,z), (n1, (HH1, HH2))); simpl in HH2.
    injection HH2; intros; subst; clear HH2.
    case (cross1_correct (y, z)); intros tmp _;
    case (tmp HH1); clear tmp HH1.
    intros y1 (z1, (V1, (V2, V3))); injection V3; intros; subst; clear V3.
    case (gen_column_correct l y1 z1).
    intros tmp _; case (tmp Hl); clear tmp.
    intros x1 (Hl1, Hy); subst.
    repeat (split; auto); case (in_indexes y1)...
  + intros Hn; case (fold_clause_insert1 _ 
                      (fun iz => gen_rect (fst iz) (snd iz)))
                 with (1 := Hn); clear Hn.
    * intros ((i,z), (n1, (HH1, HH2))); simpl in HH2.
      injection HH2; intros; subst; clear HH2.
      case (cross1_correct (i, z)); intros tmp _; case (tmp HH1); clear tmp HH1.
      intros i1 (z1, (V1, (V2, V3))); injection V3; intros; subst; clear V3.
      case (gen_rect_correct l i1 z1).
      --case (in_indexes i1)...
      --intros tmp _; case (tmp Hl); clear tmp.
        intros x1 (y1, (Hl1, (Hl2, Hl3))); subst.
        repeat (split; auto).
        ++unfold size.
          repeat rewrite (Nat.mul_comm h); apply mult_lt_plus...
          apply div_lt...
          case (in_indexes i1)...
        ++unfold size.
          repeat rewrite (Nat.mul_comm w); apply mult_lt_plus...
          apply mod_lt...
          apply Nat.le_lt_trans with (2 := Hl2)...
    * unfold all_cell; intros Hn; case fold_clause_insert1 with (1 := Hn); 
        clear Hn.
      ++intros ((x, y), (n1, (HH1, HH2))); simpl in HH2.
        injection HH2; intros; subst; clear HH2.
        case (cross2_correct (Pos x y)); intros tmp _;
          case (tmp HH1); clear tmp HH1.
        intros H2 H3.
        case (gen_cell_correct l x y); intros tmp _;
          case (tmp Hl); clear tmp.
        intros z (V1, V2); subst.
        repeat (split; auto).
      ++ intros HH; case HH.
Qed.

Theorem gen_init_clauses_valid s : 
  length s = size * size -> valid (gen_init_clauses s) s.
Proof with auto with arith.
revert s.
assert (Eq:
    forall s1 s p cs,
      length s = size * size -> s1 = jump (pos2n p) s -> valid_pos p ->
      ordered cs -> valid cs (prestrict p s) ->
      valid (gen_init_clauses_aux s1 p cs) s).
- intros s1; elim s1; clear s1;
    unfold gen_init_clauses_aux; lazy beta; fold gen_init_clauses_aux...
  + intros s p cs H H0 H1 H2 H3; rewrite prestrict_all in H3...
    case (Nat.le_gt_cases (length s) (pos2n p))...
    intros H4; absurd (length (jump (pos2n p) s) = length (@nil nat)).
    * generalize (length_jump _ (pos2n p) s).
      rewrite <- H0; simpl.
      intros H5; assert (Eq1: length s = pos2n p)...
      contradict H4; rewrite Eq1...
    * f_equal...
  + intros a s1; case s1; clear s1.
    * intros Rec s p cs H0 H1 H2 H3 H4.
      assert (F1: pos2n p < length s).
      --case (Nat.le_gt_cases (length s) (pos2n p)); auto; intros H5.
        rewrite (jump_too_far _ (pos2n p) s) in H1; try discriminate...
      --case (In_dec eq_nat a ref_list); intros H5.
        ++unfold gen_init_clauses_aux; lazy beta; fold gen_init_clauses_aux.
          replace s with (prestrict (next p) s).
          **rewrite prestrict_update...
            --- replace (get p s)  with a.
                +++ apply clauses_update_valid...
                    *** simpl; split...
                        rewrite prestrict_get_default...
                        apply out_not_in_refl.
                    *** apply anti_literals_ordered.
                    *** intros; apply anti_literals_in...
                +++ unfold get; rewrite <- H1...
            --- rewrite next_pos...
          **apply prestrict_all...
            case (Nat.le_gt_cases (length s) (pos2n (next p))); 
              auto; intros H6.
            rewrite (length_jump nat (pos2n p)).
            --- rewrite <- H1; simpl; rewrite next_pos...
            --- rewrite next_pos in H6...
        ++simpl.
          intros n c Hn (p1, z1) Hl; simpl.
          case (H4 n c Hn (L p1 z1))...
          intros U1 (U2, U3); split...
          case (Nat.le_gt_cases (pos2n p) (pos2n p1)); intros V1.
          --- unfold get; rewrite <-(Nat.sub_add (pos2n p) (pos2n p1));
                  auto with arith.
              rewrite Nat.add_comm, jump_add; rewrite <- H1.
              case (pos2n p1 - pos2n p); simpl...
              intros n1; rewrite jump_nil; simpl; apply out_not_in_refl.
          --- rewrite <- (prestrict_get s p1 p)...
    * intros b s1 Rec s p cs H0 H1 H2 H3 H4.
      assert (F0: b :: s1 = jump (pos2n (next p)) s).
      --rewrite next_pos.
        replace (S (pos2n p)) with ((pos2n p) + 1)...
        ++rewrite jump_add; rewrite <- H1; simpl...
        ++rewrite Nat.add_comm...
      --assert (F1: pos2n (next p) < length s).
        ++case (Nat.le_gt_cases (length s) (pos2n (next p))); auto; intros H5.
          rewrite (jump_too_far _ (pos2n (next p)) s) in F0; try discriminate...
        ++case (In_dec eq_nat a ref_list); intros H5.
          **apply Rec...
            --- apply valid_pos_next...
                rewrite <- H0...
            --- apply clauses_update_ordered...
                apply anti_literals_ordered.
            --- rewrite prestrict_update...
                replace (get p s)  with a.
                +++ apply clauses_update_valid...
                    *** simpl; split...
                        rewrite prestrict_get_default...
                        apply out_not_in_refl.
                    *** apply anti_literals_ordered.
                    *** intros; apply anti_literals_in...
                +++ unfold get; rewrite <- H1...
          **apply Rec...
            --- apply valid_pos_next...
                 rewrite <- H0...
            --- intros n c Hn (p1, z1) Hl; simpl.
                case (H4 n c Hn (L p1 z1))...
                intros U1 (U2, U3); split...
                case (Nat.le_gt_cases (pos2n (next p)) (pos2n p1)); intros V1.
                +++ rewrite prestrict_get_default...
                    apply out_not_in_refl.
                +++ rewrite prestrict_get...
                    case (Lt.le_lt_or_eq_stt (pos2n p1) (pos2n p));
                        try intros V2.
                    *** rewrite next_pos in V1...
                    *** rewrite prestrict_get in U1...
                    *** assert (p1 = p); try (subst p1).
                      ----apply valid_pos_eq...
                      ----unfold get; rewrite <- H1...
-intros s Hs.
  case (Lt.le_lt_or_eq_stt 0 size); auto with arith; intros V1.
  + unfold gen_init_clauses; apply Eq; simpl...
    * apply init_c_ordered.
    * destruct s...
      --simpl in Hs.
        lia.
      --rewrite prestrict_0; apply valid_init_c.
        ++rewrite <- Hs; apply mk_0_length.
        ++apply empty_mk_0.
  + generalize Hs.
    rewrite <- V1; case s; simpl...
    * intros _; unfold gen_init_clauses; simpl.
      apply valid_init_c.
      --rewrite <- V1...
      --apply empty_nil.
    * intros; discriminate.
Qed.

(******************************************************************************)
(*            Satisfiability                                                  *)
(******************************************************************************)

(* A state satisfies a literal, if the corresponding cell c
   contains the value in the literal
 *)
Definition lit_sat l s := match l with L p z => get p s = z end.

(* A state satisfies a clause if it satisfies at least one literal *)
Definition clause_sat c s := exists l, In l c /\ lit_sat l s.

(* A state satisfies a list of clauses if it satisfies
   all its clauses
 *)
Definition sat (cs : clauses) s := forall n c, In (n, c) cs -> clause_sat c s.

(* Satisifability is preserved by refinement *)
Theorem sat_refine cs s1 s2 :
  refine s1 s2 -> valid cs s1 -> sat cs s1 -> sat cs s2.
Proof.
intros H1 H2 H3 n c Hn.
case (H3 n c Hn); intros (p, z) (Hl1, Hl2); simpl in Hl2.
exists (L p z); split; simpl; auto.
case H1; auto.
intros H4 (H5, H6); rewrite <- H6; auto.
- case (H2 n c Hn (L p z) Hl1); intuition.
- rewrite Hl2; case (H2 n c Hn (L p z) Hl1); intuition.
Qed.

Theorem lit_rm_sat l1 l2 s :
  ordered_clause l1 -> ordered_clause l2 ->
  (forall ll, In ll l1 -> ~ lit_sat ll s) ->
  (clause_sat l2 s <-> clause_sat (lit_rm l1 l2) s).
Proof.
intros O1 O2 H; split; intros (ll,(H2, H3)); exists ll;
    split; auto.
- case (lit_rm_in ll l1 l2); auto; intros _ H4; apply H4; auto.
  split; auto.
  intros H5; case (H ll); auto.
- case (lit_rm_in ll l1 l2); auto; intros H4 _; case H4; auto.
Qed.

Theorem clause_insert_sat v l s : 
  sat (clause_insert v l) s <-> clause_sat v s /\ sat l s.
Proof.
split.
- intros H1; split.
  + apply (H1 (length v) v).
    case (clause_insert_in (length v, v) v l); auto.
  + intros n1 v1 H2.
    apply (H1 n1 v1).
    case (clause_insert_in (n1, v1) v l); auto.
- intros (H1, H2) n1 v1 H3.
  case (clause_insert_in (n1, v1) v l); auto.
  intros H4 _; case H4; clear H4; try intros H4; auto.
  + injection H4; intros; subst; auto.
  + apply (H2 n1 v1); auto.
Qed.

Theorem clauses_merge_sat cs1 cs2 s :
  sat (clauses_merge cs1 cs2) s <-> sat cs1 s /\ sat cs2 s.
Proof.
split; [intros H; split | intros (H, H1)].
- intros n c H1; apply (H n c).
  case (clauses_merge_in (n, c) cs1 cs2); auto.
- intros n c H1; apply (H n c).
  case (clauses_merge_in (n, c) cs1 cs2); auto.
- intros n c H2.
  case (clauses_merge_in (n, c) cs1 cs2); auto.
  intros tmp _; case tmp; auto; clear tmp; intros H3.
  + apply (H n c); auto.
  + apply (H1 n c); auto.
Qed.

Theorem clauses_update_sat l c cs s :
  ordered_clause c -> lit_sat l s -> ordered cs -> 
  sat (clauses_update l c cs) s -> sat cs s.
Proof.
intros H1 H2 H3; generalize H3; elim cs; simpl; auto; clear H3.
intros (n1, c1) cs1 Rec H3.
assert (F1: ordered_clause c1).
- apply (H3 n1); auto with datatypes.
- generalize (lit_is_in_correct l c1 F1).
  case (lit_is_in l c1); auto; intros H4 H5.
  + intros n2 c2; simpl; intros [Hn2 | Hn2].
    * injection Hn2; intros; subst; clear Hn2.
      exists l; split; auto.
    * assert (F2: sat cs1 s).
      --apply Rec; auto.
        intros n3 c3 Hn3; apply (H3 n3); auto with datatypes.
      --apply (F2 n2); auto.
  + match type of H5 with 
    | sat (clause_insert ?X ?Y) ?Z =>
      case (clause_insert_sat X Y Z); intros tmp _;
      generalize (tmp H5); clear tmp H5; intros ((l1,(H6, H7)),H8)
    end.
    assert (F2: sat cs1 s).
    * apply Rec; auto.
      intros n3 c3 Hn3; apply (H3 n3); auto with datatypes.
    * intros n2 c2; simpl; intros [Hn2 | Hn2].
      --injection Hn2; intros; subst; clear Hn2.
        exists l1; split; auto.
        case (lit_rm_in l1 c c2); intuition.
      --apply (F2 n2); auto with datatypes.
Qed.

Theorem clauses_update_sat_rev l c cs s : 
  ordered_clause c -> lit_sat l s -> ordered cs -> 
  (forall l, In l c -> ~ lit_sat l s) ->
  sat cs s -> sat (clauses_update l c cs) s.
Proof.
intros H1 H2 H3 H4; generalize H3; elim cs; simpl; auto; clear H3.
intros (n1, c1) cs1 Rec H3 H5.
assert (F1: ordered_clause c1).
- apply (H3 n1); auto with datatypes.
- generalize (lit_is_in_correct l c1 F1).
  case (lit_is_in l c1); auto; intros H6; auto.
  + apply Rec; auto.
    * intros n3 c3 Hn3; apply (H3 n3); auto with datatypes.
    * intros n2 c2 Hn2; apply (H5 n2); auto with datatypes.
  + match goal with
    |- context[sat (clause_insert ?X ?Y) ?Z] =>
      case (clause_insert_sat X Y Z); intros _ U2; apply U2; clear U2
    end.
    split.
    * case (lit_rm_sat c c1 s); auto.
      intros H7 _; apply H7; clear H7.
      apply (H5 n1 c1); auto with datatypes.
    * apply Rec.
      --intros n3 c3 Hn3; apply (H3 n3); auto with datatypes.
      --intros n2 c2 Hn2; apply (H5 n2 c2); auto with datatypes.
Qed.

Theorem gen_row_sat i z s :
  length s = size * size -> i < size ->
  clause_sat (gen_row i z) s <-> In z (row i s).
Proof.
intros H Hi.
assert (H0: length (row i s) = size); try apply length_row; auto.
split.
- intros (l, (H1, H2)).
  case (gen_row_correct l i z); intros tmp _; case tmp; auto; clear tmp.
  intros j (H3, H4).
  case (in_ex_nth _ z 0 (row i s)); intros _ tmp; apply tmp; clear tmp.
  subst; exists j; split; auto.
  + rewrite H0; auto.
  + rewrite <- get_row; auto.
- intros H1.
  case (in_ex_nth _ z 0 (row i s)); intros tmp _; case tmp; auto; clear tmp.
  intros j (H2, H3).
  rewrite <- get_row in H3; auto.
  + exists (L (Pos i j) z); split; auto.
    * case (gen_row_correct (L (Pos i j) z) i z); intros _ tmp; apply tmp;
        clear tmp.
      exists j; split; auto.
      rewrite <- H0; auto.
    * red; apply sym_equal; auto.
  + rewrite <- H0; auto.
Qed.

Theorem gen_column_sat j z s :
  length s = size * size -> j < size ->
  clause_sat (gen_column j z) s <-> In z (column j s).
Proof.
intros H H0.
assert (Eq1: length (column j s) = size); try apply length_column; auto.
split.
- intros (l, (H1, H2)).
  case (gen_column_correct l j z); intros tmp _; case tmp; auto; clear tmp.
  intros i (H3, H4).
  case (in_ex_nth _ z 0 (column j s)); intros _ tmp; apply tmp; clear tmp.
  subst; exists i; split; auto.
  + rewrite Eq1; auto.
  + rewrite <- get_column; auto.
- intros H1.
  case (in_ex_nth _ z 0 (column j s)); intros tmp _; case tmp; auto; clear tmp.
  intros i (H2, H3).
  rewrite <- get_column in H3; auto.
  + exists (L (Pos i j) z); split; auto.
    case (gen_column_correct (L (Pos i j) z) j z); intros _ tmp; apply tmp;
      clear tmp.
    exists i; split; auto.
    * rewrite <- Eq1; auto.
    * red; apply sym_equal; auto.
  + rewrite Eq1 in H2; auto.
Qed.

Theorem gen_rect_sat i z s :
  length s = size * size -> i < size ->
  clause_sat (gen_rect i z) s <-> In z (rect i s).
Proof with auto with arith.
intros H H0.
assert (V1: 0 < h) by (generalize H0; unfold size; lia).
assert (V2: 0 < w) by (generalize H0; unfold size; lia).
generalize mod_lt div_lt; intros aux1 aux2.
split.
- intros (l, (Hl1, Hl2)).
  case (gen_rect_correct l i z)...
  intros tmp _; case (tmp Hl1); auto; clear tmp Hl1.
  intros i1 (j1, (H1, (H2, H3))).
  subst; simpl in Hl2.
  rewrite get_rect in Hl2.
  + assert (Eq: div (h * div i h + i1) h * h + div (w * mod i h + j1) w = i).
    * repeat rewrite div_mult_comp...
      rewrite (div_is_0 i1 h)...
      rewrite (div_is_0 j1 w)...
      pose proof (div_mod_correct i h).
      lia.
    * subst z; rewrite Eq; apply nth_In.
      apply Nat.le_lt_trans with ((h - 1) * w + (w - 1))...
      --apply Nat.add_le_mono.
        ++apply Nat.mul_le_mono_r...
          match goal with 
          |- mod ?X ?Y <= ?T =>
            generalize (mod_lt X Y V1); auto with arith
          end.
          case h; auto with arith; intros; simpl minus;
              repeat rewrite Nat.sub_0_r...
        ++match goal with
          |- mod ?X ?Y <= ?T =>
             generalize (mod_lt X Y V2); auto with arith
          end.
          case w; auto with arith; intros; simpl minus;
              repeat rewrite Nat.sub_0_r...
      --rewrite length_rect...
        replace size with ((h - 1) * w + w)...
        pattern w at 2; rewrite <- Nat.mul_1_l; rewrite <- Nat.mul_add_distr_r.
        rewrite Nat.sub_add...
  + unfold size; repeat rewrite (Nat.mul_comm h); apply mult_lt_plus...
  + unfold size; repeat rewrite (Nat.mul_comm w); apply mult_lt_plus...
- intros H1; red.
  case (in_ex_nth _ z 0 (rect i s)); intros tmp _ ; case (tmp H1);
    clear tmp H1.
  intros j (Hj1, Hj2).
  exists (L (Pos (div i h * h + div j w) (mod i h * w  + mod j w)) z); simpl.
  split.
  + match goal with
    |- In ?l (gen_rect ?i ?z) =>
      case (gen_rect_correct l i z); auto; intros _ tmp; apply tmp; clear tmp
    end.
    exists (div j w); exists (mod j w); repeat split...
    * f_equal.
      f_equal.
      --rewrite (Nat.mul_comm h)...
      --rewrite (Nat.mul_comm w)...
    * apply div_lt; rewrite (Nat.mul_comm w); rewrite length_rect in Hj1...
  + rewrite Hj2.
    rewrite get_rect.
    * f_equal; auto; [idtac | f_equal]...
      --rewrite length_rect in Hj1...
        rewrite (Nat.mul_comm (div i h)); rewrite (Nat.mul_comm (mod i h));
          repeat rewrite mod_mult_comp...
        rewrite mod_small.
        ++rewrite mod_small.
          **apply sym_equal; apply div_mod_correct...
          **apply mod_lt...
        ++apply div_lt...
          rewrite (Nat.mul_comm w)...
      --rewrite (Nat.mul_comm (div i h)); rewrite (Nat.mul_comm (mod i h));
        repeat rewrite div_mult_comp...
        rewrite (fun x y => div_is_0 (div x y))...
        ++rewrite (fun x y => div_is_0 (mod x y))...
          pose proof (div_mod_correct i h).
          lia.
        ++apply div_lt...
          rewrite (Nat.mul_comm w)...
          rewrite length_rect in Hj1...
    * unfold size; rewrite (Nat.mul_comm h); apply mult_lt_plus...
      apply div_lt...
      rewrite (Nat.mul_comm w); rewrite length_rect in Hj1...
    * unfold size; apply mult_lt_plus...
Qed.

Theorem gen_cell_sat p s : 
  valid_pos p -> (clause_sat (gen_cell p) s <-> In (get p s) ref_list).
Proof.
destruct p as (x, y); intros (H, H0); split; simpl.
- intros (((x1, y1), z1), (Hj1, Hj2)); simpl in Hj2.
  match goal with
  | H: In ?l (gen_cell (Pos ?x ?y)) |- _ =>
    case (gen_cell_correct l x y); auto;
    intros tmp _; case (tmp H); clear tmp H; auto
  end.
  intros z2 (Hz1, Hz2); injection Hz1.
  intros; subst; auto.
- intros H1.
  exists (L (Pos x y) (get (Pos x y) s)); split; auto.
  match goal with
  | |- In ?l (gen_cell (Pos ?x ?y)) =>
    case (gen_cell_correct l x y); auto;
      intros _ tmp; apply tmp; clear tmp
  end.
  + exists (get (Pos x y) s); auto.
  + red; auto.
Qed.

Theorem fold_clause_insert2 (A : Set) (f : A -> clause) l1 l2 a :
  In a l2 -> In a (fold_right (fun p l => clause_insert (f p) l) l2 l1).
Proof.
revert l2; elim l1; simpl; auto; clear l1.
intros b l1 Rec l2 H1.
match goal with
| |- In ?p (clause_insert ?c ?cs) =>
  case (clause_insert_in p c cs); intros _ tmp; apply tmp; clear tmp; auto
end.
Qed.

Theorem fold_clause_insert3 (A : Set) (f : A -> clause) l1 l2 a :
  In a l1 -> 
  In (length (f a), (f a)) 
     (fold_right (fun p l => clause_insert (f p) l) l2 l1).
Proof.
revert l2; elim l1; simpl; auto; clear l1.
intros l2 H; case H.
intros b l1 Rec l2 [H | H]; subst;
  match goal with
  | |- In ?p (clause_insert ?c ?cs) =>
    case (clause_insert_in p c cs); intros _ tmp; apply tmp; clear tmp; auto
  end.
Qed.

Theorem all_cell_sat s : 
  sat all_cell s <-> forall p, valid_pos p -> In (get p s) ref_list.
Proof.
unfold all_cell, sat; split.
- intros H (x, y) (H1, H2).
  case (H (length (gen_cell (Pos x y))) (gen_cell (Pos x y))).
  + apply fold_clause_insert3; auto.
    case (cross2_correct (Pos x y)); intros _ tmp; apply tmp; clear tmp; auto.
    split; auto.
  + intros l (Hl1, Hl2).
    case (gen_cell_correct l x y); auto.
    intros tmp _; case tmp; auto; clear tmp Hl1.
    intros z (Hz1, Hz2); subst; simpl in Hl2.
    rewrite Hl2; auto.
- intros H n c H1.
  case fold_clause_insert1 with (1 := H1); clear H1.
  + intros ((x, y),  (n1, (H2, H3))); injection H3; intros Eq1 E2; clear H3.
    subst.
    case (cross2_correct (Pos x y)); intros tmp _; case (tmp H2);
    clear tmp H2; intros H3 H4.
    exists (L (Pos x y) (get (Pos x y) s)); split.
    * case (gen_cell_correct (L (Pos x y) (get (Pos x y) s)) x y); auto.
      intros H1 H2; apply H2; clear H1 H2; simpl; auto.
      exists (get (Pos x y) s); split; auto.
      apply H; split; auto.
    * simpl; auto.
  + simpl; intros H1; case H1.
Qed.

Theorem init_c_sat s :
  length s = size * size ->
  sat init_c s <->
    (forall i, i < size -> incl ref_list (row i s)) /\
    (forall i, i < size -> incl ref_list (column i s)) /\
    (forall i, i < size -> incl ref_list (rect i s)) /\
    (forall p, valid_pos p -> In (get p s) ref_list).
Proof with auto.
intros H0; unfold init_c; split.
intros H; repeat split.
- intros i Hi z Hz.
  case (gen_row_sat i z s); auto; intros tmp _; apply tmp; clear tmp.
  case (H (length (gen_row i z)) (gen_row i z)); auto; clear H.
  + replace (gen_row i z) with
      ((fun iz => gen_row (fst iz) (snd iz)) (i,z))...
    apply fold_clause_insert3 with
      (f := (fun iz => gen_row (fst iz) (snd iz))); simpl...
    case (cross1_correct (i, z)); auto; intros _ tmp; apply tmp; clear tmp.
    exists i; exists z; repeat split; simpl...
    case (in_indexes i)...
  + intros l (Hl1, Hl2); exists l...
- intros i Hi z Hz.
  case (gen_column_sat i z s); auto; intros tmp _; apply tmp; clear tmp.
  case (H (length (gen_column i z)) (gen_column i z)); auto; clear H.
  + apply fold_clause_insert2 with
      (f := (fun iz => gen_row (fst iz) (snd iz)))...
    replace (gen_column i z) with
      ((fun iz => gen_column (fst iz) (snd iz)) (i,z))...
    apply fold_clause_insert3 with
      (f := (fun iz => gen_column (fst iz) (snd iz))); simpl...
    case (cross1_correct (i, z)); auto; intros _ tmp; apply tmp; clear tmp.
    exists i; exists z; repeat split; simpl...
    case (in_indexes i)...
  + intros l (Hl1, Hl2); exists l...
- intros i Hi z Hz.
  case (gen_rect_sat i z s); auto; intros tmp _; apply tmp; clear tmp.
  case (H (length (gen_rect i z)) (gen_rect i z)); auto; clear H.
  + apply fold_clause_insert2 with
      (f := (fun iz => gen_row (fst iz) (snd iz)))...
    apply fold_clause_insert2 with
      (f := (fun iz => gen_column (fst iz) (snd iz)))...
    replace (gen_rect i z) with
      ((fun iz => gen_rect (fst iz) (snd iz)) (i,z))...
    apply fold_clause_insert3 with
      (f := (fun iz => gen_rect (fst iz) (snd iz))); simpl...
    case (cross1_correct (i, z)); auto; intros _ tmp; apply tmp; clear tmp.
    exists i; exists z; repeat split; simpl...
    case (in_indexes i)...
  + intros l (Hl1, Hl2); exists l...
- case (all_cell_sat s); auto; intros tmp _; apply tmp; clear tmp.
  intros n c H1.
  case (H n c)...
  + apply fold_clause_insert2 with
      (f := (fun iz => gen_row (fst iz) (snd iz)))...
    apply fold_clause_insert2 with
      (f := (fun iz => gen_column (fst iz) (snd iz)))...
    apply fold_clause_insert2 with
      (f := (fun iz => gen_rect (fst iz) (snd iz)))...
  + intros l (Hl1, Hl2); exists l...
- intros (H1, (H2, (H3, H4))).
  intros n c Hn.
  match goal with
  | H : In ?X (fold_right ?Y ?Z ?T) |- _ =>
    case (fold_clause_insert1 _ (fun iz => gen_row (fst iz) (snd iz)) _ _ _ Hn);
    clear H
  end.
  + intros ((i, z), (n1, (Hn1, Hn2))).
    injection Hn2; clear Hn2; intros; subst.
    case (cross1_correct (i, z))...
    intros tmp _; case tmp; auto; clear tmp Hn1.
    intros i1 (z1, (V1, (V2, V3))); injection V3; intros; subst; clear V3.
    case (gen_row_sat i1 z1 s)...
    * case (in_indexes i1)...
    * intros _ tmp; apply tmp; clear tmp.
      apply H1...
      case (in_indexes i1)...
  + intros H;
    match goal with
    | H : In ?X (fold_right ?Y ?Z ?T) |- _ =>
      case (fold_clause_insert1 _ (fun iz => 
                                     gen_column (fst iz) (snd iz)) _ _ _ H);
      clear H
    end.
    * intros ((i, z), (n1, (Hn1, Hn2))).
      injection Hn2; clear Hn2; intros; subst.
      case (cross1_correct (i, z))...
      intros tmp _; case tmp; auto; clear tmp Hn1.
      intros i1 (z1, (V1, (V2, V3))); injection V3; intros; subst; clear V3.
      case (gen_column_sat i1 z1 s)...
      --case (in_indexes i1)...
      --intros _ tmp; apply tmp; clear tmp.
        apply H2...
        case (in_indexes i1)...
    * intros H;
      match goal with
      | H : In ?X (fold_right ?Y ?Z ?T) |- _ =>
        case (fold_clause_insert1 _ (fun iz => 
                                        gen_rect (fst iz) (snd iz)) _ _ _ H);
        clear H
      end.
      --intros ((i, z), (n1, (Hn1, Hn2))).
        injection Hn2; clear Hn2; intros; subst.
        case (cross1_correct (i, z))...
        intros tmp _; case tmp; auto; clear tmp Hn1.
        intros i1 (z1, (V1, (V2, V3))); injection V3; intros; subst; clear V3.
        case (gen_rect_sat i1 z1 s)...
        ++case (in_indexes i1)...
        ++intros _ tmp; apply tmp; clear tmp.
          apply H3...
          case (in_indexes i1)...
      --intros H; case (all_cell_sat s).
        intros _ tmp; apply (tmp H4 n c)...
Qed.

Theorem rect_aux1 x y :
  x < size -> y < size -> div x h * h + div y w < size.
Proof.
intros H H1; unfold size; rewrite (Nat.mul_comm h); apply mult_lt_plus.
- apply div_lt; auto.
- apply div_lt; auto.
  rewrite  Nat.mul_comm; auto.
Qed.

Theorem rect_aux2 x1 x2 y1 y2 :
  y1 < size -> y2 < size ->
  mod x1 h * w + mod y1 w = mod x2 h * w + mod y2 w ->
  div x1 h * h + div y1 w = div x2 h * h + div y2 w -> x1 = x2 /\ y1 = y2.
Proof with auto with arith.
intros V1 V2 H1 H2.
assert (U1: 0 < h).
- generalize V1; unfold size; case h; simpl...
  intros tmp; contradict tmp...
- assert (U2: 0 < w).
  + generalize V1; unfold size; case w; simpl...
    rewrite Nat.mul_0_r; intros tmp; contradict tmp...
  + assert (Eq1: mod x1 h = mod x2 h).
    * apply lexico_mult with (3 := H1); apply mod_lt...
    * assert (Eq2: div x1 h = div x2 h).
      --apply lexico_mult with (3 := H2); apply div_lt; rewrite  Nat.mul_comm...
      --split; [ rewrite (div_mod_correct x1 h);
                 try rewrite (div_mod_correct x2 h) |
                 rewrite (div_mod_correct y1 w);
                 try rewrite (div_mod_correct y2 w)]...
         replace (div y1 w) with (div y2 w)...
         ++f_equal...
           apply Nat.add_cancel_l with (mod x1 h * w).
           pattern (mod x1 h) at 2; rewrite Eq1...
         ++apply Nat.add_cancel_l with (div x1 h * h).
           pattern (div x1 h) at 1; rewrite Eq2...
Qed.

Theorem anti_literals_sat p z s :
  sudoku s -> valid_pos p -> get p s = z -> 
  ~ clause_sat (anti_literals (L p z)) s.
Proof with auto with arith.
generalize ref_list_ulist; intros Eq1.
destruct p as (x, y); simpl; intros H1 (U1, U2) H2 (l, (H3, H4)).
assert (U3: 0 < h).
- generalize U1; unfold size; case h; simpl...
  intros tmp; contradict tmp...
- assert (U4: 0 < w).
  + generalize U1; unfold size; case w; simpl...
    rewrite Nat.mul_0_r; intros tmp; contradict tmp...
  + generalize div_lt; intros U5.
    generalize mod_lt; intros U6.
    repeat match goal with
           | H: In ?X (clause_merge ?Y ?Z) |- _  =>
             case (clause_merge_in X Y Z); intros tmp _; case (tmp H);
             clear tmp H; auto; intros H
           end.
    * case H1; clear H1; intros V1 (V2, _).
      case (gen_row_correct l x z); intros tmp _; case tmp; auto; clear tmp.
      --apply (rm_incl _ lit_test) with
            (l1 := L (Pos x y) z::nil)
            (l2 := gen_row x z)...
      --intros y1 (H5, H6); subst l.
        simpl in H4; absurd (y = y1).
        ++intros H7; apply (rm_not_in _ lit_test) with (a := L (Pos x y) z)
                                               (l1 := L (Pos x y) z::nil)
                                               (l2 := gen_row x z); subst; 
                                               auto with datatypes.
          **exact lit_test_trans.
          **intros; apply lit_test_anti_sym.
          **exact lit_test_exact.
          **apply olist_one.
          **apply gen_row_ordered.
        ++apply nth_ulist with (a := 0) (l := row x s)...
          **rewrite length_row...
          **rewrite length_row...
          **apply ulist_perm with ref_list...
            apply Permutation_sym...
          **repeat rewrite <- get_row; try rewrite H2...
    * case H1; clear H1; intros V1 (_, (V2, _)).
      case (gen_column_correct l y z); intros tmp _; case tmp; auto; clear tmp.
      --apply (rm_incl _ lit_test) with
          (l1 := L (Pos x y) z::nil)
          (l2 := gen_column y z)...
      --intros x1 (H5, H6); subst l.
        simpl in H4; absurd (x = x1).
        ++intros H7; apply (rm_not_in _ lit_test) with (a := L (Pos x y) z)
                                               (l1 := L (Pos x y) z::nil)
                                               (l2 := gen_column y z); subst;
                                              auto with datatypes.
          **exact lit_test_trans.
          **intros; apply lit_test_anti_sym.
          **exact lit_test_exact.
          **apply olist_one.
          **apply gen_column_ordered.
        ++apply nth_ulist with (a := 0) (l := column y s)...
          **rewrite length_column...
          **rewrite length_column...
          **apply ulist_perm with ref_list...
            apply Permutation_sym...
          **repeat rewrite <- get_column; try rewrite H2...
    * case (gen_rect_correct l (div x h * h + div y w) z).
      --apply rect_aux1...
      --intros tmp _; case tmp; auto; clear tmp.
        ++apply (rm_incl _ lit_test) with
              (l1 := L (Pos x y) z::nil)...
        ++intros x1 (y1, (H5, (H6, H7))); subst l.
          simpl in H4.
          match type of H4 with
          | get (Pos ?X ?Y) _ = _ =>
            generalize H3 H4; clear H3 H4;
            replace (Pos X Y) with
             (Pos (h * div x h + x1) (w * div y w + y1));
            [intros H3 H4 | idtac]
          end.
          **match type of H4 with
            | get (Pos ?X ?Y) _ = _ =>
              assert (X = x /\ Y = y)
            end.
            --- apply rect_aux2...
                +++ unfold size; rewrite (Nat.mul_comm w); apply mult_lt_plus...
                    apply div_lt; rewrite  Nat.mul_comm...
                +++ rewrite get_rect in H4...
                    *** rewrite get_rect in H2...
                        generalize H4; clear H4.
                        repeat rewrite (fun x =>  Nat.mul_comm x h).
                        repeat ((rewrite mod_mult_comp || 
                                 rewrite div_mult_comp); auto).
                        rewrite (div_is_0 x1 h)...
                        rewrite (div_is_0 y1 w)...
                        repeat rewrite  Nat.add_0_r.
                        intros H4.
                        apply nth_ulist with 
                           (a:= 0) (l := rect (div x h * h + div y w) s).
                        ----rewrite length_rect...
                            ++++unfold size; apply mult_lt_plus...
                            ++++unfold size; rewrite (Nat.mul_comm h); 
                                   apply mult_lt_plus...
                                apply div_lt; rewrite  Nat.mul_comm...
                            ++++case H1...
                        ----rewrite length_rect...
                            ++++unfold size; apply mult_lt_plus...
                            ++++unfold size; rewrite (Nat.mul_comm h);
                                  apply mult_lt_plus...
                                apply div_lt; rewrite  Nat.mul_comm...
                            ++++case H1...
                        ----apply ulist_perm with ref_list.
                            ++++apply Permutation_sym; case H1...
                                intros _ (_, (_, tmp)); apply tmp; clear tmp.
                                unfold size; rewrite (Nat.mul_comm h); 
                                  apply mult_lt_plus...
                                apply div_lt; rewrite  Nat.mul_comm...
                            ++++apply ref_list_ulist.
                        ----repeat rewrite (fun x =>  Nat.mul_comm x h).
                            unfold out in H4; rewrite H4...
                            repeat rewrite (Nat.mul_comm h)...
                    *** unfold size; repeat rewrite (Nat.mul_comm h);
                          apply mult_lt_plus...
                    *** unfold size; rewrite (Nat.mul_comm w);
                          apply mult_lt_plus...
                        apply div_lt; rewrite  Nat.mul_comm...
                +++ repeat rewrite div_mult_comp; auto with arith.
                    rewrite (div_is_0 x1); auto with arith.
                    rewrite (div_is_0 y1); auto with arith.
            --- case H; clear H; intros V1 V2; rewrite V1 in H3;
                  rewrite V2 in H3.
                match goal with
                | H:(In ?X _) |- _ =>
                  apply (rm_not_in _ lit_test) with (a := X)
                                      (l1 := X::nil)
                                      (l2 := gen_rect (div x h * h + 
                                                       div y w) z);
                  auto with datatypes
                end.
                +++ exact lit_test_trans.
                +++ intros; apply lit_test_anti_sym.
                +++ exact lit_test_exact.
                +++ apply olist_one.
                +++ apply gen_rect_ordered.
          **repeat rewrite (fun x =>  Nat.mul_comm x h).
            repeat ((rewrite mod_mult_comp || rewrite div_mult_comp); auto).
            rewrite (div_is_0 (div y w) h)...
            --- rewrite (mod_small (div y w) h)...
                apply div_lt; rewrite (Nat.mul_comm w)...
            --- apply div_lt; rewrite (Nat.mul_comm w)...
    * case (gen_cell_correct l x y); auto; intros tmp; case tmp; auto;
         clear tmp.
      --apply (rm_incl _ lit_test) with
            (l1 := L (Pos x y) z::nil)
            (l2 := gen_cell (Pos x y))...
      --intros z1 (H5, H6); subst l.
        intros H7.
        simpl in H4.
        apply (rm_not_in _ lit_test) with (a := L (Pos x y) z)
                                    (l1 := L (Pos x y) z::nil)
                                    (l2 := gen_cell (Pos x y)); subst;
            auto with datatypes.
        ++exact lit_test_trans.
        ++intros; apply lit_test_anti_sym.
        ++exact lit_test_exact.
        ++apply olist_one.
        ++apply gen_cell_ordered.
Qed.

Definition invariant cs s :=
  ordered cs /\ valid cs s /\ length s = size * size /\
  forall s1, refine s s1 -> (sudoku s1 <-> sat cs s1).

Theorem invariant_clauses_update n p z c cs s :
  invariant ((n, L p z :: c) :: cs) s ->
  invariant (clauses_update (L p z) (anti_literals (L p z)) cs) (update p z s).
Proof with auto with arith datatypes.
intros (V1, (V2, (V3, V4))).
assert (H: valid_lit (L p z) s)...
- apply (V2 n (L p z :: c))...
- split...
  + apply clauses_update_ordered...
    * apply anti_literals_ordered...
    * intros n2 c2 Hn2; apply (V1 n2 c2)...
  + split...
    * apply clauses_update_valid...
      --intros n2 c2 Hn2; apply (V1 n2 c2)...
      --apply anti_literals_ordered...
      --intros; apply anti_literals_in...
      --intros n2 c2 Hn2; apply (V2 n2)...
    * split...
      --rewrite length_update...
      --intros s1 Hs1.
        assert (Heq1: get p s1 = z).
        ++case Hs1; intros _ (_, tmp); case (tmp p); auto with arith; clear tmp.
          **case H; intuition.
          **rewrite update_get...
            --- case H; intuition.
            --- apply valid_pos2n...
                case H; intuition.
          **rewrite update_get...
            apply valid_pos2n...
            case H; intuition.
        ++split; intros Hs2.
          **apply clauses_update_sat_rev...
            --- apply anti_literals_ordered...
            --- intros n2 c2 Hn2; apply (V1 n2)...
            --- intros l Hl Hl1.
                case (anti_literals_sat p z s1)...
                +++ case H; intros _ (tmp, _)...
                +++ exists l...
            --- case (V4 s1)...
                +++ apply refine_trans with (2 := Hs1)...
                    apply refine_update...
                    case H; intuition.
                +++ intros tmp _; generalize (tmp Hs2); intros HH; clear tmp.
                    intros n2 c2 Hn2; apply (HH n2)...
          **case (V4 s1)...
            --- apply refine_trans with (2 := Hs1)...
                apply refine_update...
                case H; intuition.
            --- intros _ tmp; apply tmp; auto; clear tmp.
                assert (Heq: sat cs s1).
                +++ apply clauses_update_sat with (4 := Hs2)...
                    *** apply anti_literals_ordered...
                    *** intros n2 c2 Hn2; apply (V1 n2)...
                +++ intros n2 c2; simpl; intros [Hn2 | Hn2].
                    *** injection Hn2; intros; subst.
                        exists (L p (get p s1)); split...
                        simpl...
                    *** apply (Heq n2 c2)...
Qed.

Theorem invariant_clauses_update1 p z cs s :
  valid_lit (L p z) s -> invariant cs s ->
  invariant (clauses_update (L p z) (anti_literals (L p z)) cs) (update p z s).
Proof with auto with arith.
intros V0 (V1, (V2, (V3, V4))).
split...
- apply clauses_update_ordered...
  apply anti_literals_ordered...
- split...
  + apply clauses_update_valid...
    * apply anti_literals_ordered...
    * intros; apply anti_literals_in...
  + split...
    * rewrite length_update...
    * intros s1 Hs1.
      assert (Heq1: get p s1 = z).
      --case Hs1; intros _ (_, tmp); case (tmp p); auto with arith; clear tmp.
        ++case V0; intuition.
        ++rewrite update_get...
          **case V0; intuition.
          **apply valid_pos2n...
            case V0; intuition.
        ++rewrite update_get...
          apply valid_pos2n...
          case V0; intuition.
      --split; intros Hs2.
        ++apply clauses_update_sat_rev...
          **apply anti_literals_ordered...
          **intros l Hl Hl1.
            case (anti_literals_sat p z s1)...
            --- case V0; intros _ (tmp, _)...
            --- exists l...
          **case (V4 s1)...
            apply refine_trans with (2 := Hs1)...
            apply refine_update...
            case V0; intuition.
        ++case (V4 s1)...
          **apply refine_trans with (2 := Hs1)...
            apply refine_update...
            case V0; intuition.
          **intros _ tmp; apply tmp; auto; clear tmp.
            apply clauses_update_sat with (4 := Hs2)...
            apply anti_literals_ordered...
Qed.

Theorem invariant_refine n p z c cs s :
    invariant ((n, L p z :: c) :: cs) s ->
    (forall s1, refine (update p z s) s1 -> ~ sudoku s1) ->
    invariant ((n, c) :: cs) s.
Proof with auto with datatypes.
intros (V1, (V2, (V3, V4))) H0.
assert (H : valid_lit (L p z) s).
{
  apply (V2 n (L p z :: c))...
}
assert (F1 : ordered_clause (L p z :: c)).
{
  apply (V1 n)...
}
assert (F2 : valid_clause (L p z :: c) s). 
{
  apply (V2 n)...
}
split.
{
  intros n2 c2; simpl; intros [HH | HH]; subst.
  - injection HH; intros; subst; clear HH.
    inversion F1...
    red; apply olist_nil.
  - apply (V1 n2)...
}
split.
{
  intros n2 c2; simpl; intros [HH | HH]; subst.
  - injection HH; intros; subst; clear HH.
    intros l Hl; apply F2...
  - apply (V2 n2)...
}
split...
intros s2 Hs2; split; intros HH1.
- assert (Heq2: sat ((n, L p z :: c) :: cs) s2).
  {
    case (V4 s2)...
  }
  intros n2 c2; simpl; intros [HH | HH].
  injection HH; intros; subst n2 c2; clear HH.
  + case (Heq2 n (L p z :: c))...
    simpl; intros l ([Hl1 | Hl1], Hl2); subst.
    * simpl in Hl2.
      case (H0 s2)...
      split...
      --rewrite length_update...
      --split...
        ++case HH1...
        ++intros p1 Hp1.
          case (pos_dec p p1); intros Heq; try (subst p1).
          **rewrite update_get...
            apply valid_pos2n...
          **rewrite update_diff_get...
            --- case Hs2; intros _ (_, tmp)...
            --- case (F2 (L p z))...
                intros _ (tmp, _)...
    * exists l...
  + apply (Heq2 n2 c2)...
- case (V4 s2); auto; intros _ tmp; apply tmp; clear tmp.
  intros n2 c2; simpl; intros [HH | HH].
  + injection HH; intros; subst; clear HH.
    case (HH1 n2 c)...
    intros l (Hl1, Hl2); exists l...
  + apply (HH1 n2)...
Qed.

Theorem invariant_init_c s :
  length s = size * size -> empty s -> invariant init_c s.
Proof.
intros Hs Hs1.
split.
{
  apply init_c_ordered.
}
split.
{
  apply valid_init_c; auto.
}
split; auto.
intros s1 (_, (Hs2, _)).
generalize (init_c_sat s1 Hs2); intros Hs3.
generalize ref_list_ulist; intros F0.
generalize ref_list_length; intros F1.
apply iff_sym; apply iff_trans with (1 := Hs3); clear Hs3.
split; intros (V1, (V2, (V3, V4))); repeat split; auto.
- intros; apply Permutation_sym; apply ulist_eq_permutation; auto.
  rewrite length_row; auto.
- intros; apply Permutation_sym; apply ulist_eq_permutation; auto.
  rewrite length_column; auto.
- intros; apply Permutation_sym; apply ulist_eq_permutation; auto.
  rewrite length_rect; auto.
- intros i Hi x Hx; apply Permutation_in with ref_list; auto;
    apply Permutation_sym; auto.
- intros i Hi x Hx; apply Permutation_in with ref_list; auto;
    apply Permutation_sym; auto.
- intros i Hi x Hx; apply Permutation_in with ref_list; auto;
    apply Permutation_sym; auto.
- intros (x, y) (Hx, Hy); apply Permutation_in with (row x s1); auto.
  case (in_ex_nth _ (get (Pos x y) s1) out (row x s1)).
  intros _ tmp; apply tmp; clear tmp; auto.
  exists y; split; auto.
  + rewrite length_row; auto.
  + unfold get, row; simpl.
    rewrite jump_add; rewrite <- jump_nth.
    apply sym_equal; apply take_nth; auto.
Qed.

Theorem invariant_equiv cs s1 s2 :
  refine s1 s2 -> refine s2 s1 -> invariant cs s1 -> invariant cs s2.
Proof.
intros H1 H2 (H3, (H4, (H5, H6))).
split; auto.
split.
{
  apply valid_refine with (1 := H2); auto.
}
split.
{
  case H2; auto.
}
intros s3 H7; split; intros H8.
- case (H6 s3); auto.
  apply refine_trans with (1 := H1); auto.
- case (H6 s3); auto.
  apply refine_trans with (1 := H1); auto.
Qed.

Theorem invariant_gen_init_clauses s :
  length s = size * size -> invariant (gen_init_clauses s) s.
Proof with auto with arith.
revert s.
assert (forall s s1 cs p, valid_pos p -> length s = size * size ->
    invariant cs (prestrict p s) -> s1 = jump (pos2n p) s ->
    invariant (gen_init_clauses_aux s1 p cs) s).
{
  intros s s1; generalize s; elim s1; auto; clear s s1.
  intros s cs p H H0 H1 H2; rewrite prestrict_all in H1...
  - case (Nat.le_gt_cases (length s) (pos2n p))...
    intros H3; absurd (length (jump (pos2n p) s) = length (@nil nat)).
    + generalize (length_jump _ (pos2n p) s).
      rewrite <- H2; simpl.
      intros H4; assert (Eq1: length s = pos2n p)...
      contradict H3; rewrite Eq1...
    + f_equal...
  - intros a s1; unfold gen_init_clauses_aux; lazy beta; 
       fold gen_init_clauses_aux; case s1; clear s1.
    + intros Rec s cs p H0 H1 H2 H3.
      assert (F1: pos2n p < length s).
      {
        case (Nat.le_gt_cases (length s) (pos2n p)); auto; intros H5.
        rewrite (jump_too_far _ (pos2n p) s) in H3; try discriminate...
      }
      unfold gen_init_clauses_aux; lazy beta; fold gen_init_clauses_aux.
      case (In_dec eq_nat a ref_list); intros H5.
      * replace s with (prestrict (next p) s).
        --rewrite prestrict_update...
          ++replace (get p s)  with a.
            **apply invariant_clauses_update1...
              simpl; split...
              rewrite prestrict_get_default...
              apply out_not_in_refl.
            **unfold get; rewrite <- H3...
          ++rewrite next_pos...
        --apply prestrict_all...
          case (Nat.le_gt_cases (length s) (pos2n (next p))); auto; intros H6.
          rewrite (length_jump nat (pos2n p)).
          ++rewrite <- H3; simpl; rewrite next_pos...
          ++rewrite next_pos in H6...
      * apply invariant_equiv with (prestrict p s)...
        --split...
          ++rewrite prestrict_length...
          ++split...
            intros p1 Hp1.
            case (Nat.le_gt_cases (pos2n p) (pos2n p1)); intros Hp2.
            **rewrite prestrict_get_default; auto; intros HH; contradict HH;
                  apply out_not_in_refl.
            **rewrite prestrict_get...
        --split...
          split...
          ++rewrite prestrict_length...
          ++intros p1 Hp1.
            case (Nat.le_gt_cases (pos2n p) (pos2n p1)); intros Hp2.
            **intros HH; contradict HH; unfold get.
              rewrite <-(Nat.sub_add (pos2n p) (pos2n p1)); auto with arith;
              rewrite Nat.add_comm, jump_add; rewrite <- H3; 
              case (pos2n p1 - pos2n p); simpl; auto; intros; rewrite jump_nil; 
              apply out_not_in_refl.
            **rewrite prestrict_get...
    + intros b s1 Rec s cs p H0 H1 H2 H3.
      assert (F0: b :: s1 = jump (pos2n (next p)) s).
      {
        rewrite next_pos.
        replace (S (pos2n p)) with ((pos2n p) + 1)...
        * rewrite jump_add; rewrite <- H3; simpl...
        * rewrite Nat.add_comm...
      }
      assert (F1: pos2n (next p) < length s).
      {
        case (Nat.le_gt_cases (length s) (pos2n (next p))); auto; intros H5.
        rewrite (jump_too_far _ (pos2n (next p)) s) in F0; try discriminate...
      }
      case (In_dec eq_nat a ref_list); intros H4.
      * apply Rec...
        --apply valid_pos_next...
          rewrite <- H1...
        --rewrite prestrict_update...
          replace (get p s)  with a.
          ++apply invariant_clauses_update1...
            split; [idtac | split]...
            rewrite prestrict_get_default...
            apply out_not_in_refl.
          ++unfold get; rewrite <- H3...
      * apply Rec...
        --apply valid_pos_next...
          rewrite <- H1...
        --apply invariant_equiv with (prestrict p s)...
          ++split...
            **rewrite prestrict_length...
            **split...
              --- rewrite prestrict_length...
              --- intros p1 Hp1.
                  case (Nat.le_gt_cases (pos2n p) (pos2n p1)); intros Hp2.
                  +++ rewrite prestrict_get_default; auto; intros HH; 
                      contradict HH; apply out_not_in_refl.
                  +++ rewrite prestrict_get...
                      rewrite prestrict_get...
                      rewrite next_pos...
          ++split...
            **rewrite prestrict_length...
            **split...
              --- rewrite prestrict_length...
              --- intros p1 Hp1.
                  case (Nat.le_gt_cases (pos2n p) (pos2n p1)); intros Hp2.
                  +++ case Lt.le_lt_or_eq_stt with (1 := Hp2); clear Hp2; 
                            intros Hp2; subst.
                      *** intros HH; contradict HH; 
                                rewrite prestrict_get_default...
                        ----apply out_not_in_refl.
                        ----rewrite next_pos...
                      *** rewrite prestrict_get...
                        ----unfold get; rewrite <- Hp2; rewrite <- H3; simpl.
                            intros HH; case H4...
                        ----rewrite <- Hp2; rewrite next_pos...
                   +++ repeat rewrite prestrict_get...
                       rewrite next_pos...
}
case (Lt.le_lt_or_eq_stt 0 size); auto with arith; intros H1.
- intros s Hs; unfold gen_init_clauses; apply H; simpl...
  rewrite prestrict_0.
  apply invariant_init_c.
  + rewrite mk_0_length...
  + apply empty_mk_0.
- rewrite <- H1; simpl.
  intros s; case s; simpl.
  + intros _; unfold gen_init_clauses; simpl.
    apply invariant_init_c.
    * rewrite <- H1...
    * apply empty_nil.
  + intros; discriminate.
Qed.

Theorem try_one_sat s n c cs f :
  invariant ((n, c) :: cs) s ->
  (forall s cs1,
      invariant cs1 s -> length cs1 <= length cs ->
      match f s cs1 with
      | None => forall s1, refine s s1 -> ~ sudoku s1
      | Some s1 => sudoku s1 /\ refine s s1
      end) ->
  match try_one s c cs f with
  | None => forall s1, refine s s1 -> ~ sudoku s1
  | Some s1 => sudoku s1 /\ refine s s1
  end.
Proof.
intros H H1; generalize H; elim c; simpl;
    auto; clear c H.
- intros H s1 Hs1 H2.
  absurd (clause_sat nil s1).
  + intros H3; case H3; simpl; intros k (tmp, _); auto.
  + case H; simpl.
    intros _ (_, (_, tmp)); case (tmp s1); auto; clear tmp.
    intros tmp _; apply (tmp H2 n nil); auto with datatypes.
- intros (p1, z1) c1 Rec H3.
  assert (H : valid_lit (L p1 z1) s).
  {
    case H3; intros _ (V2, _).
    apply (V2 n (L p1 z1 :: c1)); auto with datatypes.
  }
  match goal with 
  | |- context [f ?X ?Y] =>
    assert (U1: invariant Y X);
    [idtac | generalize (H1 X Y U1); case (f X Y)]
  end.
  + apply invariant_clauses_update with (1 := H3).
  + intros s1 tmp; case tmp; auto; clear tmp.
    * apply length_clauses_update; auto.
    * intros Hs Hs1; split; auto.
      apply refine_trans with (2 := Hs1); auto.
      apply refine_update; auto.
      --case H3.
        simpl in H; case H; auto.
      --case H3; intuition.
  + intros H0.
    assert (Heq0: invariant ((n, c1) :: cs) s).
    {
      apply invariant_refine with (1 := H3); auto.
      intros s1 Hs1 Hs2; case H0 with s1; auto.
      apply length_clauses_update; auto.
    }
    generalize (Rec Heq0); clear Rec.
    case (try_one s c1 cs f); auto.
Qed.

Theorem find_one_aux_sat n s cs :
  length cs <= length n ->
  invariant cs s ->
  match find_one_aux n s cs with
  | None => forall s1, refine s s1 -> ~ sudoku s1
  | Some s1 => sudoku s1 /\ refine s s1
  end.
Proof.
revert s cs; elim n; simpl; clear n.
- intros s cs; case cs; simpl; auto; clear cs.
  intros _ H; case H; clear H.
  intros _ (_, (H0, H1)); split.
  + case (H1 s).
    * split; auto.
    * intros _ tmp; apply tmp; clear tmp.
      intros n2 c2 Hn2; case Hn2.
  + split; auto.
  + intros p l H; contradict H; auto with arith.
- intros _ c H s cs; case cs; clear cs.
  + intros _ (_, (H0, (H1, H2))); split.
    * case (H2 s).
      --split; auto.
      --intros _ tmp; apply tmp; clear tmp.
        intros n2 c2 Hn2; case Hn2.
    * split; auto.
  + intros (n1, c1); case c1; simpl.
    * intros cs1 H0 (H1, (H2, (H3, H4))) s1 Hs1 Hs2.
      absurd (clause_sat nil s1).
      --intros HH; case HH; simpl; intuition.
      --case (H4 s1); auto.
        intros tmp _; apply (tmp Hs2 n1); auto with datatypes.
    * intros (p, z) c2 cs1 H0 H1.
      match goal with
      | |- context [find_one_aux ?X ?Y ?Z] =>
        assert (tmp1: length Z <= length c);
        [idtac |assert (tmp2: invariant Z Y); 
          [
            idtac |
            generalize (H Y Z tmp1 tmp2); case (find_one_aux X Y Z)
          ]
        ]
      end; try clear tmp1 tmp2.
      --apply Nat.le_trans with (length cs1); auto with arith.
        apply length_clauses_update; auto.
      --apply invariant_clauses_update with (1 := H1); auto.
      --intros s1 (Hs1, Hs2); split; auto.
        apply refine_trans with (2 := Hs2).
        apply refine_update; auto.
        ++case H1; intros _ (V2, _).
          assert (Heq: valid_clause (L p z :: c2) s).
          {
            apply (V2 n1); auto with datatypes.
          }
          case (Heq (L p z)); auto with datatypes.
        ++case H1; intuition.
      --intros H2.
        match goal with 
        | |- context [try_one ?X ?Y ?Z ?T] =>
          generalize (try_one_sat X n1 Y Z T); case (try_one X Y Z T); auto
        end.
        ++intros s1 fRec; apply fRec; auto with arith.
          **apply invariant_refine with (1 := H1); auto.
          **intros; apply H; auto with arith.
            apply Nat.le_trans with (1 := H4); auto with arith.
        ++intros HH s1 Hs1 Hs2; case HH with s1; auto.
          **apply invariant_refine with (1 := H1); auto.
          **intros; apply H; auto.
            apply Nat.le_trans with (1 := H4); auto with arith.
Qed.

Theorem try_all_olist s c cs f :
  (forall s cs1, olist _ (lexico _ test) (f s cs1)) ->
  olist _ (lexico _ test) (try_all s c cs f).
Proof.
intros H; elim c; simpl; auto.
- apply olist_nil.
- intros (p, z) c1 Rec; unfold merges; apply merge_olist; auto.
  + intros; apply lexico_trans; auto.
    * exact test_trans.
    * intros; apply test_anti_sym; auto.
    * exact test_compat_l.
  + intros; apply lexico_anti_sym; auto.
    intros; apply test_anti_sym; auto.
  + intros; apply lexico_exact with (weight := test); auto.
    exact test_exact.
Qed.

Theorem try_all_sat s n c cs f :
  valid ((n, c) :: cs) s -> length s = size * size ->
  ordered cs ->
  (forall s cs1,
    length cs1 <= length cs -> length s = size * size -> valid cs1 s ->
    ordered cs1 ->
    (forall s2, refine s s2 -> sat cs1 s2 -> sat cs s2) ->
    (forall s2, refine s s2 -> sudoku s2 -> sat cs s2 -> sat cs1 s2) ->
    olist _ (lexico _ test) (f s cs1) /\
    (forall s1,
      In s1 (f s cs1) -> refine s s1 /\  sat cs s1) /\
      (forall s1,
        refine s s1 -> sudoku s1 -> sat cs s1 ->
        exists s2, In s2 (f s cs1) /\ refine s2 s1)
      ) ->
      olist _ (lexico _ test) (try_all s c cs f) /\
      (forall s1,
        In s1 (try_all s c cs f) -> refine s s1 /\  sat ((n, c) :: cs) s1) /\
        (forall s1,
          refine s s1 -> sudoku s1 ->  sat ((n, c) :: cs) s1 ->
          exists s2, In s2 (try_all s c cs f) /\ refine s2 s1).
Proof with auto with datatypes.
intros H0 VV VV1 H; generalize H0; elim c; simpl; clear c H0.
- intros H0; split...
  + apply olist_nil.
  + split...
    * intros s1 HH; case HH.
    * intros s1 _ _ Hs1.
      assert (F0: clause_sat nil s1).
      {
        apply (Hs1 n)...
      }
      case F0; simpl; intuition.
- intros (p, z) c1 Rec H0.
  case Rec...
  + intros n2 c2; simpl; intros [Hn2 | Hn2].
    * injection Hn2; intros; subst; clear Hn2.
      assert (F1: valid_clause (L p z :: c2) s).
      {
        apply (H0 n2)...
      }
      intros l Hl; apply (F1 l)...
    * apply (H0 n2)...
  + intros Rec1 (Rec2, Rec3).
    assert (F1: valid_lit (L p z) s).
    {
      assert (F2: valid_clause (L p z :: c1) s).
      { 
        apply (H0 n)...
      }
      apply F2...
    }
    case (H (update p z s) (clauses_update (L p z) (anti_literals (L p z)) cs)).
    * apply length_clauses_update.
    * rewrite length_update...
    * apply clauses_update_valid...
      --apply anti_literals_ordered.
      --intros; apply anti_literals_in...
      --intros n2 c2 Hn2; apply (H0 n2)...
    * apply clauses_update_ordered...
      apply anti_literals_ordered.
    * intros s2 HH HH0.
      apply clauses_update_sat with (4 := HH0)...
      --apply anti_literals_ordered.
      --simpl; case HH; intros _ (_, tmp); rewrite <- tmp...
        ++apply update_get...
          apply valid_pos2n...
          case F1; intuition.
        ++case F1; intuition.
        ++rewrite update_get...
          **case F1; intuition.
          **apply valid_pos2n...
            case F1; intuition.
    * intros s2 HH HH0 HH1.
      apply clauses_update_sat_rev...
      --apply anti_literals_ordered.
      --simpl; case HH; intros _ (_, tmp); rewrite <- tmp...
        ++apply update_get...
          apply valid_pos2n...
          case F1; intuition.
        ++case F1; intuition.
        ++rewrite update_get...
          **case F1; intuition.
          **apply valid_pos2n...
            case F1; intuition.
      --intros l Hl Hl1; case (anti_literals_sat p z s2)...
        ++case F1; intuition.
        ++simpl; case HH; intros _ (_, tmp); rewrite <- tmp...
          **apply update_get...
            apply valid_pos2n...
            case F1; intuition.
          **case F1; intuition.
          **rewrite update_get...
            --- case F1; intuition.
            --- apply valid_pos2n...
                case F1; intuition.
        ++exists l...
    * intros H1 (H2, H3).
      split...
      --unfold merges; apply merge_olist...
        ++intros; apply lexico_trans...
          **exact test_trans.
          **intros; apply test_anti_sym...
          **exact test_compat_l.
        ++intros; apply lexico_anti_sym...
          intros; apply test_anti_sym...
        ++intros; apply lexico_exact with (weight := test)...
          exact test_exact.
      --split...
        ++unfold merges; intros s1 Hs1; case merge_inv with (1 := Hs1);
            clear Hs1; intros Hs1...
          **case (H2 s1)...
            intros U1 U2; split...
            --- apply refine_trans with (2 := U1)...
                apply refine_update...
                case F1; intuition.
            --- intros n2 c2; simpl; intros [Hn2 | Hn2].
                +++ injection Hn2; intros; subst; clear Hn2.
                    exists (L p z); split; auto with datatypes; simpl.
                    case U1; intros _ (_, tmp); rewrite <- tmp; auto with arith; 
                    clear tmp.
                    *** apply update_get...
                        apply valid_pos2n...
                        case F1; intuition.
                    *** case F1; intuition.
                    *** rewrite update_get...
                        ----case F1; intuition.
                        ----apply valid_pos2n...
                            case F1; intuition.
                +++ apply (U2 n2)...
          **case (Rec2 s1); auto; clear Rec2; intros U1 U2.
            split...
            intros n2 c2; simpl; intros [Hn2 | Hn2].
            --- injection Hn2; intros; subst; clear Hn2.
                assert (F2: clause_sat c1 s1).
                {
                  apply (U2 n2)...
                }
                case F2; intros l (Hl1, Hl2).
                exists l...
            --- apply (U2 n2)...
        ++intros s1 Hs1 Hs2 Hs3.
          assert (F2: clause_sat (L p z :: c1) s1).
          {
            apply (Hs3 n)...
          }
          case F2; intros l (Hl1, Hl2); simpl in Hl1;
            case Hl1; clear Hl1; intros Hl1; subst.
          --- case (H3 s1)...
              +++ split...
                  *** rewrite length_update...
                  *** split...
                      ----case Hs1; intuition.
                      ----intros p1 Hp1.
                          case (pos_dec p p1); intros HH1.
                          ++++subst p1; rewrite update_get...
                              apply valid_pos2n...
                          ++++rewrite update_diff_get...
                              ****case Hs1; intuition.
                              ****case F1; intuition.
              +++ intros n2 c2 Hn2; apply (Hs3 n2)...
              +++ intros s2 (Hs4, Hs5).
                  exists s2; split...
                  unfold merges; apply merge_incl_l...
          --- case (Rec3 s1)...
              *** intros n2 c2; simpl; intros [Hn2 | Hn2].
                  ----injection Hn2; intros; subst; clear Hn2.
                      exists l...
                  ----apply (Hs3 n2)...
              *** intros s3 (Hs4, Hs5); exists s3; split...
                  unfold merges; apply merge_incl_r...
                  intros; apply lexico_exact with (weight := test)...
                  exact test_exact.
Qed.

Theorem find_all_aux_sat n s cs :
  length cs <= length n -> length s = size * size ->
  valid cs s -> ordered cs ->
  olist _ (lexico _ test) (find_all_aux n s cs) /\
  (forall s1,
    In s1 (find_all_aux n s cs) -> refine s s1 /\  sat cs s1) /\
  (forall s1,
    refine s s1 -> sudoku s1 -> sat cs s1 ->
    (exists s2, refine s2 s1 /\ In s2 (find_all_aux n s cs))).
Proof with auto with arith datatypes.
revert s cs; elim n; clear n.
intros s cs; case cs; simpl; auto; clear cs.
- intros _ H H0 HH1; split...
  + apply olist_one.
  + split...
    * intros s1 [H2 | H2]; subst.
      --split...
        ++red...
        ++intros n2 c2; simpl; intros HH; case HH.
      --case H2.
    * intros s1 H1 H2 H3; exists s...
- intros p l H; contradict H...
- intros a n Rec s cs; case cs; clear cs.
  + simpl; intros _ H0; split...
    * apply olist_one...
    * split...
      --simpl; intros s1 [Hs1 | Hs1]; subst.
        ++split...
          **split...
          **intros n2 c2; intros HH; case HH.
        ++case Hs1.
      --intros s1 Hs1 Hs2 Hs3; exists s...
  + intros (n1, c1) cs; case c1;
    unfold find_all_aux; lazy beta; fold find_all_aux.
    * intros H H0 HH1; split...
      --apply olist_nil.
      --split...
        ++simpl; intros s1 Hl; case Hl.
        ++intros s1 _ _ H2; case (H2 n1 nil)...
          intros x (tmp, _); case tmp.
    * intros l c2 H0 H1 H2 HH1; simpl in H0.
      case (try_all_sat s n1 (l :: c2) cs (find_all_aux n))...
      --intros n3 c3 Hn3; apply (HH1 n3)...
      --intros s1 cs1 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6.
        case (Rec s1 cs1)...
        ++apply Nat.le_trans with (1 := Hs1)...
        ++intros H3 (H4, H5).
          split...
          split...
          **intros s2 HH; case (H4 s2)...
          **intros s2 V1 V2 V3; case (H5 s2)...
            intros s3 (V4, V5); exists s3; split...
      --intros V1 (V2, V3).
        split...
        split...
        intros s1 V4 V5 V6; case (V3 s1)...
        intros s2 (V7, V8); exists s2...
Qed.


(******************************************************************************)
(*    Main theorems about sudoku                                              *)
(******************************************************************************)

Theorem init_c_sudoku s : length s = size * size -> (sat init_c s <-> sudoku s).
Proof with auto.
generalize (ref_list_ulist); intros Eq1.
generalize (ref_list_length); intros Eq2.
intros H; case (init_c_sat s); auto; intros HH0 HH1; split; intros H1.
- case HH0; clear HH0 HH1; auto; intros HH0 (HH1, (HH2, HH3)); unfold sudoku.
  split...
  repeat split; intros i U; apply Permutation_sym; apply ulist_eq_permutation...
  + rewrite length_row...
  + rewrite length_column...
  + rewrite length_rect...
- apply HH1; clear HH0 HH1.
  case H1; clear H1; intros H0 (H1, (H2, H3)).
  repeat split; try (intros i Hi j Hj; apply Permutation_in with (2 := Hj);
                     try apply Permutation_sym; auto).
  intros (x, y) (HH1, HH2).
  apply Permutation_in with (row x s)...
  rewrite get_row; try apply nth_In; try rewrite length_row...
Qed.

Theorem find_one_correct s :
  length s = size * size ->
  match find_one s with
  | None => forall s1, refine s s1 -> ~ sudoku s1
  | Some s1 => refine s s1 /\ sudoku s1
  end.
Proof.
intros Hs; unfold find_one.
match goal with 
| |- context [find_one_aux ?X ?Y ?Z] =>
  generalize (find_one_aux_sat X Y Z);
  case (find_one_aux X Y Z); auto
end.
- intros s1 H; case H; auto with arith; clear H.
  apply invariant_gen_init_clauses; auto.
- intros HH s1 H1 H2; case HH with s1; auto.
  apply invariant_gen_init_clauses; auto.
Qed.

Theorem sudoku_refine_id s1 s2 : sudoku s1 -> refine s1 s2 -> s1 = s2.
Proof with auto with arith.
intros H (H1, (H2, H3)).
apply list_nth_eq with (r := out).
- rewrite H2...
- intros n; case (Nat.le_gt_cases (length s1) n); intros H4.
  + repeat rewrite nth_default...
    rewrite H2; rewrite <- H1...
  + replace n with (pos2n (Pos (div n size) (mod n size))).
    * repeat rewrite (fun l x => (jump_nth nat l (pos2n x))).
      unfold get in H3; apply H3...
      --split...
        ++apply div_lt...
          rewrite <- H1...
        ++apply mod_lt...
          generalize H4; rewrite H1; case size...
          intros HH; contradict HH...
      --assert (F1 : div n size < size). 
        {
          apply div_lt...
          rewrite <- H1...
        }
        assert (F2: mod n size < size).
        {
          apply mod_lt...
          generalize H4; rewrite H1; case size; simpl...
          intros tmp; contradict tmp...
        }
        case H; intros _ (HH, _).
        apply Permutation_in with  (l := row (div n size) s1)...
        unfold row.
        match goal with
        | |- (In ?X ?Y) =>
          case (in_ex_nth _ X out Y); intros _ tmp; apply tmp; clear tmp;
          exists (mod n size); split; auto
        end.
        ++rewrite length_take...
          apply Nat.add_le_mono_l with (div n size * size).
          repeat rewrite (fun x y => Nat.add_comm (x * y)).
          rewrite <- length_jump; rewrite H1.
          **pattern size at 1; rewrite <- Nat.mul_1_l; 
              rewrite <- Nat.mul_add_distr_r.
            apply Nat.mul_le_mono_r...
          **apply Nat.mul_le_mono_r...
        ++simpl pos2n.
          rewrite jump_add; rewrite <- jump_nth.
          apply sym_equal; apply take_nth...
    * simpl; apply sym_equal; apply div_mod_correct.
      generalize H4; rewrite H1; case size; simpl...
      intros tmp; contradict tmp...
Qed.

Theorem find_all_correct s s1 :
  refine s s1 -> (sudoku s1 <-> In s1 (find_all s)).
Proof.
intros Hs; unfold find_all.
assert (F0: length s = size * size).
{
  case Hs; intuition.
}
match goal with
| |- context [find_all_aux ?X ?Y ?Z] =>
  case (find_all_aux_sat X Y Z); auto with arith
end.
- apply gen_init_clauses_valid; auto.
- apply gen_init_clauses_ordered; auto.
- intros V1 (V2, V3); split; intros V4.
  + case (V3 s1); auto.
    * case (invariant_gen_init_clauses s); auto.
      intros _ (_, (_, tmp)); case (tmp s1); auto; clear tmp.
    * intros s2 (V5, V6).
      case (V2 s2); auto.
      intros V7 V8.
      case (invariant_gen_init_clauses s); auto.
      intros _ (_, (_, tmp)); case (tmp s2); auto; clear tmp.
      intros _ tmp; generalize (tmp V8); clear tmp V8; intros V8.
      replace s1 with s2; auto.
      apply sudoku_refine_id; auto.
  + case (V2 s1); auto; intros V5 V6.
    case (invariant_gen_init_clauses s); auto.
    intros _ (_, (_, tmp)); case (tmp s1); auto; clear tmp.
Qed.

End check.
