(********************************************************)
(*            Test.v:                                   *)
(*     Some tests                                       *)
(*                               thery@sophia.inria.fr  *)
(*                                      (2006)          *)
(********************************************************)

Require Import Sudoku.


(* Compute all the sudoku 2 x 2 *)
Eval compute in length (find_all 2 2 (init 2 2)).

Definition l1 := 
  0 :: 0 :: 8 :: 1 :: 6 :: 0 :: 9 :: 0 :: 0 ::
  0 :: 0 :: 4 :: 0 :: 5 :: 0 :: 2 :: 0 :: 0 ::
  9 :: 7 :: 0 :: 0 :: 0 :: 8 :: 0 :: 4 :: 5 ::
  0 :: 0 :: 5 :: 0 :: 0 :: 0 :: 0 :: 0 :: 6 ::
  8 :: 9 :: 0 :: 0 :: 0 :: 0 :: 0 :: 3 :: 7 :: 
  1 :: 0 :: 0 :: 0 :: 0 :: 0 :: 4 :: 0 :: 0 ::
  3 :: 6 :: 0 :: 5 :: 0 :: 0 :: 0 :: 8 :: 4 ::
  0 :: 0 :: 2 :: 0 :: 7 :: 0 :: 5 :: 0 :: 0 ::
  0 :: 0 :: 7 :: 0 :: 4 :: 9 :: 3 :: 0 :: 0 :: nil.

Ltac solve n m v := 
  let x := eval compute in (match find_one n m v
   with None => nil | (Some c) => c end) in
  exact x.

(* Find a solution of l1 *)
Definition t1 : list nat.
solve 3 3 l1.
Defined.
Eval compute in (row 3 3 0 t1).
Eval compute in (row 3 3 1 t1).
Eval compute in (row 3 3 2 t1).
Eval compute in (row 3 3 3 t1).
Eval compute in (row 3 3 4 t1).
Eval compute in (row 3 3 5 t1).
Eval compute in (row 3 3 6 t1).
Eval compute in (row 3 3 7 t1).
Eval compute in (row 3 3 8 t1).

(* Compute the number of solutions of l1 *)
Eval compute in length (find_all 3 3 l1).


Definition l2 := 
0 :: 0 :: 6 :: 9 :: 8 :: 0 :: 2 :: 0 :: 0 ::
0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 ::
1 :: 0 :: 7 :: 0 :: 4 :: 3 :: 8 :: 0 :: 9 ::
0 :: 0 :: 2 :: 0 :: 0 :: 0 :: 0 :: 0 :: 1 ::
5 :: 0 :: 3 :: 0 :: 0 :: 0 :: 4 :: 0 :: 7 ::
9 :: 0 :: 0 :: 0 :: 0 :: 0 :: 6 :: 0 :: 0 ::
2 :: 0 :: 8 :: 1 :: 3 :: 0 :: 9 :: 0 :: 5 ::
0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 ::
0 :: 0 :: 4 :: 0 :: 7 :: 8 :: 1 :: 0 :: 0 :: nil.

(* Find a solution of l2 *)
Definition t2 : list nat.
  solve 3 3 l2.
Defined.
Eval compute in (row 3 3 0 t2).
Eval compute in (row 3 3 1 t2).
Eval compute in (row 3 3 2 t2).
Eval compute in (row 3 3 3 t2).
Eval compute in (row 3 3 4 t2).
Eval compute in (row 3 3 5 t2).
Eval compute in (row 3 3 6 t2).
Eval compute in (row 3 3 7 t2).
Eval compute in (row 3 3 8 t2).

(* Find a solution for 3 * 3 *)
Definition t3 : list nat.
solve 3 3 (init 3 3).
Defined.
Eval compute in (row 3 3 0 t3).
Eval compute in (row 3 3 1 t3).
Eval compute in (row 3 3 2 t3).
Eval compute in (row 3 3 3 t3).
Eval compute in (row 3 3 4 t3).
Eval compute in (row 3 3 5 t3).
Eval compute in (row 3 3 6 t3).
Eval compute in (row 3 3 7 t3).
Eval compute in (row 3 3 8 t3).

(* Find a solution for 1 x 1 *)
Eval compute in find_one 1 1 (init 1 1).

(* Find a solution for 2 x 1 *)
Eval compute in find_one 2 1 (init 2 1).

(* Find a solution for 2 x 2 *)
Eval compute in find_one 2 2 (init 2 2).

(* Find a solution for 3 x 2 *)
Eval compute in find_one 3 2 (init 3 2).

(* Find a solution for 3 x 3 *)
Eval compute in find_one 3 3 (init 3 3).


Definition l4 := 
  0 :: 0 :: 0 :: 9 :: 0 :: 0 :: 0 :: 0 :: 1 ::
  0 :: 0 :: 0 :: 0 :: 4 :: 0 :: 0 :: 2 :: 0 ::
  0 :: 8 :: 0 :: 0 :: 7 :: 0 :: 0 :: 0 :: 6 ::
  2 :: 0 :: 1 :: 4 :: 0 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 0 :: 0 :: 6 :: 0 :: 0 :: 0 :: 0 :: 0 :: 
  3 :: 0 :: 0 :: 0 :: 0 :: 1 :: 6 :: 0 :: 8 ::
  5 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 8 :: 0 ::
  4 :: 9 :: 0 :: 0 :: 5 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 0 :: 0 :: 0 :: 0 :: 2 :: 0 :: 0 :: 0 :: nil.

(* Find a solution for l4 *)
Definition t4 : list nat.
Time solve 3 3 l4.
Defined.
Eval compute in (row 3 3 0 t4).
Eval compute in (row 3 3 1 t4).
Eval compute in (row 3 3 2 t4).
Eval compute in (row 3 3 3 t4).
Eval compute in (row 3 3 4 t4).
Eval compute in (row 3 3 5 t4).
Eval compute in (row 3 3 6 t4).
Eval compute in (row 3 3 7 t4).
Eval compute in (row 3 3 8 t4).

Time Eval compute in length (find_all 3 3 l4).


Definition l5 := 
  5 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 4 :: 0 :: 8 :: 1 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 9 :: 3 :: 0 :: 0 :: 0 :: 0 :: 0 :: 2 ::
  0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 2 :: 0 :: 3 ::
  9 :: 0 :: 0 :: 7 :: 0 :: 0 :: 0 :: 0 :: 0 :: 
  2 :: 3 :: 0 :: 0 :: 0 :: 6 :: 0 :: 7 :: 0 ::
  3 :: 6 :: 5 :: 1 :: 0 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 0 :: 0 :: 0 :: 5 :: 0 :: 8 :: 0 :: 0 ::
  0 :: 0 :: 1 :: 0 :: 7 :: 0 :: 6 :: 0 :: 0 :: nil.

(* Find a solution for l5 *)
Definition t5 : list nat.
Time solve 3 3 l5.
Defined.
Eval compute in (row 3 3 0 t5).
Eval compute in (row 3 3 1 t5).
Eval compute in (row 3 3 2 t5).
Eval compute in (row 3 3 3 t5).
Eval compute in (row 3 3 4 t5).
Eval compute in (row 3 3 5 t5).
Eval compute in (row 3 3 6 t5).
Eval compute in (row 3 3 7 t5).
Eval compute in (row 3 3 8 t5).

Time Eval compute in length (find_all 3 3 l5).


