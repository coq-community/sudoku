[![Build Status](https://travis-ci.org/thery/sudoku.svg?branch=master)](https://travis-ci.org/thery/sudoku)

## Sudoku


A formalisation of Sudoku in Coq. It implements a naive
Davis-Putnam procedure to solve sudokus.

A sudoku is represented as a mono-dimensional list of natural
numbers. Zeros are used to represent empty cells. For example,
for 3x3 sudokus:

  -------------------------------------
  |   |   | 8 | 1 | 6 |   | 9 |   |   |
  -------------------------------------
  |   |   | 4 |   | 5 |   | 2 |   |   |
  -------------------------------------
  | 9 | 7 |   |   |   | 8 |   | 4 | 5 |
  -------------------------------------
  |   |   | 5 |   |   |   |   |   | 6 |
  -------------------------------------
  | 8 | 9 |   |   |   |   |   | 3 | 7 |
  -------------------------------------
  | 1 |   |   |   |   |   | 4 |   |   |
  -------------------------------------
  | 3 | 6 |   | 5 |   |   |   | 8 | 4 |
  -------------------------------------
  |   |   | 2 |   | 7 |   | 5 |   |   |
  -------------------------------------
  |   |   | 7 |   | 4 | 9 | 3 |   |   |
  -------------------------------------

is represented as

  0 :: 0 :: 8 :: 1 :: 6 :: 0 :: 9 :: 0 :: 0 ::
  0 :: 0 :: 4 :: 0 :: 5 :: 0 :: 2 :: 0 :: 0 ::
  9 :: 7 :: 0 :: 0 :: 0 :: 8 :: 0 :: 4 :: 5 ::
  0 :: 0 :: 5 :: 0 :: 0 :: 0 :: 0 :: 0 :: 6 ::
  8 :: 9 :: 0 :: 0 :: 0 :: 0 :: 0 :: 3 :: 7 ::
  1 :: 0 :: 0 :: 0 :: 0 :: 0 :: 4 :: 0 :: 0 ::
  3 :: 6 :: 0 :: 5 :: 0 :: 0 :: 0 :: 8 :: 4 ::
  0 :: 0 :: 2 :: 0 :: 7 :: 0 :: 5 :: 0 :: 0 ::
  0 :: 0 :: 7 :: 0 :: 4 :: 9 :: 3 :: 0 :: 0 :: nil.


All functions are parametrized by the height and width of
its subrectangles.

For example for 3x3,

  sudoku 3 3: list nat -> Prop

   check 3 3: forall l, {sudoku 3 3 l} + {~ sudoku 3 3 l}

find_one 3 3: list nat -> option (list nat)

find_all 3 3: list nat -> list (list nat)

See Test.v

Corresponding correctness theorems are:

find_one_correct 3 3
     : forall s,
       length s = 81 ->
       match find_one 3 3 s with
       | Some s1 => refine 3 3 s s1 /\ sudoku 3 3 s1
       | None =>
           forall s, refine 3 3 s s1 -> ~ sudoku 3 3 s1
       end

find_all_correct 3 3
     : forall s,
       length s = 81 ->
       refine 3 3 s s1 -> (sudoku 3 3 s1 <-> In s1 (find_all 3 3 s))

See Sudoku.v

The contribution includes:

ListOp.v         some basic functions on list
Sudoku.v         main file
Test.v           test file


The following files should be in the libraries of Coq:

Tactic.v         contradict tactic
Div.v            division and modulo for nat
Permutation.v    permutation
UList.v          unique list
ListAux.v        auxillary facts on lists
OrderedList.v    ordered list


Laurent Théry (Laurent.Thery@inria.fr)
