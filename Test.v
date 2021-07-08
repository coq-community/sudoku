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

Require Import Sudoku.
Require Import Print.
Require Import String.
Require Import Parse.
Require Import Extraction.
Import List.

Definition one_solution n m l :=
 match find_one n m l with Some c => print n m c 
                          | _ => "No Solution" end.

Definition solutions n m l := length (find_all n m l).

Definition cr := "
".

Definition just_one_solution n m l :=
 match find_just_one n m l with
   jOne c => print n m c 
 | jNone => "No Solution" 
 | jMore c1 c2 => ("More Than One Solution" ++ cr
                  ++ (print n m c1) ++ cr ++ (print n m c2))%string  
 end.

(* Compute all the sudoku 2 x 2 *)
Eval vm_compute in solutions 2 2 (init 2 2).

Definition os s := one_solution 3 3 (parse s).
Definition ns s := solutions 3 3 (parse s).
Definition jos s := just_one_solution 3 3 (parse s).


Time Eval vm_compute in jos
 "
   -------------
   |  8|16 |9  |
   |  4| 5 |2  |
   |97 |  8| 45|
   -------------
   |  5|   |  6|
   |89 |   | 37|
   |1  |   |4  |
   -------------
   |36 |5  | 84|
   |  2| 7 |5  |
   |  7| 49|3  |
   -------------".
Definition l1 := Eval vm_compute in parse
 "
   -------------
   |  8|16 |9  |
   |  4| 5 |2  |
   |97 |  8| 45|
   -------------
   |  5|   |  6|
   |89 |   | 37|
   |1  |   |4  |
   -------------
   |36 |5  | 84|
   |  2| 7 |5  |
   |  7| 49|3  |
   -------------".



Time Eval vm_compute in jos
 "
     -------------
     |  6|98 |2  |
     |   |   |   |
     |1 7| 43|8 9|
     -------------
     |  2|   |  1|
     |5 3|   |4 7|
     |9  |   |6  |
     -------------
     |2 8|13 |9 5|
     |   |   |   |
     |  4| 78|1  |
     -------------".

Let ppf n m := one_solution n m (init n m).

(* Find a solution for 1 x 1 *)
Time Eval compute in (ppf 1 1).

(* Find a solution for 2 x 1 *)
Time Eval vm_compute in ppf 2 1.

(* Find a solution for 2 x 2 *)
Time Eval vm_compute in ppf 2 2.

(* Find a solution for 3 x 2 *)
Time Eval vm_compute in ppf 3 2.

(* Find a solution for 3 x 3 *)
Time Eval vm_compute in ppf 3 3.


(* A problem with more than one solution *)
Time Eval vm_compute in jos
"     -------------
     |   |9  |  1|
     |   | 4 | 2 |
     | 8 | 7 |  6|
     -------------
     |2 1|4  |   |
     |   |6  |   |
     |3  |  1|6 8|
     -------------
     |5  |   | 8 |
     |49 | 5 |   |
     |   |  2|   |
     -------------".

Extraction "Sudoku.ml" find_just_one.

Time Eval vm_compute in jos
"
    -------------
    |5  |   |   |
    | 4 |81 |   |
    | 93|   |  2|
    -------------
    |   |   |2 3|
    |9  |7  |   |
    |23 |  6| 7 |
    -------------
    |365|1  |   |    |   | 5 |8  |
    |  1| 7 |6  |
    -------------".

Time Eval vm_compute in jos

"
     -------------
     |   |   | 6 |
     |43 | 5 |  2|
     |  7|832|4  |
     -------------
     |2  | 43|   |
     | 81|   |34 |
     |   |68 |  1|
     -------------
     |  3|719|6  |
     |7  | 6 | 14|
     | 6 |   |   |
     -------------".

(* L'escargot *)

Time Eval vm_compute in jos
" 
     -------------
    |1  |  7| 9 |
    | 3 | 2 |  8|
    |  9|6  |5  |
    -------------
    |  5|3  |9  |
    | 1 | 8 |  2|
    |6  |  4|   |
    -------------
    |3  |   | 1 |
    | 4 |   |  7|
    |  7|   |3  |
    -------------".

(* Le Monde 4/3/07 *)

Time Eval vm_compute in jos

" 
    -------------
    |2  | 68|   |
    | 69|   |   |
    |  7|1  |93 |
    -------------
    |   |   |8  |
    |9  |8  |5  |
    |35 |   | 4 |
    -------------
    | 12|7  |   |
    |   | 2 |6 5|
    |  5|   |4  |   -------------".

(* Le monde 28/10/07 *)

Time Eval vm_compute in jos
" 
    -------------
    |9  |  8|   |
    | 52|   |  1|
    |  4| 6 | 3 |
    -------------
    |   |   |   |
    |2  |1  |6  |
    |69 | 32| 1 |
    -------------
    |  7|5  |   |
    |   |   |8  |
    |  6| 93|5  |
    -------------".

(* Repubblica 6/05/2008 *)


Time Eval vm_compute in jos
" 
    -------------
    |   |7  |5  |
    |   | 63|   |
    | 8 |  2|  1|
    -------------
    |  6|  4|2  |
    |24 |856| 79|
    |  3|2  |1  |
    -------------
    |7  |3  | 4 |
    |   |91 |   |
    |  2|  8|   |
    -------------".


(* TeleStar 12/05/2008 *)


Time Eval vm_compute in jos
" 
    -------------
    |  2|  3| 9 |
    |9  |52 |   |
    |  3| 8 |4  |
    -------------
    |   |   |18 |
    |7  |   |  3|
    | 54|  6|   |
    -------------
    |  1| 6 |2 8|
    |   | 42| 1 |
    -------------
    |   |   |18 |
    |7  |   |  3|
    | 54|  6|   |
    -------------
    |  1| 6 |2 8|
    |   | 42| 1 |
    | 2 |3  | 7 |
    -------------".

(* Le monde 7/10/2008 *)


Time Eval vm_compute in jos
" 
    -------------
    |5  | 37|1  |
    |   |   |   |
    | 16|2  |4 8|
    -------------
    |   |   |   |
    |   |5  |6  |
    |49 |  6| 35|
    -------------
    | 87|   |   |
    | 5 |38 |  6|
    |  3| 72|8  |
    -------------".
