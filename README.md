<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Sudoku

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/sudoku/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/sudoku/actions?query=workflow:"Docker%20CI"

[nix-action-shield]: https://github.com/coq-community/sudoku/workflows/Nix%20CI/badge.svg?branch=master
[nix-action-link]: https://github.com/coq-community/sudoku/actions?query=workflow:"Nix%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



A formalisation of Sudoku in Coq. It implements a naive
Davis-Putnam procedure to solve Sudokus.

## Meta

- Author(s):
  - Laurent Théry (initial)
- Coq-community maintainer(s):
  - Ben Siraphob ([**@siraben**](https://github.com/siraben))
  - Laurent Théry ([**@thery**](https://github.com/thery))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: 8.12 or later
- Additional dependencies: none
- Coq namespace: `Sudoku`
- Related publication(s):
  - [Sudoku in Coq](https://hal.inria.fr/hal-03277886) 

## Building and installation instructions

The easiest way to install the latest released version of Sudoku
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-sudoku
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/sudoku.git
cd sudoku
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

A Sudoku is represented as a mono-dimensional list of natural
numbers. Zeros are used to represent empty cells. For example,
the 3x3 Sudoku:

```
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
```

is represented as

```coq
  0 :: 0 :: 8 :: 1 :: 6 :: 0 :: 9 :: 0 :: 0 ::
  0 :: 0 :: 4 :: 0 :: 5 :: 0 :: 2 :: 0 :: 0 ::
  9 :: 7 :: 0 :: 0 :: 0 :: 8 :: 0 :: 4 :: 5 ::
  0 :: 0 :: 5 :: 0 :: 0 :: 0 :: 0 :: 0 :: 6 ::
  8 :: 9 :: 0 :: 0 :: 0 :: 0 :: 0 :: 3 :: 7 ::
  1 :: 0 :: 0 :: 0 :: 0 :: 0 :: 4 :: 0 :: 0 ::
  3 :: 6 :: 0 :: 5 :: 0 :: 0 :: 0 :: 8 :: 4 ::
  0 :: 0 :: 2 :: 0 :: 7 :: 0 :: 5 :: 0 :: 0 ::
  0 :: 0 :: 7 :: 0 :: 4 :: 9 :: 3 :: 0 :: 0 :: nil
```

All functions are parametrized by the height and width of
a Sudoku's subrectangles. For example, for a 3x3 Sudoku:
```coq
sudoku 3 3: list nat -> Prop

check 3 3: forall l, {sudoku 3 3 l} + {~ sudoku 3 3 l}

find_one 3 3: list nat -> option (list nat)

find_all 3 3: list nat -> list (list nat)
```

See `Test.v`.

Corresponding correctness theorems are:
```coq
find_one_correct 3 3
     : forall s,
       length s = 81 ->
       match find_one 3 3 s with
       | Some s1 => refine 3 3 s s1 /\ sudoku 3 3 s1
       | None =>
           forall s, refine 3 3 s s1 -> ~ sudoku 3 3 s1
       end

find_all_correct 3 3
     : forall s s1, refine 3 3 s s1 -> (sudoku 3 3 s1 <-> In s1 (find_all 3 3 s))
```

See `Sudoku.v`.

More about the formalisation can be found in a [note](https://hal.inria.fr/hal-03277886).

The following files are included:
- `ListOp.v`         some basic functions on list
- `Sudoku.v`         main file
- `Test.v`           test file
- `Tactic.v`         contradict tactic
- `Div.v`            division and modulo for nat
- `Permutation.v`    permutation
- `UList.v`          unique list
- `ListAux.v`        auxillary facts on lists
- `OrderedList.v`    ordered list

The Sudoku code can be extracted to JavaScript using
[js_of_ocaml](https://github.com/ocsigen/js_of_ocaml):
```shell
make Sudoku.js
```
Then, point your browser at `Sudoku.html`.
