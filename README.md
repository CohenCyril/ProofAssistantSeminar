# Proof Assistant Seminar at ENS de Lyon

Repository containing the material used for the Rocq tutorial.

## Repository organization

### Tuto1
This repository contains some `.v` files which contain Rocq code:
- The `magic.v` file contains some commands and theorems to setup the environment in which the tutorial takes place.
- The `tuto1_nat*` files contain the vanilla Rocq version of the game while the `ssrnat*` files contain the SSReflect version:
  - `*nat.v` is the game file. It contains all the explanations on Rocq commands required to complete the game. There are three blank lines at places that expect Rocq commands doing the required actions.
  - `*nat_solution.v` contains an example of expected solution. Of course, your solution may be different. So long as the `Qed.` command is accepted by Rocq, everything is fine.
  - `*nat_golf.v` contains minimal proofs of every goal (to the best of my ability), with explanations on Rocq's features that are used and not covered by the tutorial.

### tuto2

Files `tuto2_*.v` contain the 2nd tutorial sessions and solutions.

### tuto3

Files `tuto3_*.v` contain the 2nd tutorial sessions and solutions.

This session requires


## Setup Instructions

### For the first two tutorials

You will probably have the best experience with an installed version of Rocq.
If installing is fine for you, go to [the official installation instructions](https://rocq-prover.org/install) and select your operating system and favorite editor (if it is one of VSCode (or Codium), Emacs and Vim). You can always use the integrated IDE RocqIDE.
Then, clone this repository (or copy the `.v` files to a local folder), move to the obtained folder and run `make` (or if you do not have `make`, find a way to compile `magic.v`, likely using `coqc magic.v` or `rocq c magic.v`).

If installing is not fine for you or does not work right away (which happens) and you have a GitHub account, you can open a fully setup codespace by clicking on the green `<> Code` button and the `Codespaces` tab.

As a last resort, go to [jsCoq](https://coq.vercel.app/scratchpad.html), copy-paste the contents of `magic.v` and `nat.v` (or the file you want to compile) and remove the line `Require Import magic.`.

### For the third tutorial

You will need to install additionally the following packages (run e.g. `opam install`)

You will need  the following packages:
- rocq-mathcomp-ssreflect
- rocq-mathcomp-stdlib
- rocq-mathcomp-zify
- rocq-mathcomp-algebra
- rocq-mathcomp-algebra-tactics
