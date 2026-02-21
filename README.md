# Proof Assistant Seminar at ENS de Lyon

Repository containing the material used for the Rocq tutorial.

## Setup Instructions

You will probably have the best experience with an installed version of Rocq.
If installing is fine for you, go to `https://rocq-prover.org/install` and select your operating system and favorite editor (if it is one of VSCode (or Codium), Emacs and Vim). You can always use the integrated IDE RocqIDE.
Then, clone this repository (or copy the `.v` files to a local folder), move to the obtained folder and run `make` (or if you do not have `make`, find a way to compile `magic.v`, likely using `coqc magic.v` or `rocq c magic.v`).

If installing is not fine for you or does not work right away (which happens) and you have a GitHub account, you can open a fully setup codespace by clicking on the green `<> Code` button and the `Codespaces` tab.

As a last resort, go to `https://coq.vercel.app/scratchpad.html`, copy-paste the contents of `magic.v` and `nat.v` (or the file you want to compile) and remove the line `Require Import magic.`.
