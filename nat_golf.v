Require Import magic.

(** 1. Tutorial *)

(* This file shows how an expert might have written the proofs from the
   Natural Number Game, without relying on large scale automation to trivialize
   everything.
*)

Goal forall n : nat, n + 3 = n + 3.
(* We actually do not need to introduce [n] before using [reflexivity]. *)
Proof. reflexivity. Qed.
(* [auto] would work too, but that feels like cheating given how strong it is.
*)

Goal forall n m : nat, n = 3 * m -> n + 1 = 3 * m + 1.
(* We can perform rewrites at introduction time using an arrow [->]. Besides,
   we can write [?] to let Rocq introduce them with auto-generated names.
*)
Proof. intros ?? ->; reflexivity. Qed.

Goal forall n m : nat, n = 3 * m -> n + 1 = 3 * m + 1.
Proof. intros n m <-; reflexivity. Qed.

(** Addition *)

Goal forall n m, (0 + n) + (0 + m) = (0 + n) + m.
(* We did not talk at all about computations, but actually, given the definition
   of the addition and multiplication operators, when the left argument is
   partially known, Rocq can do partial computations. In this case, Rocq can get
   rid of all the 0s automatically.
*)
Proof. reflexivity. Qed.

Theorem addn0 n : n + 0 = n.
(* We can chain tactics using [;]. The tactic on the left is executed first, and
   then the tactic on the right is executed on every subgoal. Besides, we can
   ask Rocq to do partial computations using the tactic [simpl].
*)
Proof.
  induction n.
    reflexivity.
  simpl; rewrite IHn; reflexivity.
Qed.

Theorem addnS n m : n + S m = S (n + m).
Proof.
induction n.
  reflexivity.
simpl; rewrite IHn; reflexivity.
Qed.

Theorem addC n m : n + m = m + n.
Proof.
induction n.
  rewrite addn0; reflexivity.
simpl; rewrite addnS; rewrite IHn; reflexivity.
Qed.

Theorem addA n m k : n + (m + k) = n + m + k.
Proof.
induction n.
  reflexivity.
simpl; rewrite IHn; reflexivity.
Qed.

Theorem addCA n m k : n + m + k = n + k + m.
Proof. rewrite <- addA; rewrite (addC m); rewrite addA; reflexivity. Qed.


(** Multiplication *)

(* Just like the addition, the multiplication is defined with two rules, looking
   at the left argument:
   - [0 * n = 0] for any [n], and
   - [S n * m = m + n * m] for any [n], [m].
   We will use the names [add0n] and [addSn] to refer to these rules.
*)

(* Let us start with an example combining the rules defining the multiplication
   to warm up.
*)
Theorem mul1n n : 1 * n = n.
Proof. simpl; rewrite addn0; reflexivity. Qed.

(* Before proving the usual results on multiplication, we first do the
   simplification rules on the right argument.
*)
Theorem muln0 n : n * 0 = 0.
Proof.
induction n.
  reflexivity.
simpl; rewrite IHn; reflexivity.
Qed.

Theorem mulnS n m : n * S m = n * m + n.
Proof.
induction n.
  reflexivity.
simpl; rewrite addnS; rewrite IHn; rewrite addA; reflexivity.
Qed.

Theorem mulC n m : n * m = m * n.
Proof.
induction n.
  rewrite muln0; reflexivity.
simpl; rewrite mulnS; rewrite addC; rewrite IHn; reflexivity.
Qed.

Theorem mulDn n m k : (n + m) * k = n * k + m * k.
Proof.
induction n.
  reflexivity.
simpl; rewrite IHn; rewrite addA; reflexivity.
Qed.

Theorem mulnD n m k : n * (m + k) = n * m + n * k.
Proof.
rewrite mulC; rewrite mulDn; rewrite mulC; rewrite (mulC k); reflexivity.
Qed.

Theorem mulA n m k : n * (m * k) = n * m * k.
Proof.
induction n.
  reflexivity.
simpl; rewrite mulDn; rewrite IHn; reflexivity.
Qed.
