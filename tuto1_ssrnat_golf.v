Require Import magic.
From Corelib Require Import ssreflect.

(** 1. Tutorial *)

(* This file shows how an expert might have written the proofs from the
   Natural Number Game, without relying on large scale automation to trivialize
   everything.
*)

Goal forall n : nat, n + 3 = n + 3.
(* First surprise, the [by] tactical, which can be put before a tactic. It is a
   limited form of automation that closes trivial proofs. In particular, it
   tries reflexivity. We do not even need to do anything beforehand, in which
   case we write [by []].
*)
Proof. by []. Qed.

Goal forall n m : nat, n = 3 * m -> n + 1 = 3 * m + 1.
(* We can perform rewrites at introduction time using an arrow [->]. Besides,
   we do not really care about the names of the natural numbers since we never
   need to mention them. We can write [?] to let Rocq introduce them with
   auto-generated names that we are forbidden to use ourselves.
*)
Proof. by move=> ?? ->. Qed.

Goal forall n m : nat, n = 3 * m -> n + 1 = 3 * m + 1.
(* We can perform rewrites from right to left using the backwards arrow [<-].
*)

Proof. by move=> ?? <-. Qed.

Goal forall n m : nat, n = 2 * m -> m = 6 -> (n - 5) * m = 42.
Proof. by move=> ?? -> ->. Qed.

(** Addition *)

Goal forall n m, (0 + n) + (0 + m) = (0 + n) + m.
(* We did not talk at all about computations, but actually, given the definition
   of the addition and multiplication operators, when the left argument is
   partially known, Rocq can do partial computations. In this case, Rocq can get
   rid of all the 0s automatically.
*)
Proof. by []. Qed.

Theorem addn0 n : n + 0 = n.
(* After a tactic that may introduce several goals, the first argument after
   the [=>] tactical can be of the form [[ | ... | ]] where the pipes separate
   introduction sequences, with one sequence of introductions for each subgoal.
   In our case, [elim] produces two subgoals, so we have one pipe. On the first
   subgoal we do nothing, and on the second we introduce one object with an
   auto-generated name and rewrite the equation that follows from right to left.
   Every introduction pattern that follows is applied to every subgoal.

   We can also ask Rocq to do partial computations in the middle of a sequence
   of introductions using [/=].
   Try removing it and understand why it fails.
*)
Proof. by elim: n => [|? /= ->]. Qed.

Theorem addnS n m : n + S m = S (n + m).
Proof. by elim: n => [|n /= ->]. Qed.

Theorem addC n m : n + m = m + n.
(* 
   Two new things here.

   One is the sequencing of tactics with [;]. The tactic on the left is executed
   first, and then the tactic on the right is executed on every subgoal. In this
   case, the [rewrite] is executed on the two subgoals produced by [elim].

   Second is the argument of the [rewrite]. We can give as argument a tuple of
   equations, and [rewrite] rewrites the first one it succeeds to rewrite. In
   this case, [rewrite] rewrites [addn0] in the first subgoal of [elim] and
   [addnS] in the second.
*)
Proof. by elim: n => [|? /= ->]; rewrite (addn0, addnS). Qed.

Theorem addA n m k : n + (m + k) = n + m + k.
Proof. by elim: n => [|? /= ->]. Qed.

Theorem addCA n m k : n + m + k = n + k + m.
Proof. by rewrite -addA (addC m) addA. Qed.


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
(* [n + 1] computes to [n + 0], so [mul1n] and [addn0] are actually the same
   theorem.
   We apply a theorem using the eponymous tactic [apply]. This tactic takes no
   argument and applies the first hypothesis of the conclusion to the rest of
   the conclusion. Thus, we start by putting the [addn0] in the conclusion as a
   hypothesis and then call [apply]. We use [exact], which is synonymous to
   [by apply], which ensures that the tactic closes the goal.
*)
Proof. exact: addn0. Qed.

(* Before proving the usual results on multiplication, we first do the
   simplification rules on the right argument.
*)
Theorem muln0 n : n * 0 = 0.
Proof. by elim: n. Qed.

Theorem mulnS n m : n * S m = n * m + n.
(* We can close a trivial subgoal during a sequence of introductions using [//],
   which behaves like the [by] tactical except that it never fails. In
   particular, the [rewrite] below only applies to the second subgoal of [elim]
   since the first one has already been solved by [//].
*)
Proof. by elim: n => [//|n /= ->]; rewrite addnS addA. Qed.

Theorem mulC n m : n * m = m * n.
(* [//] can also be used during a sequence of rewrites. In this case, it
   closes the first subgoal, leaving only the second one open where we rewrite
   [addC].
*)
Proof. by elim: n => [|n /= ->]; rewrite (muln0, mulnS)// addC. Qed.

Theorem mulDn n m k : (n + m) * k = n * k + m * k.
Proof. by elim: n => [//|n /= ->]; rewrite addA. Qed.

Theorem mulnD n m k : n * (m + k) = n * m + n * k.
Proof. by rewrite mulC mulDn !(mulC n). Qed.

Theorem mulA n m k : n * (m * k) = n * m * k.
Proof. by elim: n => [//|n /= ->]; rewrite mulDn. Qed.
