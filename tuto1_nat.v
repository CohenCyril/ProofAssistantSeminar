Require Import magic.

(** 1. Tutorial *)

(* The aim of a proof assistant is to help the user prove mathematical theorems,
   which we call "Goals". In this tutorial we will only prove statements about
   natural numbers, some of which have known values (such as [3] below), and
   others which have unknown, arbitrary values (such as [n] below).
*)

Goal forall n : nat, n + 3 = n + 3.
Proof.
(* The goal here is the theorem [forall n : nat, n + 3 = n + 3].

   We solve goals in Rocq using tactics, which are instructions we give to the
   proof assistant. Rocq executes these instructions to make progress in the
   proof. We end every tactic with a dot [.] to let Rocq know that we are done
   writing the tactic.

   We will first introduce an arbitrary number [n] and prove [n + 3 = n + 3] on
   this number. The tactic we use to introduce objects is [intros].

   Try [intros n.].
*)



(* The goal is now [n + 3 = n + 3], where [n] is the natural number we just
   introduced.
   In this case, [n + 3 = n + 3] can be proved using the reflexivity of
   equality, using the tactic [reflexivity].
*)



Qed.

Goal forall n m : nat, n = 3 * m -> n + 1 = 3 * m + 1.
Proof.
(* Now, the goal is [forall n m : nat, n = 3 * m -> n + 1 = 3 * m + 1].
   We will introduce two natural numbers [n] and [m], assume that [n = 3 * m]
   and prove that [n + 1 = 3 * m + 1]. The tactic [intros] can be used to
   introduce hypotheses, as in [intros n m nE.].
*)



(* You can check that [n], [m] and [nE] appeared in the list of known objects
   and hypotheses.
   Thanks to the hypothesis [nE], we know that [n] and [3 * m] are two
   expressions designating the same natural number, so we can replace one by the
   other in the goal using the [rewrite] tactic.
   Write [rewrite nE.] and see what happens.
*)



(* Can you conclude the proof? *)



Qed.

Goal forall n m : nat, n = 3 * m -> n + 1 = 3 * m + 1.
Proof.
  intros n m nE.
(* We can also rewrite equalities backwards, in other words replacing the
   right-hand side by the left-hand side in the goal, using [rewrite <-]. Try
   [rewrite <- nE.] and see what happens. Then conclude the proof as before.
*)



Qed.

Goal forall n m : nat, n = 2 * m -> m = 6 -> (n - 5) * m = 42.
Proof.
  intros n m nE mE.
(* [rewrite] actually accepts any number of arguments, which are all equalities
   that get rewritten one after the other. Try [rewrite nE mE.].
*)



Qed.

(** Addition *)

(* Natural numbers are defined by two rules:
   - [0] is a natural number, and
   - if [n] is a natural number, then its successor [S n] is a natural number.
   Note that the natural numbers we have encountered so far are all built using
   these two rules. For example, [3] is merely a notation for [S (S (S 0))].

   Similarly, the addition is defined by two rules:
   - [0 + n = n] for any [n], and
   - [S n + m = S (n + m)] for any [n], [m].
   We will use the names [add0n] and [addSn] to refer to these rules.
*)

(* We will now start giving names to theorems, so that we may reuse them to make
   subsequent proofs easier. When libraries of formalized mathematics become
   large, it is hard to remember the name of every theorem. Instead, we can use
   the [Search] command, that takes as argument a list of strings and patterns
   and prints every theorem whose name matches the given strings and 
   statement matches the given patterns. A pattern can be any expression with
   holes (symbolised with underscores [_]). Give it a try!
*)

Search (_ + _).

Goal forall n m, (0 + n) + (0 + m) = (0 + n) + m.
Proof.
intros n m.
(* To solve this goal, we would like to rewrite [0 + m] into [m]. However, if we
   were to simply write [rewrite add0n], Rocq would replace [0 + n] with [n] (
   try it).
   So we need to be more precise. [add0n] is a proof of the statement
   [forall n, 0 + n = n], and we can instantiate the variable [n], as in
   [add0n m], to get a proof of [0 + m = m]. Since [rewrite] expects its
   arguments to be separated by commas, we have to put parentheses around
   [add0n m], as in [rewrite (add0n m).].
*)



Qed.

Theorem addn0 n : n + 0 = n.
Proof.
(* Our first theorem is the counterpart of [add0n]. Where [add0n] simplifies
   additions by [0] on the left, we prove that we can also simplify on
   the right.
   Like most of the proof we will do today involving natural numbers, we
   reason by induction on [n] using the eponymous tactic.
   Try [induction n.].
 *)



(* [induction n.] leaves two subgoals. The first one is the base case [n = 0],
   that is [0 + 0 = 0]. Give it a try, and keep reading when the base case is
   proved.
   Hint 1: use [add0n].
   Hint 2: [rewrite add0n.]
*)



(* Next, we have the induction case. [induction n.] introduces an induction
   hypothesis [IHn] stating our goal for [n], that is [n + 0 = n], and we have
   to prove the goal for [S n], that is [S n + 0 = S n].
   Hint: use [addSn].
*)



Qed.

Theorem addnS n m : n + S m = S (n + m).
Proof.
(* Let us also do the counterpart of [addSn], where we simplify additions with
   a successor on the right.
   Hint: We know how to deal with 0 and S on the left of additions, so let us
    reason by induction on n.
*)



Qed.

(* Well done! We are now ready to start looking at the interesting properties
   of natural number additions. Let us prove that addition is commutative.
*)
Theorem addC n m : n + m = m + n.
Proof.



Qed.

(* On to associativity! When we write an expression like [n + m + k], it is
   interpreted by Rocq as [(n + m) + k]. But that is just a convention, and it
   is equal to the other reasonable interpretation [n + (m + k)].
*)

Theorem addA n m k : n + (m + k) = n + m + k.
Proof.
(* Just to be sure, do not hesitate to try [reflexivity] and see that it fails.
*)



Qed.

(* Before moving on to multiplications, let us put our last two theorems to use.
*)
Theorem addCA n m k : n + m + k = n + k + m.
Proof.
(* Hint: Recall the [rewrite <-] syntax for rewriting an equality from right to
   left. You will also need to make some statements more precise in a rewrite,
   so that Rocq finds the correct term you want to rewrite, as in [add0n m]
   above.
*)



Qed.


(** Multiplication *)

(* Just like the addition, the multiplication is defined with two rules, looking
   at the left argument:
   - [0 * n = 0] for any [n], and
   - [S n * m = m + n * m] for any [n], [m].
   We will use the names [mul0n] and [mulSn] to refer to these rules.
*)

(* Let us start with an example combining the rules defining the multiplication
   to warm up.
*)
Theorem mul1n n : 1 * n = n.
Proof.
(* Hint: no induction here, we can simplify multiplications depending on what
   the left argument looks like. Here, we know exactly the left argument, so we
   can simplify, getting rid of the multiplication completely.
*)



Qed.

(* Before proving the usual results on multiplication, we first do the
   simplification rules on the right argument.
*)
Theorem muln0 n : n * 0 = 0.
Proof.



Qed.

Theorem mulnS n m : n * S m = n * m + n.
Proof.



Qed.

(* Just like addition, multiplication is commutative and associative. *)
Theorem mulC n m : n * m = m * n.
Proof.



Qed.

(* If we were to try to prove the associativity of multiplication now, we would
   quickly get stuck. Indeed, when one argument of a multiplication is a
   successor, our simplification lemmas turn that multiplication into an
   addition. However, when that multiplication was an argument of another
   multiplication, we would end up with a multiplication, of which one of the
   arguments is an addition, which we do not know how to deal with yet.
   What we need is the distributivity of multiplication over addition.
*)
Theorem mulDn n m k : (n + m) * k = n * k + m * k.
Proof.



Qed.

Theorem mulnD n m k : n * (m + k) = n * m + n * k.
Proof.
(* How would you prove this? Can you do it with just 5 tactics? *)



Qed.

(* An expression such as [n * m * k] is interpreted as [(n * m) * k]. *)
Theorem mulA n m k : n * (m * k) = n * m * k.
Proof.



Qed.
