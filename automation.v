(** * Automation and Libraries — Tutorial (exercise file)

    This tutorial follows nat.v / ssrnat.v and inductive.v / ssrinductive.v.
    It introduces the tools that let you write shorter, more robust proofs
    by taking advantage of Rocq's automation.

    Exercises are marked [(* EXERCISE: ... *)] and end with [Admitted.] or
    [Abort.].  Replace them with real proofs.  A companion file
    [automation_solution.v] contains example solutions — try to do each
    exercise yourself first!

    Sections
    --------
    1. Propositional automation:  [tauto], [firstorder], [assert]
    2. Arithmetic decision procedures: [lia], [ring], [field]
    3. Typeclasses (monoids, groups)
    4. (SSReflect / MathComp) Boolean reflection
    5. Navigating libraries:     [Search], [Check], [Print], [Locate]
    6. Divisibility in MathComp
    7. Big operators: [\sum] and [\prod]

*)

(**********************************************************)
(* From Section 4. you will need  the following packages: *)
(* - rocq-mathcomp-ssreflect                              *)
(* - rocq-mathcomp-stdlib                                 *)
(* - rocq-mathcomp-zify                                   *)
(* - rocq-mathcomp-algebra                                *)
(* - rocq-mathcomp-algebra-tactics                        *)
(**********************************************************)



Add Search Blacklist "Unnamed" "Nat" "Hexadecimal" "Decimal" "plus" "mult"
  "__canonical" "__to__".
From Corelib Require Import ssreflect.

(* ================================================================== *)
(** ** 1. Propositional automation *)
(* ================================================================== *)

(** *** 1.1  The [tauto] tactic *)

(* [tauto] is a *complete* decision procedure for intuitionistic
   propositional tautologies.  It handles any goal built from [/\], [\/],
   [->], [~], [True], [False], as long as the atoms are treated as opaque.

   "Complete" means: if the goal is an intuitionistic propositional
   tautology, [tauto] will succeed; if not, it will fail quickly (not
   just time out). *)

Goal forall A B : Prop, A /\ B -> B /\ A.
Proof.
  tauto.
Qed.

(* EXERCISE: prove this manually and then by [tauto]. *)
Goal forall A B C : Prop, (A -> B) -> (B -> C) -> A -> C.
Proof.
  (* your proof here *)
Abort.

(* EXERCISE: the contrapositive.  Prove manually or use [tauto]. *)
Goal forall A B : Prop, (A -> B) -> ~B -> ~A.
Proof.
  (* your proof here *)
Abort.

(* However, [tauto] is intuitionistic by default: it does NOT prove classical
   tautologies like the excluded middle, unless classical logic is explicitly
   loead.  We can observe this with [Fail]:
   [Fail tac.] succeeds exactly when [tac] fails, which is what we want
   here — we want to CHECK that [tauto] fails on a classical principle. *)

Lemma em_try : forall A : Prop, A \/ ~ A.
Proof.
move=> A.
Fail tauto.                 (* intuitionistic — gets stuck on A \/ ~A  *)
Abort.

(* Because we wrote [Abort.], the lemma [em_try] is not added to the
   environment.  Here is the evidence: *)

Fail Print em_try.

(* EXERCISE: To prove classical tautologies, load the [Classical] axiom
   module from the standard library.  [Classical] gives you
       classic : forall P : Prop, P \/ ~ P.
   Uncomment the [Require] below and complete the proof using [classic]. *)

(* From Stdlib Require Import Classical. *)

Lemma em : forall A : Prop, A \/ ~ A.
Proof.
  (* Use [tauto] *)
Abort.

(* EXERCISE: another classical tautology.  Requires [Classical]. *)
(* Prove by hand or with [tauto] *)
Goal forall A B : Prop, (~ A -> B) -> A \/ B.
Proof.
(* your proof here *)
Abort.


(** *** 1.2  The [firstorder] tactic *)

(* [firstorder] extends [tauto] to first-order logic: it handles universal
   and existential quantifiers in addition to the propositional
   connectives.  It is more powerful, but it is *not complete* and it is
   significantly slower than [tauto]. *)

Goal forall (X : Type) (P Q : X -> Prop),
  (forall x, P x /\ Q x) -> (forall x, P x) /\ (forall x, Q x).
Proof.
firstorder.
Qed.

(* EXERCISE: *)
Goal forall (X : Type) (P Q : X -> Prop),
  (forall x, P x -> Q x) -> (forall x, P x) -> forall x, Q x.
Proof.
(* your proof here *)
Abort.

(* EXERCISE: *)
Goal forall (X : Type) (P : X -> Prop),
  ~(exists x, P x) -> forall x, ~P x.
Proof.
(* your proof here *)
Abort.


(** *** 1.3  When [firstorder] reaches its limit: helping it with [assert] *)

(* [firstorder] performs a proof search with a bounded depth. Even a logically
   simple goal can therefore exceed this depth budget if the implication chain
   is long enough.

   The goal below is just a chain of 10 implications — in principle [firstorder]
   could solve it (one sequence of [apply]s works) — but in practice it times
   out at the default depth.

   Solution:
   1. Increase search depth with, e.g., [Set Firstorder Depth 5.]
      This might not be sustainable depending on the complexity of the problem.
   2. give [firstorder] a stepping stone. The tactic [assert (stmt) by
       tac] introduces [stmt] as a new hypothesis, proved on the fly by [tac].
       If we cut the chain in half, each half is only 5 steps, which is
       comfortably within [firstorder]'s reach.
 *)

Goal forall (T : Type) (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 : T -> Prop),
  (forall x, P1  x -> P2  x) ->
  (forall x, P2  x -> P3  x) ->
  (forall x, P3  x -> P4  x) ->
  (forall x, P4  x -> P5  x) ->
  (forall x, P5  x -> P6  x) ->
  (forall x, P6  x -> P7  x) ->
  (forall x, P7  x -> P8  x) ->
  (forall x, P8  x -> P9  x) ->
  (forall x, P9  x -> P10 x) ->
  (forall x, P10 x -> P11 x) ->
  forall x, P1 x -> P11 x.
Proof.
intros T P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11.
intros H12 H23 H34 H45 H56 H67 H78 H89 H9_10 H10_11.
(* EXERCISE: At this point, try [firstorder.] directly.

     Then, try splitting the chain in half with an assert and finish with [firstorder.].
     Also, try various depth for firstorder and measure timing with [Time].
*)
Time firstorder.
Admitted.

(* Note: [assert (stmt).] (without the [by tac] suffix) introduces
   [stmt] as a new sub-goal that you prove interactively — useful when
   the intermediate step itself is non-trivial.  The SSReflect
   equivalent is [have h : stmt.] / [have h : stmt by tac.]. *)


(* ================================================================== *)
(** ** 2. Arithmetic decision procedures *)
(* ================================================================== *)

(* The proofs in nat.v required careful induction to establish
   arithmetic facts.  Rocq provides dedicated tactics that handle whole
   classes of arithmetic goals automatically. *)

(** *** 2.1  The [lia] tactic  (Linear Integer Arithmetic) *)

(* You saw [lia] used as "magic" in inductive.v.  Here we explain what
   it actually does.

   [lia] is a decision procedure for *linear* arithmetic over several
   implementations of natural numbers and integers in Rocq. "Linear" means
   every term is at most degree 1 — no product of two variables.

   [lia] can prove:
   - equalities and inequalities between linear arithmetic expressions
   - goals requiring case splits (e.g. [n <= m \/ m < n])
   - goals that follow by simple arithmetic from the hypotheses

   [lia] usually CANNOT prove goals involving multiplication of two
   variables.  For those, see [nia] below or [ring]. *)

Require Import Lia.

Goal forall n m : nat, n + m = m + n.
Proof.
intros n m.
(* This took induction in the first tutorial — [lia] handles it directly. *)
lia.
Qed.

Goal forall n m k : nat, n + (m + k) = (n + m) + k.
Proof.
lia.
Qed.

(* EXERCISE: go back to the first tutorial (nat.v / ssrnat.v) and tell
   which goals can be closed by [lia] alone. Try! *)


(** *** 2.2  Working with [lia] *)

(* Lia also works with integers *)

Require Import ZArith.
Local Open Scope Z_scope.
(* without general library on semirings, we switch "scopes"
   in order to pick the right set of operations *)

Goal forall a b : Z, a - b = -(b - a).
Proof.
lia.
Qed.

(* EXERCISES: be careful, fix the statements to avoid both traps *)
Goal forall a b c : Z, a <= b -> b <= c -> a <= c + b.
Proof.
  (* your proof here *)
Abort.

Close Scope Z_scope. (* back to nat scope, one may also use [%N]*)
Goal forall a b c : nat, a - b + c = a + (c - b).
Proof.
(* your proof here *)
Abort.

(** *** 2.3  The [ring] tactic *)

(* [ring] is a decision procedure for *equalities* in commutative
   (semi)rings.  Unlike [lia], it handles products of variables, but
   unlike [lia] it only proves equalities, not inequalities.

   [ring] works for [nat], [Z], [Q], [R], and any type declared as a
   (semi)ring for the [ring] tactic. When using mathcomp, the algebraic
   hierarchy also declare semirings and rings, and one needs the
   mathcomp algebra-tactics package to make [ring] work for mathcomp rings.
*)

Require Import Ring Arith.

Goal forall n m : nat, n * m = m * n.
Proof.
  intros n m.
  ring.
Qed.

(* EXERCISE: *)
Goal forall n m : nat, (n + m) * (n + m) = n*n + 2*n*m + m*m.
Proof.
(* your proof here *)
Abort.

(* EXERCISE: *)
Goal forall n m k : nat, (n + m) * k = n * k + m * k.
Proof.
(* your proof here *)
Abort.

(* [ring] over [Z]: *)
Local Open Scope Z_scope.

Goal forall a b : Z, (a + b) * (a - b) = a * a - b * b.
Proof.
intros a b.
ring_simplify.    (* imagine you did not know the right-hand side *)
ring.
Qed.

(* EXERCISE: prove the classical identity for the square of a sum of
   three terms.  You will need to figure out the right-hand side
   yourself; [ring] will close whichever normal form you pick. *)
Goal forall a b c : Z,
    (a + b + c)^2 = 0.   (* replace 0 by the real right-hand side,
                            do not hesitate asking Rocq for some help *)
Proof.
  (* your proof here *)
Abort.

Close Scope Z_scope.

(* [ring] over the reals [R]: *)

From Stdlib Require Import Reals.
Local Open Scope R_scope.

Goal forall x y : R, (x - y) * (x + y) = x^2 - y^2.
Proof.
intros x y.
ring.
Qed.

Close Scope R_scope.


(** *** 2.4  The [field] tactic *)

(* [field] extends [ring] to fields ([Q], [R], …).  It proves equalities
   involving division, provided denominators can be shown to be nonzero.

   When denominators might be zero, [field] generates side-goals asking
   you to prove they are not. *)

Local Open Scope R_scope.

Goal forall x : R, x <> 0 -> x / x = 1.
Proof.
intros x Hx.
field.
exact Hx.
Qed.

Goal forall x y : R, x <> 0 -> y <> 0 ->
  1/x + 1/y = (x + y) / (x * y).
Proof.
intros x y Hx Hy.
field.
(* [field] leaves us the side-goal that denominators are nonzero. *)
split.
- exact Hy.
- exact Hx.
Qed.

(* CAVEAT: this style is not stable — a slight change in the statement
   can reorder the generated sub-goals, breaking the script: *)

Goal forall x y : R, x <> 0 -> y <> 0 ->
  1/x + 1/y = (x + y) / (y * x).   (* note: y * x instead of x * y *)
Proof.
intros x y Hx Hy.
field.
split.
- Fail exact Hy.
Abort.

(* EXERCISE: fix the script.  The cleanest robust fix is to chain
   [field] with a finisher that does not depend on the order or shape
   of the side-conditions.
   Prove the lemma this way. *)
Goal forall x y : R, x <> 0 -> y <> 0 ->
  1/x + 1/y = (x + y) / (y * x).
Proof.
(* your proof here *)
Admitted.

(* Test whether your script still works *)
Goal forall x y : R, x <> 0 /\ y <> 0 ->
  1/x + 1/y = (x + y) / (y * x).
Proof.
(* your proof here *)
Admitted.

Close Scope R_scope.


(* ================================================================== *)
(** ** 3. A typeclasses tutorial *)
(* ================================================================== *)

(* Rocq has several "ad-hoc polymorphism" facilities:
   - typeclasses
   - canonical structures
   - Hierarchy Builder (HB)
   Here we present typeclasses, the simplest one to grasp; the
   principle is the same for the other two.
   For larger examples I recommend HB (see Quentin Vermande's HB tutorial:
   https://rocq-prover.org/platform-docs/hierarchy_builder/tutorial_basics.v)
*)

(** *** 3.1  The [Monoid] class *)

(* A typeclass is a record parameterised by a carrier type, containing
   both the operations and the laws they must satisfy. *)

Class Monoid (M : Type) := {
  op   : M -> M -> M;
  e    : M;
  opA  : forall x y z, op x (op y z) = op (op x y) z;
  e_op : forall x, op e x = x;
  op_e : forall x, op x e = x;
}.


(** *** 3.2  Instances *)

(* An [Instance] provides concrete values for every field of a class,
   so that generic lemmas can be specialised automatically. *)

Instance nat_add_monoid : Monoid nat := {
  op   := Nat.add;
  e    := 0;
  opA  := Nat.add_assoc;
  e_op := Nat.add_0_l;
  op_e := Nat.add_0_r;
}.


(** *** 3.3  A first generic lemma *)

(* The [`{Monoid M}] binder says: assume a [Monoid M] instance is
   available in the context.  Rocq will find it automatically when we
   [apply] the lemma. *)

Lemma op_e_e (M : Type) `{Monoid M} : op e e = e.
Proof.
apply: e_op.
Qed.

(* Because [nat] has a [Monoid] instance for addition, [op_e_e]
   specialises automatically to [0 + 0 = 0]: *)

Goal 0 + 0 = 0.
Proof.
apply: op_e_e.
Qed.

(* QUESTION: could we make the following work with an appropriate [Monoid nat]
   instance for multiplication? What would happen to the previous goal if we
   defined such an instance? (Spoiler: there would be two competing [Monoid nat]
   instances, and Rocq would not be so good at picking the — this is exactly the
   previous one again.
   There are several ways to work around this problem, and the most well known
   is to define one *class* per operation (e.g. AddMonoid, MulMonoid, etc).
   Sidequest: define them!
*)

(*
Goal 1 * 1 = 1.
Proof.
  apply: op_e_e.
Qed.
*)


(** *** 3.4  Uniqueness of the neutral element *)

(* EXERCISE: show that if [x] behaves like a left neutral, then [x = e]. *)
Lemma e_unique (M : Type) `{Monoid M} (x : M) :
  (forall y, op x y = y) -> x = e.
Proof.
(* your proof here *)
Admitted.

Goal forall x : nat, (forall y, x + y = y) -> x = 0.
Proof.
apply: e_unique.
Qed.

(* Sidequest: derive the same lemma for AddMonoid and MulMonoid if you defined them. *)


(** *** 3.5  Commutative monoids *)

(* Classes can extend other classes.  The [::] field tells Rocq that a
   [CMonoid M] instance is also a [Monoid M] instance (so lemmas over
   [Monoid] apply automatically). *)

Class CMonoid (M : Type) := {
  CMonoid_Monoid :: Monoid M;
  opC : forall x y, op x y = op y x;
}.

Instance nat_add_cmonoid : CMonoid nat := {
  CMonoid_Monoid := nat_add_monoid;
  opC := Nat.add_comm;
}.

Lemma opCA (M : Type) `{CMonoid M} (x y z : M) :
  op x (op y z) = op y (op x z).
Proof.
(* your proof here *)
Admitted.

Goal forall n m k : nat, n + (m + k) = m + (n + k).
Proof.
(* Use the generic lemma opCA here! *)
Admitted.


(** *** 3.6  Groups *)

Class Group (G : Type) := {
  Group_Monoid :: Monoid G;
  inv    : G -> G;
  inv_op : forall x, op (inv x) x = e;
  op_inv : forall x, op x (inv x) = e;
}.

From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Instance Z_add_monoid : Monoid Z := {
  op   := Z.add;
  e    := 0;
  opA  := Z.add_assoc;
  e_op := Z.add_0_l;
  op_e := Z.add_0_r;
}.

Instance Z_add_group : Group Z.
Proof.
  refine {| Group_Monoid := Z_add_monoid; inv := Z.opp |}.
  - exact Z.add_opp_diag_l.
  - exact Z.add_opp_diag_r.
Defined.

Lemma inv_inv (G : Type) `{Group G} (x : G) : inv (inv x) = x.
Proof.
  rewrite -(e_op (inv (inv x))).
  rewrite -(op_inv x).
  rewrite -opA.
  rewrite op_inv.
  apply: op_e.
Qed.

Goal forall x : Z, - - x = x.
Proof.
  apply: inv_inv.
Qed.

(* EXERCISE: prove that the inverse of a product is the product of
   inverses in reverse order. *)
Lemma inv_op_distr (G : Type) `{Group G} (x y : G) :
  inv (op x y) = op (inv y) (inv x).
Proof.
  (* your proof here *)
Admitted.


(** *** 3.7  Parameterised instances: function spaces *)

From Stdlib Require Import FunctionalExtensionality.
Close Scope Z_scope.

(* If [M] is a monoid, then [A -> M] is a monoid with pointwise
   operations.  The instance is [`{Monoid M}]-parameterised: Rocq will
   build a [Monoid (A -> M)] whenever it can find a [Monoid M]. *)

Instance fun_monoid (A M : Type) `{Monoid M} : Monoid (A -> M).
Proof.
  refine {|
    op := fun f g => fun x => op (f x) (g x);
    e  := fun _ => e;
  |}.
  - move=> f g h; apply: functional_extensionality; move=> x /=.
    exact: opA.
  - move=> f; apply: functional_extensionality; move=> x /=.
    exact: e_op.
  - move=> f; apply: functional_extensionality; move=> x /=.
    exact: op_e.
Defined.

Example sum_fun (f g : nat -> nat) : op f g = fun x => f x + g x.
Proof. reflexivity. Qed.

Example e_fun : e = (fun _ : nat => 0).
Proof. reflexivity. Qed.

(** *** 3.8  Endomaps as a non-commutative monoid *)

(* primitive projections also turn on an additional definitional equality,
   that is [forall x : endo A, {| fn := fn x |}]
*)
#[projections(primitive)]
Record endo (A : Type) := Endo { fn : A -> A }.
Arguments Endo {A}.
Arguments fn {A}.

Definition endo_compose {A} (f g : endo A) : endo A :=
  Endo (fun x => fn f (fn g x)).

Definition endo_id {A} : endo A := Endo (fun x => x).

Instance endo_monoid (A : Type) : Monoid (endo A).
Proof.
(* start with a refine, and then your proofs. *)
Admitted.

(* ================================================================== *)
(** ** 4. (SSReflect / MathComp) Boolean reflection *)
(* ================================================================== *)

(* We now switch to the MathComp world, which provides a very rich
   library of formalised mathematics strongly using *boolean reflection*

   Two notions of "truth" in Rocq:
   - Computational: a boolean [b : bool] evaluating to [true] / [false].
   - Logical:       a proposition [P : Prop] proved by a derivation.

   MathComp connects them with the [reflect] predicate:
       [reflect P b]
   means [P] (a Prop) holds iff [b] (a bool) equals [true].
 *)

From mathcomp Require Import all_ssreflect zify.
(*  We also import the [zify] module that makes [lia] work with MathComp's [nat] *)

(** *** 4.1  The [reflect] predicate *)

About reflect.
Print reflect.
(* reflect : Prop -> bool -> Prop *)

(* Facts about reflect *)
Search reflect in ssr.ssreflect ssr.ssrbool eqtype.
(* idP: forall {b1 : bool}, reflect b1 b1 *)
(* decP: forall [P : Prop] [b : bool], reflect P b -> decidable P *)
(* rwP: forall [P : Prop] [b : bool], reflect P b -> P <-> b *)
(* equivP: forall [P Q : Prop] [b : bool], reflect P b -> P <-> Q -> reflect Q b *)

(* There is also a generic [eqP] witnesses for equality reflection *)
Check @eqP.
(* forall (T : eqType) (x y : T), reflect (x = y) (x == y) *)

(* Here, [eqType] stands for any type for which an equality decision procedure
   exists, which is the case for [nat], [bool], etc *)
(* Here, [x == y] is a boolean test; [x = y] is a proposition.
   [eqP] says they are equivalent.
   One switches between the two with *view* via [move/eqP] and [apply/eqP]. *)

Goal forall m n : nat, m == n -> m = n.
Proof.
  move=> m n.
  (* [move/eqP] "reads" the boolean [m == n] through the [eqP] *view*,
     turning the hypothesis into the proposition [m = n]. *)
  move/eqP.
  done.
Qed.

Goal forall m n : nat, m = n -> m == n.
Proof.
  move=> m n Heq.
  (* [apply/eqP] applies to the goal instead of the hypothesis. *)
  by apply/eqP.
Qed.


(** *** 4.2  Boolean connectives *)

(* MathComp uses [&&] / [||] for boolean conjunction / disjunction,
   connected to [/\] / [\/] via [andP] / [orP]. *)

Check @andP.     (* reflect (b1 /\ b2) (b1 && b2) *)
Check @orP.      (* reflect (b1 \/ b2) (b1 || b2) *)

Goal forall b1 b2 : bool, b1 && b2 = b2 && b1.
Proof.
  move=> b1 b2.
  by rewrite andbC.
Qed.

Goal forall b : bool, b || ~~ b = true.
Proof.
  move=> b.
  by case: b.
Qed.

(* EXERCISE: prove De Morgan's law in the boolean world. *)
Goal forall b1 b2 : bool, ~~ (b1 && b2) = ~~ b1 || ~~ b2.
Proof.
Abort.


(** *** 4.3  MathComp's [ssrnat] library *)

(* [ssrnat] provides every arithmetic lemma we proved manually in the
   first tutorial, and hundreds more.
   Naming follows a systematic naming convention:
   - [addnC]   : commutativity of [+]
   - [addnA]   : associativity of [+]
   - [mulnC]   : commutativity of [*]
   - [mulnDl]  : left distributivity of [*] over [+]
   - [muln0]   : [n * 0 = 0]
   - [mul1n]   : [1 * n = n]
*)

About addnC.
About mulnDl.

Goal forall n m : nat, n + m = m + n.
Proof.
  move=> n m.
  by rewrite addnC.
Qed.

Goal forall n m : nat, 2 ^ (n + m) = 2 ^ n * 2 ^ m.
Proof.
intros.
(*  This time lia, nia and ring fail *)
Abort.

(** *** 4.4  SSReflect automation combinators *)

(* SSReflect provides several short forms for finishing goals:

     [by tac]   — apply [tac]; if any goal remains, fail
     [done]     — close a goal by trivial steps
     [//]       — embedded [done] inside a tactic chain
     [//=]      — embedded [done] after [simpl]
     [=> //]    — introduce and immediately close trivial sub-goals
*)

Goal forall n : nat, n + 0 = n.
Proof.
  by move=> n; rewrite addn0.
Qed.

Goal forall n : nat, 0 + n = n.
Proof.
  by [].                       (* [add0n] is "done-level" knowledge *)
Qed.


(** *** 4.5  The [have] tactic *)

(* [have] introduces an intermediate lemma inline, without leaving the
   current proof.  Shape:
       [have h : stmt by tac.]      — prove [stmt] with [tac], name it [h]
       [have h : stmt. tac.]        — prove [stmt] interactively
   It is one of the most useful SSReflect tactics. *)

Goal forall n m k : nat, n + m + k = (m + n) + k.
Proof.
  move=> n m k.
  have h : n + m = m + n by apply: addnC.
  by rewrite h.
Qed.

(* [have] with just a statement creates a new sub-goal: *)

Goal forall n : nat, n <= n + n.
Proof.
  move=> n.
  have h : n + 0 <= n + n by rewrite leq_add2l.
  by rewrite addn0 in h.
Qed.

(* ================================================================== *)
(** ** 5. Navigating the libraries *)
(* ================================================================== *)

(* Rocq's libraries, Stdlib, Mathcomp and many other contains thousands of
   lemmas. Knowing how to find the right one is as important as knowing
   tactics. *)

(** *** 5.1  [Search] (advanced patterns) *)

(* Search for every lemma about the length of a reversed list: *)
Search (size (rev _)).

(* Search using a name fragment (as a string): *)
Search "size".

(* Search for lemmas matching a pattern with multiple placeholders: *)
Search (_ ++ _ = _ ++ _).

(* Search filtered to a specific module: *)
Search (_ <= _) in ssrnat.

(** *** 4.2  [Check], [Print], [Locate] *)

(* [Check] displays the type of an expression. *)
Check addnC.
Check size_rev.

(* [Print] displays the complete definition. *)
Print addn.

(* [Locate] finds where a notation or identifier is defined — very useful when
   you see an unfamiliar symbol or if you do not know which scope you are in, or
   which scope the notation is in. *)
Locate "_ ++ _".


(** *** 4.3  Important library modules *)

(* Stdlib
   - [Arith], [PeanoNat]  : arithmetic on [nat]
   - [ZArith]             : integers [Z]
   - [QArith]             : rationals [Q]
   - [Reals]              : real numbers [R]
   - [List]               : polymorphic lists
   - [Bool]               : booleans
   - [Logic]              : core logical infrastructure
   - [Lia]                : the [lia] tactic
   - [Ring], [Field]      : the [ring] and [field] tactics
   - [Classical]          : classical logic axioms
see https://rocq-prover.org/doc/V9.1.0/refman-stdlib/index.html
*)

(* Mathcomp
  - [ssrnat]:             : arithmetic on [nat]
  - [div], [prime]        : divisibility and primaliry in [nat]
  - [seq]                 : reasnoning about lists
  - [fintype]             : finite types
  - [bigop]               : iterating monoid operations
  see https://math-comp.github.io/

*)


(* ================================================================== *)
(** ** 6. Divisibility in MathComp *)
(* ================================================================== *)

(* MathComp's [div] module provides divisibility as a *boolean*
   predicate:
       [d %| n : bool]
   which evaluates to [true] iff [d] divides [n]. *)

Search "dvdn".

(* Key lemmas we will use: *)

Check dvdn0.        (* d %| 0                                          *)
Check dvdnn.        (* d %| d                                          *)
Check dvd1n.        (* 1 %| n                                          *)
Check dvdn_trans.   (* d %| m -> m %| n -> d %| n                      *)
Check dvdn_add.     (* d %| m -> d %| n -> d %| m + n                  *)
Check dvdn_mulr.    (* d %| m -> d %| m * n                            *)
Check dvdn_mull.    (* d %| n -> d %| m * n                            *)
Check dvdnP.        (* reflect (exists k, n = d * k) (d %| n)          *)


(** *** 6.1  Warm-up *)

(* EXERCISE: use [dvd1n]. *)
Goal forall n : nat, 1 %| n.
Proof.
  (* your proof here *)
Admitted.

Goal forall d : nat, d %| 0.
Proof.
  move=> d.
  exact: dvdn0.
Qed.


(** *** 6.2  Linear combinations *)

(* EXERCISE: if [d] divides both [m] and [n], it divides any linear
   combination [a * m + b * n].
   Hint 1: decompose the goal with [dvdn_add].
   Hint 2: then use [dvdn_mull] on each side. *)
Lemma dvdn_lincomb (d m n a b : nat) :
  d %| m -> d %| n -> d %| a * m + b * n.
Proof.
  (* your proof here *)
Admitted.


(** *** 6.3  Product of two consecutive integers is even *)

(* A folklore result: [n * (n+1)] is always even, i.e. [2 %| n * n.+1]. *)

Lemma two_dvd_consecutive n : 2 %| n * n.+1.
Proof.
(* your proof here *)
Admitted.


(** *** 6.4  Challenge: product divides product *)

(* EXERCISE: if [a %| m] and [b %| n], then [a * b %| m * n].
   The proof starts by destructing both divisibility hypotheses with
   the view [/dvdnP]; we exhibit the witness and are then left with
   an equality of natural numbers.
   Hint: [mulnACA : m * n * (p * q) = m * p * (n * q)]. *)
Lemma dvdn_mul_mul a b m n :
  a %| m -> b %| n -> a * b %| m * n.
Proof.
  (* your proof here *)
Admitted.


(* ================================================================== *)
(** ** 7. Big operators *)
(* ================================================================== *)

(* MathComp's [bigop] library provides a uniform notation for iterated
   operations — sums, products, maxima, concatenations — over a finite
   range.

   The basic forms:
       \sum_(i <- r) F i           sum over a list [r]
       \sum_(i < n) F i            sum indexed by [i : 'I_n]
       \sum_(m <= i < n) F i       sum over a numeric range
       \sum_(i in A) F i           sum over a finite set [A]

   The same syntax works with [\prod] for products, [\max] for maxima,
   and [\big[op/idx]_(...) F i] for an arbitrary operation [op] with
   neutral element [idx]. *)


(** *** 7.1  First examples *)

(* [big_ord_recl] / [big_ord_recr] split off the first / last element;
   [big_ord0] says the empty sum is the identity element.
   [/=] forces simpl after each rewrite, which fires the numeric
   computation. *)

Example sum_0_to_4 : \sum_(i < 5) i = 10.
Proof.
  by rewrite !big_ord_recl big_ord0.
Qed.

Example prod_1_to_4 : \prod_(i < 4) i.+1 = 24.
Proof.
  by rewrite !big_ord_recl big_ord0.
Qed.


(** *** 7.2  Key lemmas *)
(* You may use any lemma from the library to do the following exercises *)
Check big_ord_recl.    (* split off the first term              *)
Check big_ord_recr.    (* split off the last term               *)
Check big_ord0.        (* [\op_(i < 0) F i = idx]               *)
Check big_split.       (* split a sum of sums                   *)
Check big_const_ord.   (* sum / product of a constant           *)
Check big_distrl.      (* [(\sum_i f i) * c = \sum_i (f i * c)] *)
Check big_distrr.      (* [c * (\sum_i f i) = \sum_i (c * f i)] *)
Check exchange_big.    (* Swap nested sums                      *)

(** *** 7.3  EXERCISE: sum of zeros *)

(* Hint: [big1_eq] — the sum of the identity element is the identity. *)
Goal forall n : nat, \sum_(i < n) 0 = 0.
Proof.
  (* your proof here *)
Admitted.


(** *** 7.4  EXERCISE: sum of a constant *)

(* Hint 1: induction on [n] with [big_ord_recr] works.
   Hint 2: [mulSnr : n.+1 * m = n * m + m] or [mulnSr]. *)
Goal forall n c : nat, \sum_(i < n) c = n * c.
Proof.
  (* your proof here *)
Admitted.


(** *** 7.5  EXERCISE: linearity of sums *)

Goal forall n (f g : nat -> nat),
  \sum_(i < n) (f i + g i) = \sum_(i < n) f i + \sum_(i < n) g i.
Proof.
  (* your proof here *)
Admitted.


(** *** 7.6  EXERCISE: factoring a constant *)

Goal forall n c (f : nat -> nat),
  c * \sum_(i < n) f i = \sum_(i < n) (c * f i).
Proof.
  (* your proof here *)
Admitted.


(** *** 7.7  EXERCISE: swapping the order of summation *)

(* The lemma [exchange_big] is MathComp's exchange of summation. *)
Goal forall n m (f : nat -> nat -> nat),
  \sum_(i < n) \sum_(j < m) f i j = \sum_(j < m) \sum_(i < n) f i j.
Proof.
Admitted.


(** *** 7.8  CHALLENGE: a double sum *)

(* Summing [f i + f j] over all pairs [(i, j)] with [i < n] and [j < m]
   factors into two single sums. 
   Hints: [big_split] (inside the inner sum), then the constant-sum
   and linearity-of-sum lemmas above. *)
Goal forall (n m : nat) (f : nat -> nat),
  \sum_(i < n) \sum_(j < m) (f i + f j)
    = m * \sum_(i < n) f i + n * \sum_(j < m) f j.
Proof.
move=> n m f.
under eq_bigr do rewrite big_split//=.
Admitted.


(** *** 7.9  CHALLENGE: Gauss's formula *)

(* The classical identity [0 + 1 + 2 + ... + n = n(n+1)/2]. *)

Lemma gauss n : \sum_(i < n.+1) i = n * n.+1 %/ 2.
Proof.
    (* your proof here *)
Admitted.


(** *** 7.10  CHALLENGE: sum of the first [n] odd numbers *)

(* A beautiful identity: [1 + 3 + 5 + ... + (2n-1) = n^2].
   State it and prove it! *)


(* ================================================================== *)
(** ** Summary *)
(* ================================================================== *)

(**
   Tactic           | What it proves
   -----------------+-------------------------------------------------
   [tauto]          | Propositional intuitionistic tautologies
   [firstorder]     | First-order tautologies (incomplete, slower)
   [lia]            | Linear arithmetic over [nat] / [Z]
   [nia]            | Non-linear arithmetic (polynomial, via [zify])
   [ring]           | Equalities in commutative (semi)rings
   [ring_simplify]  | Normalise a ring expression without closing
   [field]          | Equalities in fields, with nonzero side goals
   [done] / [by]    | (SSReflect) finish with trivial steps
   [have]           | (SSReflect) introduce an intermediate lemma
   [assert]         | (vanilla) introduce an intermediate lemma

   Command          | Purpose
   -----------------+-------------------------------------------------
   [Search] patt    | Find lemmas matching a pattern or name
   [Check] e        | Display the type of [e]
   [About] e        | Display information about [e] including its type
   [Print] id       | Display the full definition of [id]
   [Locate] s       | Find where a notation or name is defined
   [Fail] tac       | Succeed iff [tac] fails — useful for tests
   [timeout n tac]  | Abort [tac] if it takes more than [n] seconds

   MathComp idioms  | Purpose
   -----------------+-------------------------------------------------
   [d %| n]         | Boolean divisibility; see [div]
   [x == y]         | Boolean equality; reflected by [eqP]
   [\sum_(i < n) F] | Finite sum; see [bigop]
   [\prod_(i < n) F]| Finite product

   Big-operator lemmas | What they say
   --------------------+----------------------------------------------
   [big_ord_recl]      | split off the first term
   [big_ord_recr]      | split off the last term
   [big_ord0]          | empty range = identity
   [big1_eq]           | [\op_(i) idx = idx]
   [big_split]         | split a sum of sums
   [big_const_ord]     | sum / product of a constant
   [big_distrl]        | [(\sum_i f i) * c = \sum_i (f i * c)]
   [big_distrr]        | [c * (\sum_i f i) = \sum_i (c * f i)]
   [exchange_big]      | swap nested sums
*)
