(**************************************************************)
(* FSetDecide.v                                               *)
(*                                                            *)
(* Author: Aaron Bohannon                                     *)
(**************************************************************)

(** This file implements a decision procedure for a certain
    class of statements involving finite sets.  *)

Require Import FSets.
Require Import Negation.

Module Decide (Import M : S).

(** * Overview
    This module defines the tactic [decideFSet], which will
    solve any valid goal of the form
    [ forall s1 ... sn,
      forall x1 ... xm,
      P1 -> ... -> Pk -> P ]
    where [P]'s are defined by the grammar:
<<

P ::=
| Q
| Empty F
| Subset F F'
| Equal F F'

Q ::=
| E.eq X X'
| In X F
| Q /\ Q'
| Q \/ Q'
| Q -> Q'
| Q <-> Q'
| ~ Q
| True
| False

F ::=
| S
| empty
| singleton X
| add X F
| remove X F
| union F F'
| inter F F'
| diff F F'

X ::= x1 | ... | xm
S ::= s1 | ... | sn

>>

The tactic will also work on some goals that vary slightly from
the above form:
- The variables and hypotheses may be mixed in any order and
  may have already been introduced into the context.  Moreover,
  there may be additional, unrelated hypotheses mixed in
  (these will be ignored).
- A conjunction of hypotheses will work equally well as
  separated hypotheses, i.e., [P1 /\ P2 -> P] can be solved
  if [P1 -> P2 -> P] can be solved.
- [decideFSet] should solve any goal if the FSet-related
  hypotheses are contradictory.
- [decideFSet] will first perform any necessary zeta and beta
  reductions and will invoke [subst] to eliminate any Coq
  equalities between finite sets or their elements.
- If [E.eq] is convertible with Coq's equality, it will not
  matter which one you use.
- The tactic can solve goals where the finite sets or set
  elements are expressed by Coq terms other than variables.
  However, non-local definitions are not expanded, and Coq
  equalities between non-variable terms are not used.
  For example, this goal can be solved:
  [ forall (f : t -> t),
    forall (g : elt -> elt),
    forall (s1 s2 : t),
    forall (x1 x2 : elt),
    Equal s1 (f s2) ->
    E.eq x1 (g (g x2)) ->
    In x1 s1 ->
    In (g (g x2)) (f s2) ]
  This one cannot be solved:
  [ forall (f : t -> t),
    forall (g : elt -> elt),
    forall (s1 s2 : t),
    forall (x1 x2 : elt),
    Equal s1 (f s2) ->
    E.eq x1 (g x2) ->
    In x1 s1 ->
    g x2 = g (g x2) ->
    In (g (g x2)) (f s2) ]
*)

  (** * Generic Tactics
      We begin by defining a few generic, useful tactics. *)

  (** [if t then t1 else t2] executes [t] and, if it does not
      fail, then [t1] will be applied to all subgoals produced.
      If [t] fails, then [t2] is executed. *)
  Tactic Notation
    "if" tactic(t)
    "then" tactic(t1)
    "else" tactic(t2) :=
    first [ t; first [ t1 | fail 2 ] | t2 ].

  (** [prop P holds by t] succeeds (but does not modify the goal
      or context) if the proposition [P] can be proved by [t] in
      the current context.  Otherwise, the tactic fails. *)
  Tactic Notation "prop" constr(P) "holds" "by" tactic(t) :=
    let H := fresh in
    assert P as H by t;
    clear H.

  (** This tactic acts just like [assert ... by ...] but will
      fail if the context already contains the proposition. *)
  Tactic Notation "assert" "new" constr(e) "by" tactic(t) :=
    match goal with
    | H: e |- _ => fail 1
    | _ => assert e by t
    end.

  (** [subst++] is similar to [subst] except that
      - it never fails (as [subst] does on recursive equations),
      - it substitutes locally defined variable for their
        definitions,
      - it performs beta reductions everywhere, which may arise
        after substituting a locally defined function for its
        definition.
      *)
  Tactic Notation "subst" "++" :=
    repeat (
      match goal with
      | x : _ |- _ => subst x
      end);
    cbv zeta beta in *.

  (** If you have a negated goal and [H] is a negated
      hypothesis, then [contra H] exchanges your goal and [H],
      removing the negations. *)
  Ltac contra H :=
    let J := fresh in
    unfold not;
    unfold not in H;
    intros J;
    apply H;
    clear H;
    rename J into H.

  (** [decompose records] calls [decompose record H] on every
      relevant hypothesis [H]. *)
  Tactic Notation "decompose" "records" :=
    repeat (
      match goal with
      | H: _ |- _ => progress (decompose record H); clear H
      end).

  (** * Auxiliary FSet Tactics *)

  (** ** Discarding Irrelevant Hypotheses
      We will want to clear the context of any non-FSet-related
      hypotheses in order to increase the speed of the tactic.
      To do this, we will need to be able to decide which are
      relevant.  We do this by making a simple inductive
      definition classifying the propositions of interest. *)

  Inductive FSet_elt_Prop : Prop -> Prop :=
  | eq_Prop : forall (S : Set) (x y : S),
      FSet_elt_Prop (x = y)
  | eq_elt_prop : forall x y,
      FSet_elt_Prop (E.eq x y)
  | In_elt_prop : forall x s,
      FSet_elt_Prop (In x s)
  | True_elt_prop :
      FSet_elt_Prop True
  | False_elt_prop :
      FSet_elt_Prop False
  | conj_elt_prop : forall P Q,
      FSet_elt_Prop P ->
      FSet_elt_Prop Q ->
      FSet_elt_Prop (P /\ Q)
  | disj_elt_prop : forall P Q,
      FSet_elt_Prop P ->
      FSet_elt_Prop Q ->
      FSet_elt_Prop (P \/ Q)
  | impl_elt_prop : forall P Q,
      FSet_elt_Prop P ->
      FSet_elt_Prop Q ->
      FSet_elt_Prop (P -> Q)
  | not_elt_prop : forall P,
      FSet_elt_Prop P ->
      FSet_elt_Prop (~ P).

  Inductive FSet_Prop : Prop -> Prop :=
  | elt_FSet_Prop : forall P,
      FSet_elt_Prop P ->
      FSet_Prop P
  | Empty_FSet_Prop : forall s,
      FSet_Prop (Empty s)
  | Subset_FSet_Prop : forall s1 s2,
      FSet_Prop (Subset s1 s2)
  | Equal_FSet_Prop : forall s1 s2,
      FSet_Prop (Equal s1 s2).

  (** Here is the tactic that will throw away hypotheses that
      are not useful (for the intended scope of the [decideFSet]
      tactic). *)
  Hint Constructors FSet_elt_Prop FSet_Prop : FSet_Prop.
  Ltac discard_non_FSet :=
    decompose records;
    repeat (
      match goal with
      | H : ?P |- _ =>
        if prop (FSet_Prop P) holds by (auto 100 with FSet_Prop)
        then fail
        else clear H
      end).

  (** ** Replacing Set Operators with Propositional Connectives
      The lemmas from [FSetFacts] will be used to break down set
      operations into propositional formulas built over the
      predicates [In] and [E.eq] applied only to variables.  We
      are going to use them with [autorewrite]. *)
  Module F := FSetFacts.Facts M.
  Hint Rewrite
    F.empty_iff F.singleton_iff F.add_iff F.remove_iff
    F.union_iff F.inter_iff F.diff_iff
  : set_simpl.

  (** ** Decidability of FSet Propositions *)

  (** [In] is decidable. *)
  Module D := DepOfNodep M.
  Lemma dec_In : forall x s,
    decidable (In x s).
  Proof.
    intros x s. red. destruct (D.mem x s); auto.
  Qed.

  (** [E.eq] is decidable. *)
  Lemma dec_eq : forall (x y : E.t),
    decidable (E.eq x y).
  Proof.
    intros x y. red. destruct (E.compare x y); auto.
  Qed.

  (** The hint database [FSet_decidability] will be given to the
      [push_neg] tactic from the module [Negation]. *)
  Hint Resolve dec_In dec_eq : FSet_decidability.

  (** ** Normalizing Propositions About Equality
      We have to deal with the fact that [E.eq] may be
      convertible with Coq's equality.  Thus, we will find the
      following tactics useful to replace one form with the
      other everywhere. *)

  (** The next tactic, [Logic_eq_to_E_eq], mentions the term
      [E.t]; thus, we must ensure that [E.t] is used in favor of
      any other convertible but syntactically distinct term. *)
  Ltac change_to_E_t :=
    repeat (
      match goal with
      | H : ?T |- _ =>
        progress (change T with E.t in H);
        repeat (
          match goal with
          | J : _ |- _ => progress (change T with E.t in J)
          | |- _ => progress (change T with E.t)
          end )
      end).

  (** These two tactics take us from Coq's built-in equality to
      [E.eq] (and vice versa) when possible. *)

  Ltac Logic_eq_to_E_eq :=
    repeat (
      match goal with
      | H: _ |- _ =>
        progress (change (@Logic.eq E.t) with E.eq in H)
      | |- _ =>
        progress (change (@Logic.eq E.t) with E.eq)
      end).

  Ltac E_eq_to_Logic_eq :=
    repeat (
      match goal with
      | H: _ |- _ =>
        progress (change E.eq with (@Logic.eq E.t) in H)
      | |- _ =>
        progress (change E.eq with (@Logic.eq E.t))
      end).

  (** This tactic works like the built-in tactic [subst], but at
      the level of set element equality (which may not be the
      convertible with Coq's equality). *)
  Ltac substFSet :=
    repeat (
      match goal with
      | H: E.eq ?x ?y |- _ => rewrite H in *; clear H
      end).

  (** ** Taking Decidability into Account
      This tactic adds assertions about the decidability of
      [E.eq] and [In] to the context.  This is necessary for the
      completeness of the [decideFSet] tactic.  However, in
      order to minimize the cost of proof search, we should be
      careful to not add more than we need.  Once negations have
      been pushed to the leaves of the propositions, we only
      need to worry about decidability for those atomic
      propositions that appear in a negated form.  (Well, at
      least that is what I believe, but I have not tried to
      prove it in any formal sense.) *)
  Ltac assert_decidability :=
    (** We actually don't want these rules to fire if the
        syntactic context in the patterns below is trivially
        empty, but we'll just do some clean-up at the afterward.
        *)
    repeat (
      match goal with
      | H: context [~ E.eq ?x ?y] |- _ =>
        assert new (E.eq x y \/ ~ E.eq x y) by (apply dec_eq)
      | H: context [~ In ?x ?s] |- _ =>
        assert new (In x s \/ ~ In x s) by (apply dec_In)
      | |- context [~ E.eq ?x ?y] =>
        assert new (E.eq x y \/ ~ E.eq x y) by (apply dec_eq)
      | |- context [~ In ?x ?s] =>
        assert new (In x s \/ ~ In x s) by (apply dec_In)
      end);
    (** Now we eliminate the useless facts we added (because
        they would likely be very harmful to performance). *)
    repeat (
      match goal with
      | _: ~ ?P, H : ?P \/ ~ ?P |- _ => clear H
      end).

  (** ** Handling [Empty], [Subset], and [Equal]
      This tactic instantiates universally quantified hypotheses
      (which arise from the unfolding of [Empty], [Subset], and
      [Equal]) for each of the set element expressions that is
      involved in some membership or equality fact.  Then it
      throws away those hypotheses, which should no longer be
      needed. *)
  Ltac inst_FSet_hypotheses :=
    repeat (
      match goal with
      | H : forall a : E.t, _,
        _ : context [ In ?x _ ] |- _ =>
        let P := type of (H x) in
        assert new P by (exact (H x))
      | H : forall a : E.t, _
        |- context [ In ?x _ ] =>
        let P := type of (H x) in
        assert new P by (exact (H x))
      | H : forall a : E.t, _,
        _ : context [ E.eq ?x _ ] |- _ =>
        let P := type of (H x) in
        assert new P by (exact (H x))
      | H : forall a : E.t, _
        |- context [ E.eq ?x _ ] =>
        let P := type of (H x) in
        assert new P by (exact (H x))
      | H : forall a : E.t, _,
        _ : context [ E.eq _ ?x ] |- _ =>
        let P := type of (H x) in
        assert new P by (exact (H x))
      | H : forall a : E.t, _
        |- context [ E.eq _ ?x ] =>
        let P := type of (H x) in
        assert new P by (exact (H x))
      end);
    repeat (
      match goal with
      | H : forall a : E.t, _ |- _ =>
        clear H
      end).

  (** * The [decideFSet] Tactic *)

  (** Here is the crux of the proof search.  Recursion
      through [intuition]!  (This will terminate unless I am
      rather mistaken about the behavior of [intuition].) *)
  Ltac decideFSet_rec :=
    try (match goal with
    | H: E.eq ?x ?x -> False |- _ => destruct H
    end);
    (reflexivity ||
     contradiction ||
     (progress substFSet; intuition decideFSet_rec)).

  (** If we add [unfold Empty, Subset, Equal in *; intros;] to
      the beginning of this tactic, it will satisfy the same
      specification as the [decideFSet] tactic; however, it will
      be much slower than necessary without the pre-processing
      done by the wrapper tactic [decideFSet]. *)
  Ltac decideFSet_body :=
    inst_FSet_hypotheses;
    autorewrite with set_simpl in *;
    push not in * using FSet_decidability;
    substFSet;
    assert_decidability;
    auto using E.eq_refl;
    (intuition decideFSet_rec) ||
    fail 1
      "because the goal is beyond the scope of this tactic".

  (** Here is the top-level tactic (the only one intended for
      clients of this library).  It's specification is given at
      the top of the file. *)
  Ltac decideFSet :=
    (** We fold occurrences of [not] because it is better for
        [intros] to leave us with a goal of [~ P] than a goal of
        [False].  [fold_nots] is defined in [Negation].
        *)
    unfold iff in *; fold any not in *; intros;
    (** Now we decompose conjunctions, which will allow the
        [discard_non_FSet] and [assert_decidability] tactics to
        do a much better job. *)
    decompose records;
    discard_non_FSet;
    unfold Empty, Subset, Equal in *;
    (** If our goal was [Empty], [Subset], or [Equal], then we
        have one more item to introduce now. *)
    intros;
    (** We now want to get rid of all uses of [=] in favor of
        [E.eq].  However, the best way to eliminate an [=] is
        with [subst], so we will try that first.  In fact, we
        may as well convert uses of [E.eq] into [=] before we do
        [subst] so that we can even more mileage out of it.
        Also, we use [change_to_E_t] to ensure that we have a
        canonical name for set elements, so that
        [Logic_eq_to_E_eq] will work properly.  *)
    change_to_E_t; E_eq_to_Logic_eq; subst++; Logic_eq_to_E_eq;
    (** The next optimization is to swap a negated goal with a
        negated hypothesis when possible.  Any swap will improve
        performance, but we will get the maximum benefit if we
        swap the goal with a hypotheses mentioning the same set
        element, so we try that first.  Of course, to maintain
        completeness of this tactic, we can only perform such a
        swap with a decidable proposition; hence, we first test
        whether the hypothesis is an [FSet_elt_Prop] in the
        fourth branch (any [FSet_elt_Prop] is decidable). *)
    pull not using FSet_decidability;
    unfold not in *;
    match goal with
    | H: (In ?x ?r) -> False |- (In ?x ?s) -> False =>
      contra H; decideFSet_body
    | H: (In ?x ?r) -> False |- (E.eq ?x ?y) -> False =>
      contra H; decideFSet_body
    | H: (In ?x ?r) -> False |- (E.eq ?y ?x) -> False =>
      contra H; decideFSet_body
    | H: ?P -> False |- ?Q -> False =>
      if prop (FSet_elt_Prop P) holds by
        (auto 100 with FSet_Prop)
      then (contra H; decideFSet_body)
      else decideFSet_body
    | |- _ =>
      decideFSet_body
    end.

  (** * Examples *)

  Lemma test_eq_trans_1 : forall x y z s,
    E.eq x y ->
    ~ ~ E.eq z y ->
    In x s ->
    In z s.
  Proof. decideFSet. Qed.

  Lemma test_eq_trans_2 : forall x y z r s,
    In x (singleton y) ->
    ~ In z r ->
    ~ ~ In z (add y r) ->
    In x s ->
    In z s.
  Proof. decideFSet. Qed.

  Lemma test_eq_neq_trans_1 : forall w x y z s,
    E.eq x w ->
    ~ ~ E.eq x y ->
    ~ E.eq y z ->
    In w s ->
    In w (remove z s).
  Proof. decideFSet. Qed.

  Lemma test_eq_neq_trans_2 : forall w x y z r1 r2 s,
    In x (singleton w) ->
    ~ In x r1 ->
    In x (add y r1) ->
    In y r2 ->
    In y (remove z r2) ->
    In w s ->
    In w (remove z s).
  Proof. decideFSet. Qed.

  Lemma test_In_singleton : forall x,
    In x (singleton x).
  Proof. decideFSet. Qed.

  Lemma test_Subset_add_remove : forall x s,
    s [<=] (add x (remove x s)).
  Proof. decideFSet. Qed.

  Lemma test_eq_disjunction : forall w x y z,
    In w (add x (add y (singleton z))) ->
    E.eq w x \/ E.eq w y \/ E.eq w z.
  Proof. decideFSet. Qed.

  Lemma test_not_In_disj : forall x y s1 s2 s3 s4,
    ~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
    ~ (In x s1 \/ In x s4 \/ E.eq y x).
  Proof. decideFSet. Qed.

  Lemma test_not_In_conj : forall x y s1 s2 s3 s4,
    ~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
    ~ In x s1 /\ ~ In x s4 /\ ~ E.eq y x.
  Proof. decideFSet. Qed.

  Lemma test_iff_conj : forall a x s s',
   (In a s' <-> E.eq x a \/ In a s) ->
   (In a s' <-> In a (add x s)).
  Proof. decideFSet. Qed.

  Lemma test_set_ops_1 : forall x q r s,
    (singleton x) [<=] s ->
    Empty (union q r) ->
    Empty (inter (diff s q) (diff s r)) ->
    ~ In x s.
  Proof. decideFSet. Qed.

  Lemma eq_chain_test : forall x1 x2 x3 x4 s1 s2 s3 s4,
    Empty s1 ->
    In x2 (add x1 s1) ->
    In x3 s2 ->
    ~ In x3 (remove x2 s2) ->
    ~ In x4 s3 ->
    In x4 (add x3 s3) ->
    In x1 s4 ->
    Subset (add x4 s4) s4.
  Proof. decideFSet. Qed.

  Lemma test_too_complex : forall x y z r s,
    E.eq x y ->
    (In x (singleton y) -> r [<=] s) ->
    In z r ->
    In z s.
  Proof.
    (** decideFSet is not intended to solve this directly. *)
    intros until s; intros Heq H Hr; lapply H; decideFSet.
  Qed.

  Lemma function_test_1 :
    forall (f : t -> t),
    forall (g : elt -> elt),
    forall (s1 s2 : t),
    forall (x1 x2 : elt),
    Equal s1 (f s2) ->
    E.eq x1 (g (g x2)) ->
    In x1 s1 ->
    In (g (g x2)) (f s2).
  Proof. decideFSet. Qed.

  Lemma function_test_2 :
    forall (f : t -> t),
    forall (g : elt -> elt),
    forall (s1 s2 : t),
    forall (x1 x2 : elt),
    Equal s1 (f s2) ->
    E.eq x1 (g x2) ->
    In x1 s1 ->
    g x2 = g (g x2) ->
    In (g (g x2)) (f s2).
  Proof.
    (** decideFSet is not intended to solve this directly. *)
    intros until 3. intros g_eq. rewrite <- g_eq. decideFSet.
  Qed.

End Decide.
