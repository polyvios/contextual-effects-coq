(**************************************************************)
(* Negation.v                                                 *)
(*                                                            *)
(* Author: Aaron Bohannon                                     *)
(**************************************************************)

(** This file provides some lemmas and tactics for manipulating
    uses of [not] in propositions.  A few assorted items are
    included that would make more sense in [Decidable.v] in the
    standard library. *)

Require Export Decidable.
Require Import Setoid.

(** * Some Lemmas and Tactics About Decidable Propositions *)

Lemma dec_iff : forall P Q : Prop,
  decidable P ->
  decidable Q ->
  decidable (P <-> Q).
Proof.
  unfold decidable in *. tauto.
Qed.

(** With this hint database, we can leverage [auto] to check
    decidability of propositions. *)
Hint Resolve
  dec_True dec_False dec_or dec_and dec_imp dec_not dec_iff
: decidable_prop.

(** [solve_decidable using lib] will solve goals about the
    decidability of a proposition, assisted by an auxiliary
    database of lemmas.  The database is intended to contain
    lemmas stating the decidability of additional propositions,
    (e.g., the decidability of equality on a particular
    inductive type). *)
Tactic Notation "solve_decidable" "using" ident(db) :=
  match goal with
  | |- decidable ?P =>
    solve [ auto 100 with decidable_prop db ]
  end.

Tactic Notation "solve_decidable" :=
  solve_decidable using core.

(** * Propositional Equivalences Involving Negation
    These are all written with the unfolded form of negation,
    since, in a situation (such as a tactic) where they will be
    used repeatedly, we don't want to have to interleave their
    uses with uses of [fold] or [unfold] to get their full
    benefit.  (For a specific example, consider what would
    happen if the first lemma [not_true_iff] were written as [~
    True <-> False].  How would it be used to replace [True ->
    (~ True)] with [False]?)
*)

(** ** Eliminating Negations
    We begin with lemmas that, when read from left to right, can
    be understood as ways to eliminate uses of [not]. *)

Lemma not_true_iff :
  (True -> False) <-> False.
Proof.
  tauto.
Qed.

Lemma not_false_iff :
  (False -> False) <-> True.
Proof.
  tauto.
Qed.

Lemma not_not_iff : forall P : Prop,
  decidable P ->
  (((P -> False) -> False) <-> P).
Proof.
  unfold decidable in *. tauto.
Qed.

Lemma contrapositive : forall P Q : Prop,
  decidable P ->
  (((P -> False) -> (Q -> False)) <-> (Q -> P)).
Proof.
  unfold decidable in *. tauto.
Qed.

Lemma and_not_l_iff_1 : forall P Q : Prop,
  decidable P ->
  ((P -> False) \/ Q <-> (P -> Q)).
Proof.
  unfold decidable in *. tauto.
Qed.

Lemma and_not_l_iff_2 : forall P Q : Prop,
  decidable Q ->
  ((P -> False) \/ Q <-> (P -> Q)).
Proof.
  unfold decidable in *. tauto.
Qed.

Lemma and_not_r_iff_1 : forall P Q : Prop,
  decidable P ->
  (P \/ (Q -> False) <-> (Q -> P)).
Proof.
  unfold decidable in *. tauto.
Qed.

Lemma and_not_r_iff_2 : forall P Q : Prop,
  decidable Q ->
  (P \/ (Q -> False) <-> (Q -> P)).
Proof.
  unfold decidable in *. tauto.
Qed.

Lemma imp_not_l : forall P Q : Prop,
  decidable P ->
  ((~ P -> Q) <-> (P \/ Q)).
Proof.
  unfold decidable in *. tauto.
Qed.

(** ** Pushing Negations Around
    We have four lemmas that, when read from left to right,
    describe how to push negations toward the leaves of a
    proposition and, when read from right to left, describe
    how to pull negations toward the top of a propsition. *)

Lemma not_or_iff : forall P Q : Prop,
  (P \/ Q -> False) <-> (P -> False) /\ (Q -> False).
Proof.
  tauto.
Qed.

Lemma not_and_iff : forall P Q : Prop,
  (P /\ Q -> False) <-> (P -> Q -> False).
Proof.
  tauto.
Qed.

Lemma not_imp_iff : forall P Q : Prop,
  decidable P ->
  (((P -> Q) -> False) <-> P /\ (Q -> False)).
Proof.
  unfold decidable in *. tauto.
Qed.

Lemma not_imp_rev_iff : forall P Q : Prop,
  decidable P ->
  (((P -> Q) -> False) <-> (Q -> False) /\ P).
Proof.
  unfold decidable in *. tauto.
Qed.

(** * Tactics for Negations *)

(** ** Folding Negations
    This section provides tactics for folding uses of [not]
    wherever possible.  Multiple versions are provided that
    correspond to many of the forms used by the built-in
    conversion tactics. *)

Tactic Notation "fold" "any" "not" :=
  repeat (
    match goal with
    | |- context [?P -> False] =>
      fold (~ P)
    end).

Tactic Notation "fold" "any" "not" "in" ident(H) "|-" :=
  repeat (
    match goal with
    | J: context [?P -> False] |- _ =>
      fold (~ P) in H
    end).

Tactic Notation "fold" "any" "not" "in" ident(H) :=
  fold any not in H |-.

Tactic Notation "fold" "any" "not" "in" "*" "|-" :=
  repeat (
    match goal with
    | H: context [?P -> False] |- _ =>
      fold (~ P) in H
    end).

Tactic Notation "fold" "any" "not" "in" "*" :=
  fold any not in * |-; fold any not.

Tactic Notation "fold" "any" "not" "in" "*" "|-" "*" :=
  fold any not in *.

(** ** Folding [Iff]
    This section provides tactics for folding uses of [iff]
    wherever possible.  Multiple versions are provided that
    correspond to many of the forms used by the built-in
    conversion tactics.  These tactic may be better located
    somewhere else in the standard library: although it is
    used in this file, it has nothing to do with negation. *)

Tactic Notation "fold" "any" "iff" :=
  repeat (
    match goal with
    | |- context [(?P -> ?Q) /\ (?Q -> ?P)] =>
      fold (P <-> Q)
    end).

Tactic Notation "fold" "any" "iff" "in" ident(H) "|-" :=
  repeat (
    match goal with
    | J: context [(?P -> ?Q) /\ (?Q -> ?P)] |- _ =>
      fold (P <-> Q) in H
    end).

Tactic Notation "fold" "any" "iff" "in" ident(H) :=
  fold any iff in H |-.

Tactic Notation "fold" "any" "iff" "in" "*" "|-" :=
  repeat (
    match goal with
    | H: context [(?P -> ?Q) /\ (?Q -> ?P)] |- _ =>
      fold (P <-> Q) in H
    end).

Tactic Notation "fold" "any" "iff" "in" "*" :=
  fold any iff in * |-; fold any iff.

Tactic Notation "fold" "any" "iff" "in" "*" "|-" "*" :=
  fold any iff in *.

(** [push not using db] will push all negations to the leaves of
    propositions in the goal, using the lemmas in [db] to assist
    in checking the decidability of the propositions involved.
    If [using db] is omitted, then [core] will be used.
    Additional versions are provided to manipulate the
    hypotheses, following the conventions used by the built-in
    tactics.  (Is there a way to do this without using so much
    cut-and-paste?) *)

Tactic Notation "push" "not" "using" ident(db) :=
  unfold not, iff;
  repeat (
    match goal with
    (** simplification by not_true_iff *)
    | |- context [True -> False] =>
      rewrite not_true_iff
    (** simplification by not_false_iff *)
    | |- context [False -> False] =>
      rewrite not_false_iff
    (** simplification by not_not_iff *)
    | |- context [(?P -> False) -> False] =>
      rewrite (not_not_iff P);
        [ solve_decidable using db | ]
    (** simplification by contrapositive *)
    | |- context [(?P -> False) -> (?Q -> False)] =>
      rewrite (contrapositive P Q);
        [ solve_decidable using db | ]
    (** simplification by and_not_l_iff_1/_2 *)
    | |- context [(?P -> False) \/ ?Q] =>
      (rewrite (and_not_l_iff_1 P Q);
        [ solve_decidable using db | ]) ||
      (rewrite (and_not_l_iff_2 P Q);
        [ solve_decidable using db | ])
    (** simplification by and_not_r_iff_1/_2 *)
    | |- context [?P \/ (?Q -> False)] =>
      (rewrite (and_not_r_iff_1 P Q);
        [ solve_decidable using db | ]) ||
      (rewrite (and_not_r_iff_2 P Q);
        [ solve_decidable using db | ])
    (** simplification by imp_not_l *)
    | |- context [(?P -> False) -> ?Q] =>
      rewrite (imp_not_l P Q);
        [ solve_decidable using db | ]
    (** rewriting by not_or_iff *)
    | |- context [?P \/ ?Q -> False] =>
      rewrite (not_or_iff P Q)
    (** rewriting by not_and_iff *)
    | |- context [?P /\ ?Q -> False] =>
      rewrite (not_and_iff P Q)
    (** rewriting by not_imp_iff *)
    | |- context [(?P -> ?Q) -> False] =>
      rewrite (not_imp_iff P Q);
        [ solve_decidable using db | ]
    end);
  fold any not; fold any iff.

Tactic Notation "push" "not" :=
  push not using core.

Tactic Notation "push" "not" "in" ident(H) "|-"
  "using" ident(db) :=
  unfold not, iff in * |-;
  repeat (
    match goal with
    (** simplification by not_true_iff *)
    | J: context [True -> False] |- _ =>
      rewrite not_true_iff in H
    (** simplification by not_false_iff *)
    | J: context [False -> False] |- _ =>
      rewrite not_false_iff in H
    (** simplification by not_not_iff *)
    | J: context [(?P -> False) -> False] |- _ =>
      rewrite (not_not_iff P) in H;
        [ | solve_decidable using db ]
    (** simplification by contrapositive *)
    | J: context [(?P -> False) -> (?Q -> False)] |- _ =>
      rewrite (contrapositive P Q) in H;
        [ | solve_decidable using db ]
    (** simplification by and_not_l_iff_1/_2 *)
    | J: context [(?P -> False) \/ ?Q] |- _ =>
      (rewrite (and_not_l_iff_1 P Q) in H;
        [ | solve_decidable using db ]) ||
      (rewrite (and_not_l_iff_2 P Q) in H;
        [ | solve_decidable using db ])
    (** simplification by and_not_r_iff_1/_2 *)
    | J: context [?P \/ (?Q -> False)] |- _ =>
      (rewrite (and_not_r_iff_1 P Q) in H;
        [ | solve_decidable using db ]) ||
      (rewrite (and_not_r_iff_2 P Q) in H;
        [ | solve_decidable using db ])
    (** simplification by imp_not_l *)
    | J: context [(?P -> False) -> ?Q] |- _ =>
      rewrite (imp_not_l P Q) in H;
        [ | solve_decidable using db ]
    (** rewriting by not_or_iff *)
    | J: context [?P \/ ?Q -> False] |- _ =>
      rewrite (not_or_iff P Q) in H
    (** rewriting by not_and_iff *)
    | J: context [?P /\ ?Q -> False] |- _ =>
      rewrite (not_and_iff P Q) in H
    (** rewriting by not_imp_iff *)
    | J: context [(?P -> ?Q) -> False] |- _ =>
      rewrite (not_imp_iff P Q) in H;
        [ | solve_decidable using db ]
    end);
  fold any not in * |-; fold any iff in * |-.

Tactic Notation "push" "not" "in" ident(H) "|-"  :=
  push not in H |- using core.

Tactic Notation "push" "not" "in" ident(H) "using" ident(db) :=
  push not in H |- using db.
Tactic Notation "push" "not" "in" ident(H) :=
  push not in H |- using core.

Tactic Notation "push" "not" "in" "*" "|-" "using" ident(db) :=
  unfold not, iff in * |-;
  repeat (
    match goal with
    (** simplification by not_true_iff *)
    | H: context [True -> False] |- _ =>
      rewrite not_true_iff in H
    (** simplification by not_false_iff *)
    | H: context [False -> False] |- _ =>
      rewrite not_false_iff in H
    (** simplification by not_not_iff *)
    | H: context [(?P -> False) -> False] |- _ =>
      rewrite (not_not_iff P) in H;
        [ | solve_decidable using db ]
    (** simplification by contrapositive *)
    | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
      rewrite (contrapositive P Q) in H;
        [ | solve_decidable using db ]
    (** simplification by and_not_l_iff_1/_2 *)
    | H: context [(?P -> False) \/ ?Q] |- _ =>
      (rewrite (and_not_l_iff_1 P Q) in H;
        [ | solve_decidable using db ]) ||
      (rewrite (and_not_l_iff_2 P Q) in H;
        [ | solve_decidable using db ])
    (** simplification by and_not_r_iff_1/_2 *)
    | H: context [?P \/ (?Q -> False)] |- _ =>
      (rewrite (and_not_r_iff_1 P Q) in H;
        [ | solve_decidable using db ]) ||
      (rewrite (and_not_r_iff_2 P Q) in H;
        [ | solve_decidable using db ])
    (** simplification by imp_not_l *)
    | H: context [(?P -> False) -> ?Q] |- _ =>
      rewrite (imp_not_l P Q) in H;
        [ | solve_decidable using db ]
    (** rewriting by not_or_iff *)
    | H: context [?P \/ ?Q -> False] |- _ =>
      rewrite (not_or_iff P Q) in H
    (** rewriting by not_and_iff *)
    | H: context [?P /\ ?Q -> False] |- _ =>
      rewrite (not_and_iff P Q) in H
    (** rewriting by not_imp_iff *)
    | H: context [(?P -> ?Q) -> False] |- _ =>
      rewrite (not_imp_iff P Q) in H;
        [ | solve_decidable using db ]
    end);
  fold any not in * |-; fold any iff in * |-.

Tactic Notation "push" "not" "in" "*" "|-"  :=
  push not in * |- using core.

Tactic Notation "push" "not" "in" "*" "using" ident(db) :=
  push not using db; push not in * |- using db.
Tactic Notation "push" "not" "in" "*" :=
  push not in * using core.

Tactic Notation "push" "not" "in" "*" "|-" "*"
  "using" ident(db) :=
  push not in * using db.
Tactic Notation "push" "not" "in" "*" "|-" "*" :=
  push not in * using core.

Lemma test_push : forall P Q R : Prop,
  decidable P ->
  decidable Q ->
  (~ True) ->
  (~ False) ->
  (~ ~ P) ->
  (~ (P /\ Q) -> ~ R) ->
  ((P /\ Q) \/ ~ R) ->
  (~ (P /\ Q) \/ R) ->
  (R \/ ~ (P /\ Q)) ->
  (~ R \/ (P /\ Q)) ->
  (~ P -> R) ->
  (~ ((R -> P) \/ (R -> Q))) ->
  (~ (P /\ R)) ->
  (~ (P -> R)) ->
  True.
Proof.
  intros. push not in *. tauto.
Qed.

(** [pull not using db] will pull as many negations as possible
    toward the top of the propositional formula in the goal,
    using the lemmas in [db] to assist in checking the
    decidability of the propositions involved.  If [using db] is
    omitted, then [core] will be used.  Additional versions are
    provided to manipulate the hypotheses, following the
    conventions used by the built-in tactics.  (Is there a way
    to do this without using so much cut-and-paste?) *)

Tactic Notation "pull" "not" "using" ident(db) :=
  unfold not, iff;
  repeat (
    match goal with
    (** simplification by not_true_iff *)
    | |- context [True -> False] =>
      rewrite not_true_iff
    (** simplification by not_false_iff *)
    | |- context [False -> False] =>
      rewrite not_false_iff
    (** simplification by not_not_iff *)
    | |- context [(?P -> False) -> False] =>
      rewrite (not_not_iff P);
        [ solve_decidable using db | ]
    (** simplification by contrapositive *)
    | |- context [(?P -> False) -> (?Q -> False)] =>
      rewrite (contrapositive P Q);
        [ solve_decidable using db | ]
    (** simplification by and_not_l_iff_1/_2 *)
    | |- context [(?P -> False) \/ ?Q] =>
      (rewrite (and_not_l_iff_1 P Q);
        [ solve_decidable using db | ]) ||
      (rewrite (and_not_l_iff_2 P Q);
        [ solve_decidable using db | ])
    (** simplification by and_not_r_iff_1/_2 *)
    | |- context [?P \/ (?Q -> False)] =>
      (rewrite (and_not_r_iff_1 P Q);
        [ solve_decidable using db | ]) ||
      (rewrite (and_not_r_iff_2 P Q);
        [ solve_decidable using db | ])
    (** simplification by imp_not_l *)
    | |- context [(?P -> False) -> ?Q] =>
      rewrite (imp_not_l P Q);
        [ solve_decidable using db | ]
    (** rewriting by not_or_iff *)
    | |- context [(?P -> False) /\ (?Q -> False)] =>
      rewrite <- (not_or_iff P Q)
    (** rewriting by not_and_iff *)
    | |- context [?P -> ?Q -> False] =>
      rewrite <- (not_and_iff P Q)
    (** rewriting by not_imp_iff *)
    | |- context [?P /\ (?Q -> False)] =>
      rewrite <- (not_imp_iff P Q);
        [ solve_decidable using db | ]
    (** rewriting by not_imp_rev_iff *)
    | |- context [(?Q -> False) /\ ?P] =>
      rewrite <- (not_imp_rev_iff P Q);
        [ solve_decidable using db | ]
    end);
  fold any not; fold any iff.

Tactic Notation "pull" "not" :=
  pull not using core.

Tactic Notation "pull" "not" "in" ident(H) "|-"
  "using" ident(db) :=
  unfold not, iff in * |-;
  repeat (
    match goal with
    (** simplification by not_true_iff *)
    | J: context [True -> False] |- _ =>
      rewrite not_true_iff in H
    (** simplification by not_false_iff *)
    | J: context [False -> False] |- _ =>
      rewrite not_false_iff in H
    (** simplification by not_not_iff *)
    | J: context [(?P -> False) -> False] |- _ =>
      rewrite (not_not_iff P) in H;
        [ | solve_decidable using db ]
    (** simplification by contrapositive *)
    | J: context [(?P -> False) -> (?Q -> False)] |- _ =>
      rewrite (contrapositive P Q) in H;
        [ | solve_decidable using db ]
    (** simplification by and_not_l_iff_1/_2 *)
    | J: context [(?P -> False) \/ ?Q] |- _ =>
      (rewrite (and_not_l_iff_1 P Q) in H;
        [ | solve_decidable using db ]) ||
      (rewrite (and_not_l_iff_2 P Q) in H;
        [ | solve_decidable using db ])
    (** simplification by and_not_r_iff_1/_2 *)
    | J: context [?P \/ (?Q -> False)] |- _ =>
      (rewrite (and_not_r_iff_1 P Q) in H;
        [ | solve_decidable using db ]) ||
      (rewrite (and_not_r_iff_2 P Q) in H;
        [ | solve_decidable using db ])
    (** simplification by imp_not_l *)
    | J: context [(?P -> False) -> ?Q] |- _ =>
      rewrite (imp_not_l P Q) in H;
        [ | solve_decidable using db ]
    (** rewriting by not_or_iff *)
    | J: context [(?P -> False) /\ (?Q -> False)] |- _ =>
      rewrite <- (not_or_iff P Q) in H
    (** rewriting by not_and_iff *)
    | J: context [?P -> ?Q -> False] |- _ =>
      rewrite <- (not_and_iff P Q) in H
    (** rewriting by not_imp_iff *)
    | J: context [?P /\ (?Q -> False)] |- _ =>
      rewrite <- (not_imp_iff P Q) in H;
        [ | solve_decidable using db ]
    (** rewriting by not_imp_rev_iff *)
    | J: context [(?Q -> False) /\ ?P] |- _ =>
      rewrite <- (not_imp_rev_iff P Q) in H;
        [ | solve_decidable using db ]
    end);
  fold any not in * |-; fold any iff in * |-.

Tactic Notation "pull" "not" "in" ident(H) "|-"  :=
  pull not in H |- using core.

Tactic Notation "pull" "not" "in" ident(H) "using" ident(db) :=
  pull not in H |- using db.
Tactic Notation "pull" "not" "in" ident(H) :=
  pull not in H |- using core.

Tactic Notation "pull" "not" "in" "*" "|-" "using" ident(db) :=
  unfold not, iff in * |-;
  repeat (
    match goal with
    (** simplification by not_true_iff *)
    | H: context [True -> False] |- _ =>
      rewrite not_true_iff in H
    (** simplification by not_false_iff *)
    | H: context [False -> False] |- _ =>
      rewrite not_false_iff in H
    (** simplification by not_not_iff *)
    | H: context [(?P -> False) -> False] |- _ =>
      rewrite (not_not_iff P) in H;
        [ | solve_decidable using db ]
    (** simplification by contrapositive *)
    | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
      rewrite (contrapositive P Q) in H;
        [ | solve_decidable using db ]
    (** simplification by and_not_l_iff_1/_2 *)
    | H: context [(?P -> False) \/ ?Q] |- _ =>
      (rewrite (and_not_l_iff_1 P Q) in H;
        [ | solve_decidable using db ]) ||
      (rewrite (and_not_l_iff_2 P Q) in H;
        [ | solve_decidable using db ])
    (** simplification by and_not_r_iff_1/_2 *)
    | H: context [?P \/ (?Q -> False)] |- _ =>
      (rewrite (and_not_r_iff_1 P Q) in H;
        [ | solve_decidable using db ]) ||
      (rewrite (and_not_r_iff_2 P Q) in H;
        [ | solve_decidable using db ])
    (** simplification by imp_not_l *)
    | H: context [(?P -> False) -> ?Q] |- _ =>
      rewrite (imp_not_l P Q) in H;
        [ | solve_decidable using db ]
    (** rewriting by not_or_iff *)
    | H: context [(?P -> False) /\ (?Q -> False)] |- _ =>
      rewrite <- (not_or_iff P Q) in H
    (** rewriting by not_and_iff *)
    | H: context [?P -> ?Q -> False] |- _ =>
      rewrite <- (not_and_iff P Q) in H
    (** rewriting by not_imp_iff *)
    | H: context [?P /\ (?Q -> False)] |- _ =>
      rewrite <- (not_imp_iff P Q) in H;
        [ | solve_decidable using db ]
    (** rewriting by not_imp_rev_iff *)
    | H: context [(?Q -> False) /\ ?P] |- _ =>
      rewrite <- (not_imp_rev_iff P Q) in H;
        [ | solve_decidable using db ]
    end);
  fold any not in * |-; fold any iff in * |-.

Tactic Notation "pull" "not" "in" "*" "|-"  :=
  pull not in * |- using core.

Tactic Notation "pull" "not" "in" "*" "using" ident(db) :=
  pull not using db; pull not in * |- using db.
Tactic Notation "pull" "not" "in" "*" :=
  pull not in * using core.

Tactic Notation "pull" "not" "in" "*" "|-" "*"
  "using" ident(db) :=
  pull not in * using db.
Tactic Notation "pull" "not" "in" "*" "|-" "*" :=
  pull not in * using core.

Lemma test_pull : forall P Q R : Prop,
  decidable P ->
  decidable Q ->
  (~ True) ->
  (~ False) ->
  (~ ~ P) ->
  (~ (P /\ Q) -> ~ R) ->
  ((P /\ Q) \/ ~ R) ->
  (~ (P /\ Q) \/ R) ->
  (R \/ ~ (P /\ Q)) ->
  (~ R \/ (P /\ Q)) ->
  (~ P -> R) ->
  (~ (R -> P) /\ ~ (R -> Q)) ->
  (~ P \/ ~ R) ->
  (P /\ ~ R) ->
  (~ R /\ P) ->
  True.
Proof.
  intros. pull not in *. tauto.
Qed.
