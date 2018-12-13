(** A library of additional tactics. *)

Require Export String.
Open Scope string_scope.


(* *********************************************************************** *)
(** * Extensions of the standard library *)

(** "[remember c as x in |-]" replaces the term [c] by the identifier
    [x] in the conclusion of the current goal and introduces the
    hypothesis [x=c] into the context.  This tactic differs from a
    similar one in the standard library in that the replacmement is
    made only in the conclusion of the goal; the context is left
    unchanged. *)

Tactic Notation "remember" constr(c) "as" ident(x) "in" "|-" :=
  let x := fresh x in
  let H := fresh "Heq" x in
  (set (x := c); assert (H : x = c) by reflexivity; clearbody x).

(** "[unsimpl E]" replaces all occurence of [X] by [E], where [X] is
    the result that tactic [simpl] would give when used to evaluate
    [E]. *)

Tactic Notation "unsimpl" constr(E) :=
  let F := (eval simpl in E) in change F with E.


(* *********************************************************************** *)
(** * Delineating cases in proofs *)

(** The following tries to move hypothesis [x] to the top of the
    hypothesis list.  It should never result in tactic failure. *)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

(** The following tactics are used to put simultaneously comment
    markers in a proof script and the current proof context.  For
    example, [(Case "cons x xs")] introduces a new variable [case]
    into the context with value ["cons x xs"].  This would be useful
    when starting the [cons] case for a proof by induction on a list;
    as long as [case] is defined, one can be sure that the case has
    not yet been proven completely. *)

Ltac Case s :=
  let c := fresh "case" in set (c := s); move_to_top c.
Ltac Subcase s :=
  let c := fresh "subcase" in set (c := s); move_to_top c.
Ltac Subsubcase s :=
  let c := fresh "subsubcase" in set (c := s); move_to_top c.
