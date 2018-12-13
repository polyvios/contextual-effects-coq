Set Undo 10000.

Require Export Metatheory.
Require Import Ensembles.

Parameter label : Type.
Definition ptr := atom.
Definition labelset := Ensemble label.

(* my label-set library *)
Definition union := Union label.
Definition subset := Included label.
Definition full_set := Full_set label.
Definition empty_set := Empty_set label.
Definition subseteq := (Extensionality_Ensembles label).
Definition singl (x:label) : labelset := (Singleton label x).

Notation "A `U` B" := (union A B) (at level 69, right associativity) : set_scope.
Notation "A `In` B" := (In label B A) (at level 69) : set_scope.
Notation "A `Notin` B" := (~In label B A) (at level 69) : set_scope.

Lemma subset_refl : forall (A: labelset), subset A A.
Proof.
  intros. unfold subset. unfold Included. intros. trivial.
Qed.

Lemma subset_trans : forall A B C,
  subset A B -> subset B C -> subset A C.
Proof.
  intros.
  unfold subset in *.
  unfold Included in *.
  intros. auto.
Qed.

Lemma subset_union_left : forall A B C,
  subset A B -> subset A (union B C).
Proof.
  intros.
  unfold subset in *.
  unfold Included in *.
  intros. auto using (Union_introl label).
Qed.

Lemma subset_union_right : forall A B C,
  subset A C -> subset A (union B C).
Proof.
  intros.
  unfold subset in *.
  unfold Included in *.
  intros. auto using (Union_intror label).
Qed.

Lemma subset_full_set : forall s, subset s full_set.
Proof.
  intros.
  unfold subset. unfold Included. unfold full_set.
  intros. apply Full_intro.
Qed.

Lemma full_set_subset : forall s,
  subset full_set s -> s = full_set.
Proof.
  intros. apply subseteq. split.
  apply subset_full_set. assumption.
Qed.

Lemma full_set_union : forall s,
  union full_set s = full_set.
Proof.
  intros.
  apply subseteq. split.
  apply subset_full_set.
  unfold Included.
    intros.
    apply (Union_introl label). trivial.
Qed.

Lemma union_full_set : forall s,
  union s full_set = full_set.
Proof.
  intros.
  apply subseteq. split.
  apply subset_full_set.
  unfold Included.
    intros.
    apply (Union_intror label). trivial.
Qed.

Lemma empty_set_subset : forall s, subset empty_set s.
Proof.
  unfold subset. unfold empty_set. unfold Included. intros. destruct H.
Qed.

Hint Resolve subset_refl subset_trans subset_union_left subset_union_right
  subset_full_set full_set_subset union_full_set full_set_union
  empty_set_subset (Union_introl label) (Union_intror label) (In_singleton label) (Full_intro label)
  subseteq.

Lemma union_assoc : forall A B C,
  (A `U` B) `U` C = A `U` (B `U` C).
Proof.
  intros.
  apply subseteq. split; unfold Included; intros x H; destruct H; try destruct H; auto.
Qed.

Lemma union_symmetric : forall A B,
  A `U` B = B `U` A.
Proof.
  intros.
  apply subseteq. split; unfold Included; intros x H; destruct H; try destruct H; auto.
Qed.

Lemma in_union : forall x s1 s2,
  x `In` (s1 `U` s2) <-> (x `In` s1) \/ (x `In` s2).
Proof.
  intros. split; intro; (destruct H; [ left; trivial | right; trivial ]).
Qed.

Lemma in_empty : forall x, x `In` empty_set <-> False.
  intros. split; intros; destruct H.
Qed.

Lemma in_singleton : forall x y, x `In` (Singleton label y) <-> x = y.
  intros. split; intros; inversion H; subst; auto.
Qed.

Hint Rewrite in_union in_empty in_singleton: labelset_simpl.

Ltac mysolve :=
  match goal with
    | _: _ |- _ = _ => subst;
      let x := fresh "x" in
      let H := fresh "H" in
      apply subseteq; split;
        unfold union in *;
        unfold subset in *;
        unfold Included in *;
        unfold singl in *;
        intros x H;
        autorewrite with labelset_simpl in *; subst;
        intuition eauto
    | _ =>  subst;
      unfold union in *;
      unfold subset in *;
      unfold Included in *;
      unfold singl in *;
      intros;
      autorewrite with labelset_simpl in *; subst;
      intuition eauto
  end.

Tactic Notation "rewrite" "set" constr(s) "as" constr(X) :=
  let H := fresh "H" in
  assert (s = X) as H; [ mysolve | rewrite H; clear H ].  

Lemma subset_add : forall s1 s2 s3 s4,
  subset s1 s2 ->
  subset s3 s4 ->
  subset (s1 `U` s3) (s2 `U` s4).
Proof.
  unfold subset. unfold Included. unfold union. intros.
  destruct H1; eauto.
Qed.

(* end my set library *)

(*****************************************************)
(* phi definition *)
Inductive phi : Type :=
  | make_phi : labelset -> labelset -> labelset -> phi.

Definition phi_0 := make_phi full_set empty_set full_set.

Function phi_fld_fst (p: phi) : labelset :=
  match p with
    | make_phi a e o => a
  end.

Function phi_fld_rst (p: phi) : labelset :=
  match p with
    | make_phi a e o => o
  end.

Function phi_fld_eff (p: phi) : labelset :=
  match p with
    | make_phi a e o => e
  end.

(* subtyping on phis *)

Inductive phi_sub : phi -> phi -> Prop :=
  | sub_context : forall (fst1 fst2 teff1 teff2 rst1 rst2: labelset),
      subset fst2 fst1 ->
      subset teff1 teff2 ->
      subset rst2 rst1 ->
      phi_sub
        (make_phi fst1 teff1 rst1)
        (make_phi fst2 teff2 rst2).

Hint Constructors phi_sub.

Lemma phi_0_sub_all : forall p, phi_sub phi_0 p.
Proof.
  intros.
  destruct p. unfold phi_0.
  apply sub_context; auto using subset_full_set, empty_set_subset.
Qed.

Lemma phi_sub_eq : forall p1 p2,
  phi_sub p1 p2 -> phi_sub p2 p1 -> p1 = p2.
Proof.
  intros. induction H. inversion H0. subst.
  f_equal; apply subseteq; split; trivial.
Qed.

Lemma phi_sub_refl : forall p, phi_sub p p.
Proof.
  intros. destruct p. auto.
Qed.

Lemma phi_sub_trans : forall p1 p2 p3,
  phi_sub p1 p2 -> phi_sub p2 p3 -> phi_sub p1 p3.
Proof.
  intros p1 p2 p3 H1 H2.
  inversion H1. subst. inversion H2. subst. eauto.
Qed.

Hint Resolve phi_0_sub_all phi_sub_eq phi_sub_refl phi_sub_trans.

(* combine phis *)
Inductive comb_cflow : phi -> phi -> phi -> Prop :=
  | make_comb : forall fst1 teff1 teff2 rst2,
      comb_cflow
      (make_phi fst1 teff1 (rst2 `U` teff2))
      (make_phi (fst1 `U` teff1) teff2 rst2)
      (make_phi fst1 (teff1 `U` teff2) rst2).

Hint Constructors comb_cflow.

Lemma phi_comb_teff : forall p1 p2 p3,
  comb_cflow p1 p2 p3 ->
  subset (phi_fld_eff p1) (phi_fld_eff p3) /\
  subset (phi_fld_eff p2) (phi_fld_eff p3).
Proof.
  intros. destruct H. simpl. split; auto.
Qed.

Hint Resolve phi_comb_teff.

(***************************************************************)
(* types *)
Inductive typ : Type :=
  | typ_int : typ
  | typ_ref : labelset -> typ -> typ
  | typ_fun : phi -> typ -> typ -> typ.

(***************************************************************)
(* subtyping *)
Inductive subtype : typ -> typ -> Prop :=
  | sub_int : subtype typ_int typ_int
  | sub_ref : forall t t' teff teff',
      subtype t t' ->
      subtype t' t ->
      subset teff teff' ->
      subtype (typ_ref teff t) (typ_ref teff' t')
  | sub_fun : forall t1 t1' t2 t2' p p',
      subtype t1' t1 ->
      subtype t2 t2' ->
      phi_sub p p' ->
      subtype (typ_fun p t1 t2) (typ_fun p' t1' t2').

Hint Constructors subtype.

Lemma subtype_eq : forall t1 t2,
  subtype t1 t2 -> subtype t2 t1 -> t1 = t2.
Proof.
  intros. induction H.
  Case "int".
    reflexivity.
  Case "ref".
    f_equal. apply subseteq. split. 
      assumption.
      inversion H0. assumption.
    apply IHsubtype1. assumption.
  Case "fun".
    inversion H0. subst.
    f_equal. 
      apply phi_sub_eq; assumption.
      assert (t1' = t1). apply IHsubtype1. assumption. subst. reflexivity.
      apply IHsubtype2. assumption.
Qed.

Lemma subtype_refl : forall s, subtype s s.
Proof.
  intros. induction s.
    apply sub_int.
    apply sub_ref. assumption. assumption. apply subset_refl.
    apply sub_fun. assumption. assumption. apply phi_sub_refl.
Qed.

Lemma subtype_trans : forall t1 t2 t3,
  subtype t1 t2 -> subtype t2 t3 -> subtype t1 t3.
Proof with simpl_env; auto.
  intros.
  generalize dependent t1.
  generalize dependent t3.
  remember t2 as Q' in |-.
  generalize dependent Q'.
  induction t2;
    intros Q' EQ S SsubQ;
    induction SsubQ; try discriminate;
    inversion EQ; subst;
    intros T QsubT;
    inversion QsubT; subst; eauto.
Qed.

Hint Resolve subtype_eq subtype_refl subtype_trans.

(* the language *)
Inductive exp : Type :=
  | e_nat : nat -> exp
  | e_bvar : nat -> exp
  | e_fvar : atom -> exp
  | e_lam : exp -> exp
  | e_app : exp -> exp -> exp
  | e_let : exp -> exp -> exp
  | e_if : exp -> exp -> exp -> exp
  | e_ref : label -> exp -> exp
  | e_deref : exp -> exp
  | e_assign : exp -> exp -> exp
  | e_loc : ptr -> label -> exp
.

Inductive value : exp -> Prop :=
  | int_value : forall n, value (e_nat n)
  | lam_value : forall e, value (e_lam e)
  | loc_value : forall ptr label, value (e_loc ptr label).

Hint Constructors value.

(*Coercion e_bvar : nat >-> exp.*)
Coercion e_fvar : atom >-> exp.

Fixpoint subst (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
    | e_nat n => e_nat n
    | e_bvar i => e_bvar i
    | e_fvar x => if x == z then u else (e_fvar x)
    | e_lam e1 => e_lam (subst z u e1)
    | e_app e1 e2 => e_app (subst z u e1) (subst z u e2)
    | e_let e1 e2 => e_let (subst z u e1) (subst z u e2)
    | e_if e1 e2 e3 => e_if (subst z u e1) (subst z u e2) (subst z u e3)
    | e_ref teff e => e_ref teff (subst z u e)
    | e_deref e => e_deref (subst z u e)
    | e_assign e1 e2 => e_assign (subst z u e1) (subst z u e2)
    | e_loc ptr label => e_loc ptr label
  end.

Notation "[ z ~> u ] e" := (subst z u e) (at level 68).

Fixpoint fv (e : exp) {struct e} : atoms :=
  match e with
    | e_nat n => {}
    | e_bvar i => {}
    | e_fvar x => singleton x
    | e_lam e1 => fv e1
    | e_app e1 e2 => (fv e1) `union` (fv e2)
    | e_let e1 e2 => (fv e1) `union` (fv e2)
    | e_if e1 e2 e3 => (fv e1) `union` (fv e2) `union` (fv e3)
    | e_ref teff e => fv e
    | e_deref e => fv e
    | e_assign e1 e2 => (fv e1) `union` (fv e2)
    | e_loc ptr label => singleton ptr
  end.

Fixpoint open_rec (k : nat) (u : exp) (e : exp) {struct e} : exp :=
  match e with
    | e_nat n => e_nat n
    | e_bvar i => if k === i then u else (e_bvar i)
    | e_fvar x => e_fvar x
    | e_lam e1 => e_lam (open_rec (S k) u e1)
    | e_app e1 e2 => e_app (open_rec k u e1) (open_rec k u e2)
    | e_let e1 e2 => e_let (open_rec k u e1) (open_rec (S k) u e2)
    | e_if e1 e2 e3 => e_if (open_rec k u e1) (open_rec k u e2) (open_rec k u e3)
    | e_ref teff e => e_ref teff (open_rec k u e)
    | e_deref e => e_deref (open_rec k u e)
    | e_assign e1 e2 => e_assign (open_rec k u e1) (open_rec k u e2)
    | e_loc ptr label => e_loc ptr label
  end.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

Definition open e u := open_rec 0 u e.

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv x) in
  constr:(A `union` B `union` C `union` D).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in
  (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.

Notation env := (list (atom * typ)).

Inductive typing : phi -> env -> env -> exp -> typ -> Prop :=
  | typing_nat : forall n E P,
      ok E -> ok P -> typing phi_0 E P (e_nat n) typ_int
  | typing_var : forall E P (x : atom) T,
      ok E -> ok P ->
      binds x T E ->
      typing phi_0 E P (e_fvar x) T
  | typing_lam : forall L p E P e T1 T2,
      (forall x : atom, x `notin` L ->
        typing p ((x, T1) :: E) P (open e x) T2) ->
      typing phi_0 E P (e_lam e) (typ_fun p T1 T2)
  | typing_app : forall p1 p2 pf p E P e1 e2 T1 T2,
      typing p1 E P e1 (typ_fun pf T1 T2) ->
      typing p2 E P e2 T1 ->
      (exists p3, comb_cflow p1 p2 p3 /\ comb_cflow p3 pf p) ->
      typing p E P (e_app e1 e2) T2
  | typing_let : forall L p1 p2 T1 p E P e1 e2 T2,
      typing p1 E P e1 T1 ->
      (forall x : atom, x `notin` L ->
        typing p2 ((x, T1)::E) P (open e2 x) T2) ->
      comb_cflow p1 p2 p ->
      typing p E P (e_let e1 e2) T2
  | typing_if : forall p1 p2 p E P e1 e2 e3 T,
      typing p1 E P e1 typ_int ->
      typing p2 E P e2 T ->
      typing p2 E P e3 T ->
      comb_cflow p1 p2 p ->
      typing p E P (e_if e1 e2 e3) T
  | typing_sub : forall p p' E P e T T',
      typing p' E P e T' ->
      subtype T' T ->
      phi_sub p' p ->
      typing p E P e T
  | typing_ref : forall p E P e t l,
      typing p E P e t ->
      typing p E P (e_ref l e) (typ_ref (singl l) t)
  | typing_deref : forall p p1 E P e teff t fst rst,
      typing p1 E P e (typ_ref teff t) ->
      comb_cflow p1 (make_phi fst teff rst) p ->
      typing p E P (e_deref e) t
  | typing_assign : forall p1 p2 fst rst teff p p' E P e1 e2 t,
      typing p1 E P e1 (typ_ref teff t) ->
      typing p2 E P e2 t ->
      comb_cflow p1 p2 p' ->
      comb_cflow p' (make_phi fst teff rst) p ->
      typing p E P (e_assign e1 e2) t
  | typing_loc : forall E P ptr l t,
      ok E -> ok P ->
      binds ptr t P ->
      typing phi_0 E P (e_loc ptr l) (typ_ref (singl l) t)  
.

Hint Constructors typing.

Lemma typing_env_ok : forall p E P e t,
  typing p E P e t -> ok E /\ ok P.
Proof.
  intros. induction H; auto.
  pick fresh x. destruct (H0 x). auto. inversion H1. auto.
Qed.

Notation heap := (list (ptr * exp)).

Fixpoint replace (h: heap) (r: ptr) (v: exp) {struct h} :=
  match h with
    | nil => nil
    | (r',v')::tl =>
        if r' == r then cons (r, v) tl
        else (r', v')::(replace tl r v)
  end.

Lemma binds_after_replace : forall (h: heap) (r: ptr) (v v': exp),
  binds r v h -> binds r v' (replace h r v').
Proof.
  intros. induction h as [|(l,e)].
  Case "nil".
    unfold binds in H. inversion H.
  Case "cons".
    unfold binds. simpl. destruct (l == r). 
    Case "equal". 
      simpl. destruct (r == r). reflexivity.
        destruct n. reflexivity.
    Case "different".
      simpl. destruct (r == l).
        subst. destruct n. reflexivity.
        unfold binds in *. simpl in *. apply IHh. destruct (r == l).
          subst. destruct n. reflexivity. apply H.
Qed.

Lemma binds_other_after_replace : forall h r r' v v',
  binds r v h -> r <> r' -> binds r v (replace h r' v').
Proof.
  intros. induction h as [|(l,e)].
  Case "nil". unfold binds in H. inversion H.
  Case "cons".
    unfold binds. simpl. destruct (l==r).
    Case "equal". subst.
      destruct (r == r'). destruct H0. assumption.
        simpl. unfold binds in H. simpl in H.
        destruct (r == r). assumption.
      unfold binds in *. apply IHh. assumption.
    Case "different".
      unfold binds in *. simpl in *.
      destruct (r == l). destruct n; auto. simpl.
      destruct (l == r'). subst. simpl. destruct (r == r'). destruct n. auto.
      unfold binds in *. simpl in *. destruct (r == r'). destruct n. auto.
      assumption.
      simpl. destruct (r == l). destruct n; auto.
      apply IHh. assumption.
Qed.

Inductive result : Type :=
  | exp_result : exp -> result
  | err_result : result.

Inductive evaluation :
  labelset -> labelset -> heap -> exp ->
  labelset ->
  labelset -> labelset -> heap -> result -> Prop :=
  | id : forall fst rst heap v,
      value v ->
      evaluation fst rst heap v empty_set fst rst heap (exp_result v)
  | call : forall e1 e2 e v2 v fst fst1 fst2 fst' rst rst1 rst2 rst'
                  heap heap1 heap2 heap' teff1 teff2 teff3,
      evaluation fst rst heap e1 teff1 fst1 rst1 heap1 (exp_result (e_lam e)) ->
      evaluation fst1 rst1 heap1 e2 teff2 fst2 rst2 heap2 (exp_result v2) ->
      evaluation fst2 rst2 heap2 (open e v2) teff3 fst' rst' heap' (exp_result v) ->
      evaluation fst rst heap (e_app e1 e2) (teff1 `U` teff2 `U` teff3)
        fst' rst' heap' (exp_result v)
  | ref : forall fst fst' rst rst' heap heap' e teff v r l,
      evaluation fst rst heap e teff fst' rst' heap' (exp_result v) ->
      r `notin` (dom heap') ->
      evaluation fst rst heap (e_ref l e) teff fst' rst' ((r,v)::heap')
        (exp_result (e_loc r l))
  | deref : forall fst fst' rst rst' teff (l: label) heap heap' e ptr v,
      evaluation fst rst heap e teff fst'
        (rst' `U` (singl l)) heap' (exp_result (e_loc ptr l)) ->
      ptr `in` (dom heap') ->
      binds ptr v heap' ->
      evaluation fst rst heap (e_deref e) (teff `U` (singl l))
        (fst' `U` (singl l)) rst' heap' (exp_result v)
  | assign : forall fst fst1 fst2 teff1 teff2 rst rst1 rst2
                    e1 e2 heap heap1 heap2 ptr l v v',
      evaluation fst rst heap e1 teff1
                 fst1 rst1 heap1 (exp_result (e_loc ptr l)) ->
      evaluation fst1 rst1 heap1 e2 teff2
                 fst2 (rst2 `U` (singl l)) heap2 (exp_result v) ->
      binds ptr v' heap2 ->
      evaluation fst rst heap (e_assign e1 e2)
                 ((teff1 `U` teff2) `U` (singl l))
                 (fst2 `U` (singl l)) rst2
                 (replace heap2 ptr v) (exp_result v)
  | let_in : forall fst rst heap e1 eff1 fst1 rst1 heap1 v1 e2 eff2 fst2 rst2 heap2 v2,
      evaluation fst rst heap e1 eff1 fst1 rst1 heap1 (exp_result v1) ->
      evaluation fst1 rst1 heap1 (open e2 v1) eff2 fst2 rst2 heap2 (exp_result v2) ->
      evaluation fst rst heap (e_let e1 e2) (eff1 `U` eff2)
                 fst2 rst2 heap2 (exp_result v2)
  | if_t : forall fst rst heap e1 e2 e3 v fst1 fst2 rst1 rst2 heap1 heap2 teff1 teff2,
      evaluation fst rst heap e1 teff1 fst1 rst1 heap1 (exp_result (e_nat 0)) ->
      evaluation fst1 rst1 heap1 e2 teff2 fst2 rst2 heap2 (exp_result v) ->
      evaluation fst rst heap (e_if e1 e2 e3) (teff1 `U` teff2) fst2 rst2 heap2
        (exp_result v)
  | if_f : forall fst rst heap e1 e2 e3 v n fst1 fst2 rst1 rst2 heap1 heap2 teff1 teff2,
      evaluation fst rst heap e1 teff1 fst1 rst1 heap1 (exp_result (e_nat n)) ->
      n <> 0 ->
      evaluation fst1 rst1 heap1 e3 teff2 fst2 rst2 heap2 (exp_result v) ->
      evaluation fst rst heap (e_if e1 e2 e3) (teff1 `U` teff2) fst2 rst2 heap2
        (exp_result v)
  | call_w : forall fst rst heap e1 e2 teff fst' rst' heap' v,
      evaluation fst rst heap e1 teff fst' rst' heap' (exp_result v) ->
      (forall e, v <> (e_lam e)) ->
      evaluation fst rst heap (e_app e1 e2) teff fst' rst' heap err_result
  | deref_h_w : forall fst rst e heap teff fst' rst' heap' ptr label,
      evaluation fst rst heap e teff fst' rst' heap'
        (exp_result (e_loc ptr label)) ->
      ptr `notin` (dom heap') ->
      evaluation fst rst heap (e_deref e) teff fst' rst' heap err_result
  | deref_l_w : forall fst rst e heap teff fst' rst' heap' ptr label,
      evaluation fst rst heap e teff fst' rst' heap'
        (exp_result (e_loc ptr label)) ->
      ptr `in` (dom heap') ->
      (label `Notin` fst') ->
      evaluation fst rst heap (e_deref e) teff fst' rst' heap err_result
  | assign_h_w : forall fst rst heap e1 teff1 fst1 rst1 heap1 ptr label
                        e2 teff2 fst2 rst2 heap2 v,
      evaluation fst rst heap e1 teff1
                 fst1 rst1 heap1 (exp_result (e_loc ptr label)) ->
      evaluation fst1 rst1 heap1 e2 teff2
                 fst2 rst2 heap2 (exp_result v) ->
      ptr `notin` (dom heap2) ->
      evaluation fst rst heap (e_assign e1 e2) (teff1 `U` teff2)
                 fst2 rst2 heap err_result
  | assign_l_w : forall fst rst heap e1 teff1 fst1 rst1 heap1 ptr label
                        e2 teff2 fst2 rst2 heap2 v' v,
      evaluation fst rst heap e1 teff1 fst1 rst1 heap1
                 (exp_result (e_loc ptr label)) ->
      evaluation fst1 rst1 heap1 e2 teff2 fst2 rst2 heap2 (exp_result v) ->
      binds ptr v' heap2 ->
      label `Notin` rst2 ->
      evaluation fst rst heap (e_assign e1 e2) (teff1 `U` teff2) fst2 rst2 heap err_result
.

Hint Constructors evaluation.

Lemma evaluation_weakening : forall fst rst heap e eff fst' rst' heap' v fstw rstw,
  evaluation fst rst heap e eff fst' rst' heap' (exp_result v) ->
  evaluation (fst `U` fstw) (rst `U` rstw) heap e eff
    (fst' `U` fstw) (rst' `U` rstw) heap' (exp_result v).
Proof.
  intros.
  remember (exp_result v) as R.
  generalize dependent v.
  generalize dependent fstw.
  generalize dependent rstw.
  induction H;
    intros rstw fstw vv Eq; inversion Eq; subst; clear Eq; eauto.
  Case "deref".
    intros.
    rewrite set ((fst' `U` singl l) `U` fstw) as ((fst' `U` fstw) `U` singl l).
    eapply deref.
    rewrite set ((rst' `U` rstw) `U` singl l) as ((rst' `U` singl l) `U` rstw).
    eapply IHevaluation.
    reflexivity. assumption. assumption.
  Case "assign".
    rewrite set ((fst2 `U` singl l) `U` fstw) as ((fst2 `U` fstw) `U` singl l).
    eapply assign.
    eapply IHevaluation1; auto.
    rewrite set ((rst2 `U` rstw) `U` singl l) as ((rst2 `U` singl l) `U` rstw).
    eapply IHevaluation2; auto.
    apply H1.
Qed.

Lemma forward_effect_subset : forall fst rst fst' rst' teff e v H H',
  evaluation fst rst H e teff fst' rst' H' (exp_result v) ->
  subset fst fst'.
Proof.
  intros.
  induction H0; eauto.
Qed.

Lemma backward_effect_subset : forall fst rst fst' rst' teff e v H H',
  evaluation fst rst H e teff fst' rst' H' (exp_result v) ->
  subset rst' rst.
Proof.
  intros.
  induction H0; eauto.
Qed.

Lemma adequacy : forall fst rst heap e eff fst' rst' heap' v,
  value v ->
  evaluation fst rst heap e eff fst' rst' heap' (exp_result v) ->
  fst' = fst `U` eff /\ rst = rst' `U` eff.
Proof.
  intros fst rst heap e eff fst' rst' heap' v V H.
  split; induction H; try assumption; try mysolve.
Qed.

Ltac propagate_full_set f :=
  assert (f = full_set);
    [ apply full_set_subset; eauto 4 using forward_effect_subset, backward_effect_subset
      | subst f ].

Ltac propagate_full_sets :=
  repeat (
    match goal with
    | [x : labelset, _: ?x = full_set |- _ ] => subst x
    | [x : labelset, H : evaluation full_set _ _ _ _ ?x _ _ _ |- _ ] =>
        propagate_full_set x
    | [x : labelset, H : evaluation _ ?x _ _ _ _ full_set _ _ |- _ ] =>
        propagate_full_set x
    | [x : labelset, H : evaluation _ ?x _ _ _ _ (full_set `U` _) _ _ |- _ ] =>
        propagate_full_set x
    | [x : labelset, H : evaluation _ ?x _ _ _ _ (_ `U` full_set) _ _ |- _ ] =>
        propagate_full_set x
    end).

Lemma canonical_evaluation : forall fst rst heap e eff fst' rst' heap' v,
  fst = full_set ->
  rst = full_set ->
  fst' = full_set ->
  rst' = full_set ->
  evaluation fst rst heap e eff fst' rst' heap' (exp_result v) ->
  evaluation empty_set eff heap e eff eff empty_set heap' (exp_result v).
Proof.
  intros.
  remember (exp_result v) as R.
  generalize dependent v.
  induction H3; intros vv Eq; inversion Eq; subst vv; clear Eq; eauto;
    subst fst rst.
  Case "call".
    intros.
    propagate_full_sets.
    eapply call.
    Subcase "e1".
      rewrite set empty_set as (empty_set `U` empty_set).
      apply evaluation_weakening. eauto.
    Subcase "e2".
      rewrite set (teff1 `U` empty_set) as (empty_set `U` teff1).
      rewrite set (empty_set `U` teff2 `U` teff3) as (teff2 `U` teff3).
      apply evaluation_weakening. eauto.      
    Subcase "e3".
      rewrite set empty_set as (empty_set `U` empty_set).
      rewrite set (teff2 `U` teff1) as (empty_set `U` (teff1 `U` teff2)).
      rewrite set ((empty_set `U` empty_set) `U` teff3) as (teff3 `U` empty_set).
      rewrite set (teff1 `U` teff2 `U` teff3) as
        (teff3 `U` teff1 `U` teff2).
      apply evaluation_weakening. eauto.
  Case "deref".
    propagate_full_sets.
    eapply deref.
    rewrite set empty_set as (empty_set `U` empty_set).
    rewrite set teff as (teff `U` empty_set).
    rewrite set ((empty_set `U` empty_set) `U` singl l) as (empty_set `U` singl l).
    rewrite set ((teff `U` empty_set) `U` singl l) as (teff `U` singl l).
    apply evaluation_weakening.
    rewrite set (teff `U` empty_set) as teff.
    eauto. assumption. assumption.
  Case "assign".
    propagate_full_sets.
    eapply assign; eauto.
    rewrite set empty_set as (empty_set `U` empty_set).
    rewrite set ((teff1 `U` teff2) `U` (singl l)) as (teff1 `U` teff2 `U` (singl l)).
    apply evaluation_weakening. eauto.
    rewrite set (empty_set `U` teff2 `U` singl l) as (teff2 `U` singl l).
    rewrite set (teff1 `U` empty_set) as (empty_set `U` teff1).
    rewrite set (teff1 `U` teff2) as (teff2 `U` teff1).
    apply evaluation_weakening.
    eauto.
  Case "let".
    propagate_full_sets.
    rewrite set empty_set as (empty_set `U` empty_set).
    eapply let_in.
    eauto using evaluation_weakening.
    rewrite set (eff1 `U` empty_set) as (empty_set `U` eff1).
    rewrite set (empty_set `U` eff2) as (eff2 `U` empty_set).
    rewrite set (eff1 `U` eff2) as (eff2 `U` eff1).
    eauto using evaluation_weakening.
  Case "if".
    propagate_full_sets.
    rewrite set empty_set as (empty_set `U` empty_set).
    eapply if_t; eauto.
    apply evaluation_weakening; eauto.
    rewrite set (teff1 `U` empty_set) as (empty_set `U` teff1).
    rewrite set (empty_set `U` teff2) as (teff2 `U` empty_set).
    rewrite set (teff1 `U` teff2) as (teff2 `U` teff1).
    apply evaluation_weakening; eauto.
    Case "if-f". 
    propagate_full_sets.
    rewrite set empty_set as (empty_set `U` empty_set).
    eapply if_f; eauto.
    apply evaluation_weakening; eauto.
    rewrite set (teff1 `U` empty_set) as (empty_set `U` teff1).
    rewrite set (empty_set `U` teff2) as (teff2 `U` empty_set).
    rewrite set (teff1 `U` teff2) as (teff2 `U` teff1).
    apply evaluation_weakening; eauto.
Qed.

Definition heap_ok (P:env) h := ok P /\ (dom h) = (dom P) /\
  forall r, r `in` (dom h) ->
  exists t, exists v,
    value v /\ binds r v h /\ binds r t P /\ typing phi_0 nil P v t.

Lemma empty_heap_ok : heap_ok nil nil.
Proof.
  split. apply ok_nil.
  split. reflexivity.
  intros. decideFSet.
Qed.

Lemma typing_weakening_str : forall P P1 P2 E F G p e t,
  typing p (G ++ E) (P1 ++ P) e t ->
  ok (G ++ F ++ E) ->
  ok (P1 ++ P2 ++ P) ->
  typing p (G ++ F ++ E) (P1 ++ P2 ++ P) e t.
Proof.
  intros P P1 P2 E F G p e t H.
  remember (G ++ E) as E'.
  remember (P1 ++ P) as P'.
  generalize dependent G.
  generalize dependent P1.
  induction H; intros P1 Eqp G EqE OkE OkP; subst; eauto.
  Case "lam".
    pick fresh x and apply typing_lam. apply H0 with (G0 := (x,T1)::G); auto.
    rewrite cons_concat_assoc. auto.
  Case "let".
    pick fresh x and apply typing_let; eauto.
    apply H1 with (G0 := (x,T1)::G); auto. rewrite cons_concat_assoc. auto.
Qed.

Lemma typing_weakening : forall p E F P P1 e T,
    typing p E P e T ->
    ok (F ++ E) ->
    ok (P1 ++ P) ->
    typing p (F ++ E) (P1 ++ P) e T.
Proof.
  intros p E F P P1 e T H J.
  rewrite <- (nil_concat _ (F ++ E)).
  rewrite <- (nil_concat _ (P1 ++ P)).
  apply typing_weakening_str; auto.
Qed.

Lemma env_ok : forall H E, heap_ok E H -> ok E.
Proof.
  intros.
  unfold heap_ok in H0. destruct H0. auto.
Qed.

Hint Resolve env_ok.

Lemma typing_subst_var_case : forall p E F P u S T z x,
  binds x T (F ++ (z, S) :: E) ->
  ok (F ++ (z, S) :: E) ->
  ok P ->
  typing p E P u S ->
  typing p (F ++ E) P ([z ~> u] x) T.
Proof.
  intros p E F P u S T z x H J Pok K.
  simpl.
  destruct (x == z).
  Case "x = z".
    subst.
    assert (T = S).
      eapply binds_mid_eq_cons. apply H. apply J.
    subst.
    rewrite <- (nil_concat _ P).
    apply typing_weakening.
      apply K.
      eapply ok_remove_mid_cons. apply J. simpl. auto.
  Case "x <> z". eauto.
Qed.

Inductive lc : exp -> Prop :=
  | lc_nat : forall n, lc (e_nat n)
  | lc_fvar : forall x,
      lc (e_fvar x)
  | lc_lam : forall L e,
      (forall x:atom, x `notin` L -> lc (open e x)) ->
      lc (e_lam e)
  | lc_app : forall e1 e2,
      lc e1 ->
      lc e2 ->
      lc (e_app e1 e2)
  | lc_let : forall L e1 e2,
      lc e1 ->
      (forall x:atom, x `notin` L -> lc (open e2 x)) -> lc (e_let e1 e2)
  | lc_if : forall e1 e2 e3,
      lc e1 -> lc e2 -> lc e3 -> lc (e_if e1 e2 e3)
  | lc_ref : forall teff e,
      lc e -> lc (e_ref teff e)
  | lc_deref : forall e,
      lc e -> lc (e_deref e)
  | lc_assign : forall e1 e2,
      lc e1 -> lc e2 -> lc (e_assign e1 e2)
  | lc_loc : forall ptr label, lc (e_loc ptr label)
.

Hint Constructors lc.

Lemma typing_regular_lc : forall p E P e T,
  typing p E P e T -> lc e.
Proof.
  intros p E P e T H. induction H; eauto.
Qed.

Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof with eauto*.
  induction e; intros j v i u Neq H; simpl in *;
      try solve [inversion H; f_equal; eauto].
  Case "bvar".
    destruct (j === n)...
    destruct (i === n)...
Qed.

Lemma open_rec_lc : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC; simpl; intro k; f_equal; auto.
  Case "lc_lam".
    unfold open in *.
    pick fresh x for L.
    apply open_rec_lc_core with (i := S k) (j := 0) (u := u) (v := x). auto.
    auto.
  Case "lc_let".
    unfold open in *.
    pick fresh x for L.
    apply open_rec_lc_core with (i := S k) (j := 0) (u := u) (v := x). auto.
    auto.
Qed.

Lemma subst_open_rec : forall e1 e2 u x k,
  lc u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
  induction e1; intros e2 u x k H; simpl in *; f_equal; auto.
  Case "bvar".
    destruct (k === n); auto.
  Case "fvar".
    destruct (a == x); subst; auto.
    apply open_rec_lc; auto.
Qed.

Lemma subst_open_var : forall (x y : atom) u e,
  y <> x ->
  lc u ->
  open ([x ~> u] e) y = [x ~> u] (open e y).
Proof.
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec with (e2 := y).
  simpl.
  destruct (y == x).
    Case "y=x".
    destruct Neq. auto.
    Case "y<>x".
    auto.
  auto.
Qed.

Lemma typing_subst_strengthened : forall p E F P e u S T z,
  typing p (F ++ (z, S) :: E) P e T ->
  typing phi_0 E P u S ->
  typing p (F ++ E) P ([z ~> u] e) T.
Proof.
  intros p E F P e u S T z He Hu.
  remember (F ++ (z, S) :: E) as E'.
  generalize dependent F.
  induction He; intros F Eq; subst; simpl; eauto.
  Case "typing_var".
    apply (typing_subst_var_case phi_0 E F P u S T z x); auto.
  Case "typing_lam".
    pick fresh y and apply typing_lam.
    rewrite subst_open_var.
    rewrite <- cons_concat_assoc. auto. auto.
    apply (typing_regular_lc phi_0 E P u S Hu).
  Case "typing_let".
    pick fresh y and apply typing_let. auto.
      rewrite subst_open_var.
      apply H0 with (x := y) (F0 := (y,T1)::F); auto. auto.
      apply (typing_regular_lc phi_0 E P u S Hu). assumption.
Qed.

Lemma typing_subst : forall p E P e u S T z,
  typing p ((z, S) :: E) P e T ->
  typing phi_0 E P u S ->
  typing p E P ([z ~> u] e) T.
Proof.
  intros p E P e u S T z H J.
  rewrite <- (nil_concat _ E).
  eapply typing_subst_strengthened.
    rewrite nil_concat. apply H.
    apply J.
Qed.

Lemma generalize_value_phi : forall v E P p t,
  value v ->
  typing p E P v t ->
  typing phi_0 E P v t.
Proof with rewrite H2; eapply typing_sub; auto; eauto.
  intros v E P p t V H.
  induction H; intros; inversion V; eauto...
Qed.

Lemma subst_fresh : forall (x : atom) e u,
  x `notin` fv e -> [x ~> u] e = e.
Proof.
  intros x e u H.
  induction e; subst; simpl in *; f_equal; auto.
  Case "fvar".
   destruct (a == x); subst; auto. decideFSet.
Qed.

Lemma subst_intro : forall (x : atom) u e,
  x `notin` (fv e) ->
  lc u ->
  open e u = [x ~> u](open e x).
Proof.
  intros x u e H J.
  unfold open.
  rewrite subst_open_rec; auto.
  simpl.
  destruct (x == x).
  Case "x = x".
    rewrite subst_fresh; auto.
  Case "x <> x".
    destruct n; auto.
Qed.

Lemma ok_env_narrowing : forall (F E:env) x t t',
  ok (F ++ ((x,t)::nil) ++ E) -> ok (F ++ ((x,t')::nil) ++ E).
Proof.
  induction F; intros E x t t' H; inversion H; subst; simpl; apply ok_cons; auto.
  simpl_env in *. eapply IHF. apply H2. 
    simpl_env in *. assumption.
Qed.

Lemma sub_narrowing_str : forall x p t1 t2 F E P e t,
  subtype t1 t2 ->
  typing p (F ++ (x, t2)::E) P e t ->
  typing p (F ++ (x, t1)::E) P e t.
Proof with simpl_env in *; eauto using ok_env_narrowing.
  intros x p t1 t2 F E P e t Sub T.
  remember (F ++ (x,t2)::E) as G.
  generalize dependent F.
  induction T; intros F Eq; subst...
  Case "var". destruct (x == x0).
    Subcase "x = x0".
    subst. binds_get H1. apply typing_sub with (T' := t1) (p' := phi_0)...
      apply typing_var; auto.
      apply ok_env_narrowing with (t := t2). assumption. 
      apply binds_mid. eapply ok_env_narrowing... 
    Subcase "x<>x0".
      apply typing_var; eauto using ok_env_narrowing.
      binds_cases H1; eauto using binds_tail, binds_head.      
  Case "lam".
    pick fresh y and apply typing_lam. apply H0 with (F0 := (y,T1)::F). auto.
    simpl_env. reflexivity.
  Case "let".
    pick fresh y and apply typing_let.
      apply IHT...
      apply H0 with (F0 := (y,T1)::F); auto.
      assumption.
Qed.

Lemma sub_narrowing : forall p x E P e t1 t2 t,
  subtype t2 t1 ->
  typing p ((x, t1)::E) P e t ->
  typing p ((x, t2)::E) P e t.
Proof.
  intros.
  rewrite_env (nil ++ (x,t2)::E). eapply sub_narrowing_str. apply H.
  assumption.
Qed.

Lemma typing_nat_inv : forall p n E P t,
  typing p E P (e_nat n) t ->
    ok E /\ ok P /\ subtype typ_int t.
Proof.
  intros.
  destruct (typing_env_ok p E P (e_nat n) t H).
  split. assumption.
  split. assumption.
  remember (e_nat n) as e'.
  induction H; inversion Heqe'; subst. eauto.
  eauto.
Qed.

Lemma typing_var_inv : forall p E P x t,
  typing p E P (e_fvar x) t ->
  exists t', subtype t' t /\ ok E /\ ok P /\ binds x t' E.
Proof.
  intros. remember (e_fvar x) as e. induction H; inversion Heqe; subst.
  exists T. eauto.
  destruct (IHtyping H2) as [ t' [sub [ oke [ okp b ]]]]. 
  exists t'. split; eauto.
Qed.

Lemma typing_lam_inv : forall p E P e1 t,
  typing p E P (e_lam e1) t ->
  forall pf t1 t2,
    subtype t (typ_fun pf t1 t2) ->
    exists L, forall x, x `notin` L ->
    typing pf ((x,t1)::E) P (open e1 x) t2.
Proof.
  intros p E P e1 t T.
  remember (e_lam e1) as e'.
  generalize dependent e1.
  induction T; intros e' Eq pf' t1 t2 Sub; inversion Eq; subst.
  inversion Sub. subst. exists L. intros. eapply sub_narrowing. apply H5.
  eauto using typing_sub.
  apply IHT. reflexivity. eauto.
Qed.

Lemma typing_let_inv : forall p E P e1 e2 T2,
  typing p E P (e_let e1 e2) T2 ->
  exists p1, exists p2, exists t1, exists p',
    comb_cflow p1 p2 p' /\
    phi_sub p' p /\
    typing p1 E P e1 t1 /\
    exists L, forall x, x `notin` L ->
      typing p2 ((x, t1)::E) P (open e2 x) T2.
Proof.
  intros.
  remember (e_let e1 e2) as e.
  induction H; inversion Heqe; subst.
  Case "let".
    exists p1. exists p2. exists T1. exists p.
    repeat split; auto; clear Heqe IHtyping H1.
    exists L. intros. auto.
  Case "sub".
    destruct IHtyping as [p1 [p2 [t1 [p'' [cf [Sub [H' [L H'']]]]]]]]. auto.
    exists p1. exists p2. exists t1. exists p''.
    repeat split; eauto using phi_sub_trans.
Qed.

Lemma typing_app_inv : forall p E P e1 e2 t2,
  typing p E P (e_app e1 e2) t2 ->
  exists p1, exists p2, exists p3, exists pf, exists t1, exists p',
  comb_cflow p1 p2 p3 /\
  comb_cflow p3 pf p' /\
  phi_sub p' p /\
  typing p1 E P e1 (typ_fun pf t1 t2) /\
  typing p2 E P e2 t1.
Proof.
  intros.
  remember (e_app e1 e2) as e.
  induction H; inversion Heqe; subst.
  Case "app".
    destruct H1 as [p3 [cf1 cf2]].
    exists p1. exists p2. exists p3. exists pf. exists T1. exists p.
    auto.
  Case "sub".
    destruct (IHtyping H2) as [p1[p2[p3[pf[t1[p''[cf1[cf2[T1 T2]]]]]]]]].
    exists p1. exists p2. exists p3. exists pf. exists t1. exists p''.
    split. assumption. split. assumption.
    split. eauto using phi_sub_trans.
    destruct T2 as [T2a T2b].
    split; auto.
   eauto using typing_sub, sub_fun.
Qed.

Lemma typing_ref_inv : forall p E P e t l,
  typing p E P (e_ref l e) t ->
  exists teff, exists t', subtype (typ_ref teff t') t /\
  typing p E P e t' /\ l `In` teff.
Proof.
  intros.
  remember (e_ref l e) as e'.
  induction H; inversion Heqe'; subst.
  Case "sub".
    destruct (IHtyping H2) as [teff [t' [sub [T1 I]]]].
    exists teff. exists t'. intuition eauto.
  Case "ref".
    exists (singl l). exists t.
    split. auto.
    split. assumption.
    mysolve.
Qed.

Lemma typing_deref_inv : forall p E P e t,
  typing p E P (e_deref e) t ->
  exists p1, exists fst, exists teff, exists rst, exists t', exists p',
  subtype t' t /\
  phi_sub p' p /\
  typing p1 E P e (typ_ref teff t') /\
  comb_cflow p1 (make_phi fst teff rst) p'.
Proof.
  intros.
  remember (e_deref e) as e'.
  induction H; inversion Heqe'; subst.
  Case "sub".
    destruct (IHtyping H2) as [p1[fst[teff[rst[t'[p''[Sub [SP [T1 Cf]]]]]]]]].
    exists p1. exists fst. exists teff. exists rst. exists t'. exists p''.
    split. eauto.
    split. apply (phi_sub_trans p'' p'); assumption.
    split; assumption.
  Case "deref".
    exists p1. exists fst. exists teff. exists rst. exists t. exists p.
    eauto.
Qed.

Lemma typing_assign_inv : forall p E P e1 e2 t,
  typing p E P (e_assign e1 e2) t ->
  exists t', exists p', exists p1, exists p2, exists p3,
    exists fst, exists teff, exists rst,
      comb_cflow p1 p2 p3 /\
      comb_cflow p3 (make_phi fst teff rst) p' /\
      subtype t' t /\
      phi_sub p' p /\
      typing p1 E P e1 (typ_ref teff t') /\
      typing p2 E P e2 t'.
Proof.
  intros.
  remember (e_assign e1 e2) as e'.
  induction H; inversion Heqe'; subst.
  Case "sub".
    destruct (IHtyping H2)
      as [t'[p''[p1[p2[p3[fst[teff[rst[Cf1[Cf2[Sub[PS[T1 T2]]]]]]]]]]]]].
    exists t'. exists p''. exists p1. exists p2. exists p3.
    exists fst. exists teff. exists rst.
    split. assumption.
    split. assumption.
    split. eauto.
    split. apply (phi_sub_trans p'' p'); assumption.
    split; assumption.
  Case "assign".
    exists t. exists p. exists p1. exists p2. exists p'.
    exists fst. exists teff. exists rst.
    eauto 6.
Qed.

Lemma typing_if_inv : forall p E P e1 e2 e3 t,
      typing p E P (e_if e1 e2 e3) t ->
      exists p1, exists p2, exists p', exists t',
      typing p1 E P e1 typ_int /\
      typing p2 E P e2 t' /\
      typing p2 E P e3 t' /\
      comb_cflow p1 p2 p' /\
      phi_sub p' p /\
      subtype t' t.
Proof.
  intros. remember (e_if e1 e2 e3) as e.
  induction H; inversion Heqe; subst.
  Case "if". clear IHtyping1 IHtyping2 IHtyping3 Heqe.
    exists p1. exists p2. exists p. exists T.
    repeat split; auto.
  Case "sub".
    destruct (IHtyping H2) as [p1 [p2[p''[t'[T1[T2[T3[Cf [S1 S2]]]]]]]]].
    exists p1. exists p2. exists p''. exists t'.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. eauto using phi_sub_trans.
    eauto.
Qed.

Lemma typing_loc_inv : forall p E P r l t,
  typing p E P (e_loc r l) t ->
  ok E /\ ok P /\
  exists t',
    subtype (typ_ref (singl l) t') t /\
    binds r t' P.
Proof.
  intros. remember (e_loc r l) as e'.
  induction H; inversion Heqe'; subst.
  Case "sub".
    destruct (IHtyping H2) as [okE[okP[t'[Sub B ]]]].
    repeat split;auto.
    exists t'. split. eauto. assumption.
  Case "loc".
    split. assumption.
    split. assumption.
    exists t. eauto.
Qed.


Lemma typing_weak_P : forall p E P e t r t',
  r `notin` dom P ->
  typing p E P e t ->
  typing p E ((r,t')::P) e t.
Proof.
  intros p E P e t r t' NE T. induction T; subst; eauto.
  apply typing_loc; auto. simpl_env. apply binds_tail. assumption.
  simpl. destruct (ptr0 == r).
    subst. unfold not in NE. assert False. apply NE. eapply binds_In. apply H1.
    destruct H2.
    decideFSet.
Qed.

Lemma heap_push : forall r v t P H,
  heap_ok P H ->
  r `notin` dom P ->
  value v ->
  typing phi_0 nil P v t ->
  heap_ok ((r,t)::P) ((r,v)::H).
Proof.
  intros. unfold heap_ok in *. destruct H0 as [Pok [Eq ?]].
  split. eauto using ok_cons, env_ok.
  split. simpl. rewrite Eq. reflexivity.
  intros. destruct (r == r0).
    subst. exists t. exists v.
      split. assumption. 
      split. simpl_env. auto using binds_head, binds_singleton.
      split. simpl_env. auto using binds_head, binds_singleton.
      intros. apply typing_weak_P; auto.
    simpl in H4. assert (r0 `in` dom H). remember (dom H) as a. decideFSet.
    destruct (H0 r0 H5) as [t'[v'[V[bh[bp T]]]]].
    exists t'. exists v'. simpl_env.
    split. assumption.
    split. apply binds_tail. assumption. decideFSet.
    split. apply binds_tail. assumption. decideFSet.
    simpl. apply typing_weak_P. assumption. apply T.
Qed.

Lemma binds_unique : forall A, forall r (x x':A) h,
  binds r x h -> binds r x' h -> x = x'.
Proof.
  intros. unfold binds in *. induction h.
  rewrite H in H0. inversion H0. subst. reflexivity.
  destruct a as (r',x''). simpl in *. destruct (r == r').
    subst. inversion H; inversion H0; subst. assumption. auto.
Qed.

Ltac break_heap_ok H r :=
  match type of H with
    | heap_ok ?P ?h =>
        let okP := fresh "okP" in
        let domeq := fresh "domeq" in
        let H' := fresh "H" in
        let t := fresh "t" in
        let v := fresh "v" in
        let V := fresh "V" in
        let bh := fresh "bh" in
        let bp := fresh "bp" in
        destruct H as [okP [ domeq H' ]];
        destruct (H' r) as [t [ v [ V [ bh [ bp T]]]]];
        [ eauto 3 using binds_In; try rewrite domeq; eauto 3 using binds_In
        | clear H' ]
  end.

Tactic Notation "break_heap_ok" "in" hyp(H) "for" hyp(r) hyp(v') hyp(t') :=
  match type of H with
    | heap_ok ?P ?h =>
        let okP := fresh "okP" in
        let domeq := fresh "domeq" in
        let H' := fresh "H" in
        let t := fresh "t" in
        let v := fresh "v" in
        let V := fresh "V" in
        let bh := fresh "bh" in
        let bp := fresh "bp" in
        destruct H as [okP [ domeq H' ]];
        destruct (H' r) as [t [ v [ V [ bh [ bp T]]]]];
        [ eauto 3 using binds_In; try rewrite domeq; eauto 3 using binds_In
        | clear H';
          assert (v = v');
          [ eauto using binds_unique
            | assert (t = t'); [eauto using binds_unique | subst]
          ]
        ]
  end.
  

Lemma value_in_heap : forall P heap r v,
  heap_ok P heap -> binds r v heap -> value v.
Proof.
  intros. break_heap_ok H r.
  assert (v = v0). eauto using binds_unique.
  subst. assumption.
Qed.

Lemma typing_in_heap : forall P heap r v t,
  heap_ok P heap -> binds r v heap -> binds r t P ->
  typing phi_0 nil P v t.
Proof.
  intros. break_heap_ok in H for r v t. auto.
Qed.

Lemma heap_ok_binds : forall P h r,
  heap_ok P h -> ((exists v, binds r v h) <-> (exists t, binds r t P)).
Proof.
  intros. split; intros [v B]; break_heap_ok H r.
    exists t. assumption.
    exists v0. assumption.
Qed.

Lemma dom_after_replace: forall h r v v',
  binds r v h ->
  dom h = dom (replace h r v').
Proof.
  intros.
  induction h as [|(l,e)]. auto.
  simpl. destruct (l == r). subst. simpl. auto.
  simpl. rewrite IHh. reflexivity. unfold binds in H. simpl in H.
    destruct (r == l). destruct n. auto. unfold binds. auto.
Qed.

Lemma heap_ok_after_replace: forall P h r v v' t,
  heap_ok P h ->
  binds r v h ->
  binds r t P ->
  value v' ->
  typing phi_0 nil P v' t ->
  heap_ok P (replace h r v').
Proof.
  intros.
  destruct H as [Ok[Domeq HH]].
  unfold heap_ok. rewrite <- (dom_after_replace h r v v') in *; auto.
    split. assumption.
    split. assumption.
    intros. destruct (HH r0 H) as [t0[v0[V0[Bh0[Bp0 T0]]]]]. clear HH.
    exists t0.
    destruct(r == r0).
    Case "equal".
      subst r0. exists v'.
      split. assumption.
      split. apply binds_after_replace with v0. assumption.
      split. assumption.
      assert (t0 = t) as Eq. eauto using binds_unique. subst. assumption.
    Case "not equal".
      exists v0.
      split. assumption.
      split. apply binds_other_after_replace; auto.
      split. auto.
      assumption.
Qed.

Ltac standard_soundness_value v := 
  exists (nil:env); exists v; simpl in *; eauto 10 using empty_set_subset.

Theorem standard_effect_soundness :
  forall p P H H' e teff t R fst rst fst' rst',
    typing p nil (P) e t ->
    heap_ok P H ->
    evaluation fst rst H e teff fst' rst' H' R ->
    fst = full_set ->
    rst = full_set ->
    fst' = full_set ->
    rst' = full_set ->
    exists P', exists v,
      R = exp_result v /\
      value v /\
      typing phi_0 nil (P' ++ P) v t /\
      heap_ok (P' ++ P) H' /\
      subset teff (phi_fld_eff p)
.
Proof.
  intros p P H H' e teff t R fst rst fst' rst' T Hok D.
  intros Eqfst Eqrst Eqfst' Eqrst'.
  generalize dependent p.
  generalize dependent t.
  generalize dependent P.
  induction D; intros P Hok t p T.
  Case "Id".
    exists (nil:env). exists v.
      eauto 6 using generalize_value_phi, empty_set_subset.
  Case "app".
    destruct (typing_app_inv p nil P e1 e2 t T)
      as [p1 [p2 [p3 [pf [t1 [p' [Cf1 [Cf2 [Sub [T1 T2]]]]]]]]]].
    propagate_full_sets.
    assert (full_set = full_set) as EQ by reflexivity.
    destruct (IHD1 EQ EQ EQ EQ P Hok (typ_fun pf t1 t) p1 T1) as
      [ P1 [ vlam [ Nerr1 [ Vlam [Tf [ H1ok Sub1 ] ]] ]]].
    inversion Nerr1. subst vlam.
      assert (typing p2 nil (P1 ++ P) e2 t1).
      apply (typing_weakening p2 nil nil P P1 e2 t1 T2); simpl; eauto.
      destruct (IHD2 EQ EQ EQ EQ (P1 ++ P) H1ok t1 p2 H) 
        as [P2 [v2' [Nerr2 [V2 [Tv2 [H2ok Sub2]]]]]].
      inversion Nerr2. subst v2'.
      assert (typing phi_0 nil (P2 ++ P1 ++ P) (e_lam e) (typ_fun pf t1 t)) as Tf'.
      apply (typing_weakening phi_0 nil nil (P1 ++ P) P2 (e_lam e)
                 (typ_fun pf t1 t) Tf); simpl.
        apply ok_nil.
        apply env_ok with heap2. assumption.
        destruct (typing_lam_inv _ _ _ _ _ Tf' pf t1 t) as [L Tpf]. auto.
      assert (typing pf nil (P2 ++ P1 ++ P) (open e v2) t).
        pick fresh y.
        rewrite (subst_intro y).
        apply typing_subst with t1. apply Tpf. decideFSet. assumption.
        decideFSet.
        apply typing_regular_lc with (p := phi_0) (E := nil:env) (P := P2 ++ P1 ++ P) (T := t1). apply Tv2.
      destruct (IHD3 EQ EQ EQ EQ (P2 ++ P1 ++ P) H2ok t pf H0)
        as [P3 [v' [Nerr3 [V [Tv [H3ok Sub3]]]]]].
      inversion Nerr3. subst v'.
      exists (P3 ++ P2 ++ P1). exists v.
      clear D1 D2 D3 IHD1 IHD2 IHD3 Hok H1ok H2ok Tf H Tv2 Tf' Tpf H0 Nerr3 Nerr1 Nerr2 T T1 T2 t1 Vlam heap heap1 heap2 V2 L e e1 e2.
      intuition (simpl_env; eauto).
      inversion Cf1. subst p1 p2 p3. simpl in *.
      inversion Cf2. subst p' pf. simpl in *.
      inversion Sub. subst p. simpl in *.
      clear Cf1 Cf2 Sub. subst.
      autorewrite with labelset_simpl in *.
      apply subset_trans with  (teff0 `U` teff4 `U` teff6).
      apply subset_add. assumption.
        apply subset_add; assumption.
        rewrite <-union_assoc.
        assumption.
  Case "ref".
    destruct (typing_ref_inv p nil P e t l T) as [eff [t' [Sub [T' I]]]].
    destruct (IHD Eqfst Eqrst Eqfst' Eqrst' P Hok t' p T')
      as [P' [v' [Nerr [V [p0 [H'ok Sub1]]]]]].
    inversion Nerr. subst v'.
    exists ((r,t'):: P'). exists (e_loc r l).
    split. reflexivity.
    split. apply loc_value.
    split. intros.
    apply typing_sub with (p' := phi_0) (T' := typ_ref (singl l) t'); eauto.
    apply typing_loc.
      apply ok_nil. simpl_env. apply ok_push. apply env_ok with heap'. assumption.
      destruct H'ok as [? [Dom ?]].
      rewrite <- Dom. auto. simpl_env. auto using binds_head, binds_singleton.
      apply subtype_trans with (typ_ref eff t').
      apply sub_ref; auto.
      mysolve.
      assumption.
    split. simpl. apply heap_push; auto.
      destruct H'ok as [_ [Dom _]]. rewrite <- Dom. assumption.
      assumption.
  Case "deref".
    destruct (typing_deref_inv p nil P e t T)
      as [p1[fst1[teff1[rst1[t'[p'[Sub[PS[T' Cf]]]]]]]]].
    propagate_full_sets.
    assert (full_set = full_set) as EQ by reflexivity.
    destruct (IHD EQ EQ EQ Eqfst' P Hok (typ_ref teff1 t') p1 T')
      as [P1[v1[Nerr1[V1[Tf[H1ok Sub1]]]]]]. clear IHD D.
    inversion Nerr1. subst v1. clear Nerr1.
    destruct (typing_loc_inv phi_0 nil (P1 ++ P) ptr0 l (typ_ref teff1 t') Tf)
      as [_[_ [t'' [Sub2 B]]]]. clear Tf.
    exists P1. exists v.
    inversion Sub2.
    intuition (eauto using value_in_heap, typing_in_heap).
    inversion Cf. subst p'. subst p1. clear Cf.
    inversion Sub2. subst teff'. subst teff3. clear Sub2.
    inversion PS. subst p. clear PS. simpl in *.
    eauto using subset_add.
  Case "assign".
    destruct (typing_assign_inv p nil P e1 e2 t T)
      as [t'[p'[p1[p2[p3[fst'[teff[rst'[Cf1[Cf2[Sub1[PS[T1 T2]]]]]]]]]]]]].
    propagate_full_sets.
    assert (full_set = full_set) as EQ by reflexivity.
    destruct (IHD1 EQ EQ EQ EQ P Hok (typ_ref teff t') p1 T1)
      as [ P1 [ r [ Nerr1 [Vr [Tr[H1ok Sub2]]]]]]. clear IHD1.
    inversion Nerr1. subst r. clear Nerr1.
    assert (typing p2 nil (P1 ++ P) e2 t') as T2'.
      apply (typing_weakening p2 nil nil P P1 e2 t' T2); simpl; eauto. clear T2.
    assert (full_set `U` (singl l) = full_set) as EQ1 by eauto.
    destruct (IHD2 EQ EQ EQ EQ1 (P1 ++ P) H1ok t' p2 T2')
      as [P2[v2[Nerr2[Vv2[Tv2[H2ok Sub3]]]]]]. clear IHD2.
    inversion Nerr2. subst v2. clear Nerr2 EQ.
    destruct (typing_loc_inv phi_0 nil (P1 ++ P) ptr0 l (typ_ref teff t') Tr)
      as [_[_ [t'' [Sub4 B]]]]. clear Tr.
    inversion Sub4. subst.
    exists (P2 ++ P1). exists v.
    intuition (simpl_env; eauto using heap_ok_after_replace, binds_concat_ok).
    clear D1 D2 Vv2 Tv2 Sub4 B T1 Sub1 T t H Hok H1ok T2' H2ok P EQ1.
    inversion Cf1. subst p1 p2 p3.
    inversion Cf2. subst p' teff5 rst0 teff4 fst0 rst2. clear Cf1 Cf2.
    inversion PS. subst p rst1 fst0 teff4 fst'. clear PS. simpl in *.
    eauto using subset_add.
  Case "let".
    destruct (typing_let_inv p nil P e1 e2 t T)
      as [p1 [p2 [t1 [p' [cf [Sub [TT [L H]]]]]]]].
    propagate_full_sets.
    assert (full_set = full_set) as EQ by reflexivity.
    destruct (IHD1 EQ EQ EQ EQ P Hok t1 p1 TT) as [P' [v' [E [V [Tv [H1ok S1]]]]]].
    inversion E; subst v'.
    assert (typing p2 nil (P' ++ P) (open e2 v1) t) as T2.
      pick fresh y. rewrite (subst_intro y).
      apply typing_subst with t1.
      apply (typing_weakening p2 ((y,t1)::nil) nil); simpl; eauto.
      auto. auto. eauto using typing_regular_lc.
    destruct (IHD2 EQ EQ EQ EQ (P' ++ P) H1ok t p2 T2)
      as [P2 [v2' [E2 [V2 [Tv2 [H2ok S2]]]]]].
    inversion E2; subst v2'. clear E2.
    exists (P2 ++ P'). exists v2. simpl_env; intuition eauto.
    inversion cf. subst p' p1 p2. inversion Sub. subst p. simpl in *.
    eauto using subset_add.
  Case "if_t".
    destruct (typing_if_inv p nil P e1 e2 e3 t T)
      as [p1 [p2 [p' [t' [T1 [T2[T3[Cf [PS Sub]]]]]]]]].
    propagate_full_sets.
    assert (full_set = full_set) as EQ by reflexivity.
    destruct (IHD1 EQ EQ EQ EQ P Hok typ_int p1 T1) as [P1 [v1 [E1 [V1[Tv1[H1ok S1]]]]]].
    inversion E1. subst v1. clear E1.
    assert (typing p2 nil (P1 ++ P) e2 t') as T2'.
      apply (typing_weakening p2 nil nil). assumption. simpl. apply ok_nil. eauto.
    destruct (IHD2 EQ EQ EQ EQ (P1 ++ P) H1ok t' p2 T2') as [P2[v2[E2[V2[Tv2[H2ok S2]]]]]].
    inversion E2. subst v2. clear E2.
    exists (P2 ++ P1). exists v. simpl_env. intuition eauto.
    inversion Cf. subst p1 p2 p'. inversion PS. subst p. simpl in *.
    eauto using subset_add.
  Case "if_t".
    destruct (typing_if_inv p nil P e1 e2 e3 t T)
      as [p1 [p2 [p' [t' [T1 [T2[T3[Cf [PS Sub]]]]]]]]].
    propagate_full_sets.
    assert (full_set = full_set) as EQ by reflexivity.
    destruct (IHD1 EQ EQ EQ EQ P Hok typ_int p1 T1) as [P1 [v1 [E1 [V1[Tv1[H1ok S1]]]]]].
    inversion E1. subst v1. clear E1.
    assert (typing p2 nil (P1 ++ P) e3 t') as T2'.
      apply (typing_weakening p2 nil nil). assumption. simpl. apply ok_nil. eauto.
    destruct (IHD2 EQ EQ EQ EQ (P1 ++ P) H1ok t' p2 T2') as [P2[v2[E2[V2[Tv2[H2ok S2]]]]]].
    inversion E2. subst v2. clear E2.
    exists (P2 ++ P1). exists v. simpl_env. intuition eauto.
    inversion Cf. subst p1 p2 p'. inversion PS. subst p. simpl in *.
    eauto using subset_add.
  Case "call-w".
    destruct (typing_app_inv p nil P e1 e2 t T)
      as [p1 [p2 [p3 [pf [t1 [p' [Cf1 [Cf2 [Sub [T1 T2]]]]]]]]]].
    destruct (IHD Eqfst Eqrst Eqfst' Eqrst' P Hok (typ_fun pf t1 t) p1 T1) as
      [ P1 [ vlam [ Nerr1 [ Vlam [Tf [ H1ok Sub1 ] ]] ]]]. clear IHD.
    inversion Nerr1. subst v. clear Nerr1.
    inversion Vlam; subst vlam.
    Subcase "nat".
      destruct (typing_nat_inv phi_0 n nil (P1++P) (typ_fun pf t1 t) Tf) as [_[_ S]].
      inversion S.
    Subcase "lam".
      subst. destruct (H e). reflexivity.
    Subcase "loc".
      destruct (typing_loc_inv phi_0 nil (P1++P) ptr0 label0 (typ_fun pf t1 t) Tf)
        as [_[_[t'[S _]]]].
      inversion S.
  Case "deref_h_w".
    destruct (typing_deref_inv p nil P e t T)
      as [p1[a[ee[o[t'[p'[S[PS[T' C]]]]]]]]].
    destruct (IHD Eqfst Eqrst Eqfst' Eqrst' P Hok (typ_ref ee t') p1 T') as [P1[v[Eq[V[Tf[H1ok Sub]]]]]].
    inversion Eq. subst v. clear Eq. clear IHD.
    destruct (typing_loc_inv phi_0 nil (P1 ++ P) ptr0 label0 (typ_ref ee t') Tf)
      as [_[_[t''[S' B]]]].
    destruct (heap_ok_binds (P1 ++ P) heap' ptr0 H1ok). clear H0.
    destruct H1. exists t''. assumption.
    assert False. apply H. apply binds_In with x. assumption. inversion H1.
  Case "deref_l_w".
    destruct H0. rewrite Eqfst'. apply (Full_intro label).
  Case "assign_h_w".
    destruct (typing_assign_inv p nil P e1 e2 t T)
      as [t'[p'[p1[p2[p3[fst'[teff[rst'[Cf1[Cf2[Sub1[PS[T1 T2]]]]]]]]]]]]].
    propagate_full_sets.
    assert (full_set = full_set) as EQ by reflexivity.
    destruct (IHD1 EQ EQ EQ EQ P Hok (typ_ref teff t') p1 T1)
      as [ P1 [ r [ Nerr1 [Vr [Tr[H1ok Sub2]]]]]]. clear IHD1.
    inversion Nerr1. subst r. clear Nerr1.
    assert (typing p2 nil (P1 ++ P) e2 t') as T2'.
      apply (typing_weakening p2 nil nil P P1 e2 t' T2); simpl; eauto. clear T2.
    assert (full_set `U` (singl label0) = full_set) as EQ1 by eauto.
    destruct (IHD2 EQ EQ EQ EQ (P1 ++ P) H1ok t' p2 T2')
      as [P2[v2[Nerr2[Vv2[Tv2[H2ok Sub3]]]]]]. clear IHD2.
    inversion Nerr2. subst v2. clear Nerr2 EQ.
    destruct (typing_loc_inv phi_0 nil (P1 ++ P) ptr0 label0 (typ_ref teff t') Tr)
      as [_[_ [t'' [Sub4 B]]]]. clear Tr.
    destruct H2ok as [P2ok[Domeq _ ]].
    assert False. apply H. rewrite Domeq. apply binds_In with t''.
    apply binds_concat_ok. assumption. assumption. destruct H0.
  Case "assign_l_w".
    destruct H0. subst rst2. apply (Full_intro label).
Qed.
