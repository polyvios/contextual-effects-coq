Set Undo 10000.

Require Import Contextual.

Inductive typed_evaluation :
  forall p P P' e v t,
  typing p nil P e t -> labelset -> labelset -> heap -> exp ->
  labelset ->
  typing phi_0 nil P' v t -> labelset -> labelset -> heap -> exp -> Prop :=
  | id_a : forall p fst rst heap v P t (Tv : typing p nil P v t)
      (V : value v),
      typed_evaluation p P P v v t
        Tv fst rst heap v empty_set
        (generalize_value_phi v nil P p t V Tv) fst rst heap v
  | call_a : forall e1 e2 e v2 v fst fst1 fst2 fst' rst rst1 rst2 rst'
                    heap heap1 heap2 heap' eff1 eff2 eff3
                    phi phi1 phi2 phif P P1 P2 P3 t1 t2 t
                    (T1 : typing phi1 nil P e1 (typ_fun phif t1 t2))
                    (Tlam : typing phi_0 nil P1 (e_lam e) (typ_fun phif t1 t2))
                    (T2 : typing phi2 nil P1 e2 t1)
                    (Tv2 : typing phi_0 nil P2 v2 t1)
                    (T3 : typing phif nil P2 (open e v2) t)
                    (T : typing phi nil P (e_app e1 e2) t)
                    (Tv : typing phi_0 nil P3 v t)
                    phi3 phi',
      comb_cflow phi1 phi2 phi3 ->
      comb_cflow phi3 phif phi' ->
      phi_sub phi' phi ->
      typed_evaluation phi1 P P1 e1 (e_lam e) (typ_fun phif t1 t2)
        T1 fst rst heap e1 eff1 Tlam fst1 rst1 heap1 (e_lam e) ->
      typed_evaluation phi2 P1 P2 e2 v2 t1
        T2 fst1 rst1 heap1 e2 eff2 Tv2 fst2 rst2 heap2 v2 ->
      typed_evaluation phif P2 P3 (open e v2) v t
        T3 fst2 rst2 heap2 (open e v2) eff3 Tv fst' rst' heap' v ->
      typed_evaluation phi P P3 (e_app e1 e2) v t
        T fst rst heap (e_app e1 e2) (eff1 `U` eff2 `U` eff3)
        Tv fst' rst' heap' v
  | ref_a : forall fst fst' rst rst' heap heap' e eff v r l
                   teff t phi phi' P P'
                   (T1 : typing phi' nil P e t)
                   (Tv : typing phi_0 nil P' v t)
                   (T : typing phi nil P (e_ref l e) (typ_ref teff t))
                   (Tloc : typing phi_0 nil ((r,t)::P') (e_loc r l) (typ_ref teff t)),
      phi_sub phi' phi ->
      typed_evaluation phi' P P' e v t
        T1 fst rst heap e eff Tv fst' rst' heap' v ->
      r `notin` (dom heap') ->
      typed_evaluation phi P ((r,t)::P') (e_ref l e) (e_loc r l) (typ_ref teff t)
        T fst rst heap (e_ref l e) eff
        Tloc fst' rst' ((r,v)::heap') (e_loc r l)
  | deref_a : forall fst fst' rst rst' eff l heap heap' e r v
                     phi phi1 phi' P P' t t' teff fst2 rst2
                     (T1 : typing phi1 nil P e (typ_ref teff t'))
                     (Tloc : typing phi_0 nil P' (e_loc r l) (typ_ref teff t'))
                     (T : typing phi nil P (e_deref e) t)
                     (Tv : typing phi_0 nil P' v t),
      comb_cflow phi1 (make_phi fst2 teff rst2) phi' ->
      phi_sub phi' phi ->
      subtype t' t ->
      typed_evaluation phi1 P P' e (e_loc r l) (typ_ref teff t')
        T1 fst rst heap e eff
        Tloc fst' (rst' `U` (singl l)) heap' (e_loc r l) ->
      r `in` (dom heap') ->
      binds r v heap' ->
      typed_evaluation phi P P' (e_deref e) v t
        T fst rst heap (e_deref e) (eff `U` (singl l))
        Tv (fst' `U` (singl l)) rst' heap' v
  | assign_a : forall fst fst1 fst2 eff1 eff2 rst rst1 rst2
                      e1 e2 heap heap1 heap2 r l v v' p p1 p2 p3 p'
                      fst3 rst3 teff t t' P P1 P2
                      (T: typing p nil P (e_assign e1 e2) t)
                      (T1: typing p1 nil P e1 (typ_ref teff t'))
                      (Tr: typing phi_0 nil P1 (e_loc r l) (typ_ref teff t'))
                      (T2: typing p2 nil P1 e2 t')
                      (Tv: typing phi_0 nil P2 v t')
                      (Tv': typing phi_0 nil P2 v t),
      phi_sub p' p ->
      subtype t' t ->
      comb_cflow p1 p2 p3 ->
      comb_cflow p3 (make_phi fst3 teff rst3) p' ->
      typed_evaluation p1 P P1 e1 (e_loc r l) (typ_ref teff t') 
                 T1 fst rst heap e1 eff1
                 Tr fst1 rst1 heap1 (e_loc r l) ->
      typed_evaluation p2 P1 P2 e2 v t'
                 T2 fst1 rst1 heap1 e2 eff2
                 Tv fst2 (rst2 `U` (singl l)) heap2 v ->
      binds r v' heap2 ->
      typed_evaluation p P P2 (e_assign e1 e2) v t 
                 T fst rst heap (e_assign e1 e2)
                 ((eff1 `U` eff2) `U` (singl l))
                 Tv' (fst2 `U` (singl l)) rst2
                 (replace heap2 r v) v
  | let_in_a : forall p p' p1 p2 P P1 P2 t1 t2 t
                    fst rst heap e1 eff1 fst1 rst1 heap1 v1 
                    e2 eff2 fst2 rst2 heap2 v2
                    T T1 T2 Tv1 Tv2 Tv2',
      comb_cflow p1 p2 p ->
      phi_sub p p' ->
      subtype t2 t ->
      typed_evaluation p1 P P1 e1 v1 t1 T1 fst rst heap e1 eff1
                       Tv1 fst1 rst1 heap1 v1 ->
      typed_evaluation p2 P1 P2 (open e2 v1) v2 t2
                       T2 fst1 rst1 heap1 (open e2 v1) eff2
                       Tv2 fst2 rst2 heap2 v2 ->
      typed_evaluation p' P P2 (e_let e1 e2) v2 t
                       T fst rst heap (e_let e1 e2) (eff1 `U` eff2)
                       Tv2' fst2 rst2 heap2 v2
  | if_t_a : forall fst rst heap e1 e2 e3 v
                    fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
                    p1 p2 p p' t t' P P1 P2
                    (T: typing p' nil P (e_if e1 e2 e3) t')
                    (T1: typing p1 nil P e1 typ_int)
                    (Tn: typing phi_0 nil P1 (e_nat 0) typ_int)
                    (T2: typing p2 nil P1 e2 t)
                    (T3: typing p2 nil P1 e3 t)
                    (Tv: typing phi_0 nil P2 v t)
                    (Tv': typing phi_0 nil P2 v t')
,
      comb_cflow p1 p2 p ->
      phi_sub p p' ->
      subtype t t' ->
      typed_evaluation p1 P P1 e1 (e_nat 0) typ_int
                       T1 fst rst heap e1 eff1
                       Tn fst1 rst1 heap1 (e_nat 0) ->
      typed_evaluation p2 P1 P2 e2 v t
                       T2 fst1 rst1 heap1 e2 eff2
                       Tv fst2 rst2 heap2 v ->
      typed_evaluation p' P P2 (e_if e1 e2 e3) v t'
                       T fst rst heap (e_if e1 e2 e3) (eff1 `U` eff2)
                       Tv' fst2 rst2 heap2 v
  | if_f_a : forall fst rst heap e1 e2 e3 v
                    fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
                    p1 p2 p p' t t' P P1 P2 n
                    (T: typing p' nil P (e_if e1 e2 e3) t')
                    (T1: typing p1 nil P e1 typ_int)
                    (Tn: typing phi_0 nil P1 (e_nat n) typ_int)
                    (T2: typing p2 nil P1 e2 t)
                    (T3: typing p2 nil P1 e3 t)
                    (Tv: typing phi_0 nil P2 v t)
                    (Tv': typing phi_0 nil P2 v t')
,
      n <> 0 ->
      comb_cflow p1 p2 p ->
      phi_sub p p' ->
      subtype t t' ->
      typed_evaluation p1 P P1 e1 (e_nat n) typ_int
                       T1 fst rst heap e1 eff1
                       Tn fst1 rst1 heap1 (e_nat n) ->
      typed_evaluation p2 P1 P2 e3 v t
                       T3 fst1 rst1 heap1 e3 eff2
                       Tv fst2 rst2 heap2 v ->
      typed_evaluation p' P P2 (e_if e1 e2 e3) v t'
                       T fst rst heap (e_if e1 e2 e3) (eff1 `U` eff2)
                       Tv' fst2 rst2 heap2 v
.

Lemma strip_typings :
  forall phi P P' e v t
         (T : typing phi nil P e t) fst rst heap eff
         (Tv : typing phi_0 nil P' v t) fst' rst' heap',
    typed_evaluation phi P P' e v t T fst rst heap e eff Tv fst' rst' heap' v ->
    evaluation fst rst heap e eff fst' rst' heap' (exp_result v).
Proof.
  intros.
  induction H; eauto.
Qed.

Lemma environment_grows :
  forall phi P P' e v t
         (T : typing phi nil P e t) fst rst heap eff
         (Tv : typing phi_0 nil P' v t) fst' rst' heap',
    typed_evaluation phi P P' e v t T fst rst heap e eff Tv fst' rst' heap' v ->
    exists P1,
      P' = P1 ++ P.
Proof with simpl; simpl_env; reflexivity.
  intros.
  induction H; simpl_env;
    (repeat (match goal with | H : exists x, _ |- _ => destruct H end));
    subst; (repeat rewrite <- concat_assoc);
    (match goal with
       | |- exists P1, ?x ++ ?P = _ => exists x
       | |- exists P1, ?P = _ => exists (nil:env)
     end); simpl_env; reflexivity.
Qed.

Lemma eval_to_value_and_heap :
    forall phi P P' e v t
         (T : typing phi nil P e t) fst rst heap eff
         (Tv : typing phi_0 nil P' v t) fst' rst' heap',
    heap_ok P heap ->
    typed_evaluation phi P P' e v t T fst rst heap e eff Tv fst' rst' heap' v ->
    value v /\ heap_ok P' heap'.
Proof.
  intros phi P P' e v t T fst rst heap eff Tv fst' rst' heap' Hok D.
  induction D;
    repeat (match goal with | [ Hok : ?e,  H : ?e -> _ |- _ ] => destruct H; auto end);
    eauto.
  Case "ref".
    split.
      apply loc_value.
      apply heap_push; auto.
        destruct H2 as [ _ [ Eq _ ]].
        rewrite <- Eq. assumption.
  Case "deref".
    split. apply (value_in_heap P' heap' r v0 H5 H3).
    assumption.
  Case "assign".
    split. assumption.
    destruct (typing_loc_inv phi_0 nil P1 r l (typ_ref teff t') Tr)
      as [_[_ [tt [Sub B]]]].
    destruct (environment_grows p1 P P1 e1 (e_loc r l) (typ_ref teff t')
      T1 fst rst heap eff1 Tr fst1 rst1 heap1 D1).
    destruct (environment_grows p2 P1 P2 e2 v0 t'
      T2 fst1 rst1 heap1 eff2 Tv fst2 (rst2 `U` (singl l)) heap2 D2).
    subst P2 P1.
    eapply heap_ok_after_replace; eauto using binds_concat_ok, env_ok.
    inversion Sub. subst. assert (tt = t'); auto. subst. assumption.
Qed.

Lemma consistent_states :
  forall phi P P' e v t
         (T : typing phi nil P e t) fst rst heap eff
         (Tv : typing phi_0 nil P' v t) fst' rst' heap',
    heap_ok P heap ->
    typed_evaluation phi P P' e v t T fst rst heap e eff Tv fst' rst' heap' v ->
    heap_ok P' heap'.
Proof.
  intros.
  destruct (eval_to_value_and_heap phi P P' e v t T fst rst heap eff
    Tv fst' rst' heap' H);
  assumption.
Qed.

Hint Resolve consistent_states.

Lemma typed_eval_to_value :
  forall phi P P' e v t
         (T : typing phi nil P e t) fst rst heap eff
         (Tv : typing phi_0 nil P' v t) fst' rst' heap',
    heap_ok P heap ->
    typed_evaluation phi P P' e v t T fst rst heap e eff Tv fst' rst' heap' v ->
    value v.
Proof.
  intros.
  destruct (eval_to_value_and_heap phi P P' e v t T fst rst heap eff Tv fst' rst' heap' H); assumption.
Qed.

Hint Resolve typed_eval_to_value.

Lemma comb_sub : forall p1 p2 p3,
  comb_cflow p1 p2 p3 ->
  phi_sub p1 p3.
Proof.
  intros. inversion H. subst p1 p2 p3.
  apply sub_context; unfold subset in *; mysolve.
Qed.

Lemma annotated_evaluation_exists :
  forall p P e t fst rst heap eff fst' rst' heap' v
    (T : typing p nil P e t)
    (D : evaluation fst rst heap e eff fst' rst' heap' (exp_result v)),
    heap_ok P heap ->
    exists P', exists T' : typing phi_0 nil (P' ++ P) v t,
      typed_evaluation p P (P' ++ P) e v t T fst rst heap e eff T' fst' rst' heap' v.
Proof.
  intros.
  remember (exp_result v) as R.
  generalize dependent v.
  generalize dependent P.
  generalize dependent t.
  generalize dependent p.
  induction D; intros p t P T Hok vv Eq; inversion Eq; subst vv; clear Eq.
  Case "id".
    exists (nil:env).
    simpl_env.
    exists (generalize_value_phi v nil P p t H T).
    apply id_a.
  Case "app".
    destruct (typing_app_inv p nil P e1 e2 t T)
      as [ phi1 [ phi2 [ phi3 [ phif [ t1 [ phi' [ C1 [ C2 [ Sub1 [ T1 T2 ]]]]]]]]]].
    destruct (IHD1 phi1 (typ_fun phif t1 t) P T1 Hok (e_lam e))
      as [ P1 [ Tlam E1 ]]. reflexivity. clear D1 IHD1.
    assert (heap_ok (P1 ++ P) heap1) as H1ok by eauto.
    assert (typing phi2 (nil ++ nil) (P1 ++ P) e2 t1) as T2'.
      apply typing_weakening. assumption. simpl_env. auto.
      destruct (typing_env_ok phi_0 nil (P1 ++ P) (e_lam e) (typ_fun phif t1 t) Tlam).
      assumption. simpl_env in T2'. clear T2.
    destruct (IHD2 phi2 t1 (P1 ++ P) T2' H1ok v2)
      as [ P2 [ Tv2 E2 ]]. reflexivity. clear D2 IHD2.
    assert (heap_ok (P2 ++ P1 ++ P) heap2) as H2ok by eauto.
    assert (typing phi_0 nil (P2 ++ P1 ++ P) (e_lam e) (typ_fun phif t1 t)) as Tlam'.
      apply (typing_weakening phi_0 nil nil (P1 ++ P) P2 (e_lam e)
                 (typ_fun phif t1 t) Tlam); simpl.
        apply ok_nil.
        apply env_ok with heap2. assumption.
    destruct (typing_lam_inv _ _ _ _ _ Tlam' phif t1 t (subtype_refl (typ_fun phif t1 t)))
      as [ L Tf ].
    assert (typing phif nil (P2 ++ P1 ++ P) (open e v2) t) as T3.
        pick fresh y.
        rewrite (subst_intro y).
        apply typing_subst with t1. apply Tf. decideFSet. assumption.
        decideFSet.
        apply typing_regular_lc
          with (p := phi_0) (E := nil:env) (P := P2 ++ P1 ++ P) (T := t1).
        apply Tv2.
    destruct (IHD3 phif t (P2 ++ P1 ++ P) T3 H2ok v) as [ P3 [ Tv E3 ]]. reflexivity.
      clear D3 IHD3.
    exists (P3 ++ P2 ++ P1). simpl_env.
    exists Tv.
    eapply call_a. apply C1. apply C2. assumption.
      apply E1. apply E2. apply E3.
  Case "ref".
    destruct (typing_ref_inv p nil P e t l T) as [eff [t' [Sub [T' I]]]].
    destruct (IHD p t' P T' Hok v) as [P' [ Tv E ]]. reflexivity. clear IHD.
    destruct (eval_to_value_and_heap p P (P' ++ P) e v t'
      T' fst rst heap teff Tv fst' rst' heap' Hok E) as [ V H'ok ].
    assert (typing phi_0 nil ((r,t')::P' ++ P) (e_loc r l) t) as Tloc.
      apply typing_sub with (p' := phi_0) (T' := typ_ref (singl l) t').
        apply typing_loc.
          apply ok_nil. 
          apply env_ok with ((r,v)::heap').
          apply heap_push; try assumption.
            destruct H'ok as [ _ [ Dom _ ]]. rewrite <- Dom. assumption. 
          simpl_env. apply binds_head. apply binds_singleton.
        apply subtype_trans with (typ_ref eff t').
          apply sub_ref; auto. mysolve.
          assumption. apply phi_sub_refl.
    exists ((r,t')::P'). exists Tloc. simpl.
    inversion Sub. subst. assert (t'0 = t'). apply subtype_eq; assumption. subst.
    apply ref_a with p T' Tv. apply phi_sub_refl. apply E. assumption.
  Case "deref".
    destruct (typing_deref_inv p nil P e t T)
      as [p1[fst1[teff1[rst1[t'[p'[Sub[PS[T' Cf]]]]]]]]].
    destruct (IHD p1 (typ_ref teff1 t') P T' Hok (e_loc ptr l))
      as [P' [ Tloc E ]]. reflexivity.
    destruct (typing_loc_inv phi_0 nil (P' ++ P) ptr l (typ_ref teff1 t') Tloc)
      as [_[_ [t'' [Sub2 B]]]].
    inversion Sub2. assert (t'' = t'). apply subtype_eq; assumption. subst. 
    exists P'.
    assert (typing phi_0 nil (P' ++ P) v t) as Tv.
    apply typing_sub with phi_0 t'; auto.
    apply typing_in_heap with heap' ptr; eauto.
    exists Tv.
    eauto using deref_a.
  Case "assign".
    destruct (typing_assign_inv p nil P e1 e2 t T)
      as [t'[p'[p1[p2[p3[tfst[teff[trst[Cf1 [Cf2[Sub[PS[T1 T2]]]]]]]]]]]]].
    destruct (IHD1 p1 (typ_ref teff t') P T1 Hok (e_loc ptr l))
      as [ P1 [ Tr E1 ]]. reflexivity. clear D1 IHD1.
    assert (heap_ok (P1 ++ P) heap1) as H1ok by eauto.
    assert (typing p2 (nil ++ nil) (P1 ++ P) e2 t') as T2'. 
      apply typing_weakening; simpl_env; eauto.
    destruct (IHD2 p2 t' (P1 ++ P) T2' H1ok v) as [ P2 [ Tv E2 ]].
      reflexivity. clear IHD2 D2.
    assert (heap_ok (P2 ++ P1 ++ P) heap2) as H2ok by eauto.
    assert (typing phi_0 nil (P2 ++ P1 ++ P) v t) as Tv'. eauto.
    exists (P2 ++ P1). simpl_env. exists Tv'.
    eauto using assign_a.
  Case "let".
    destruct (typing_let_inv p nil P e1 e2 t T)
      as [p1[p2[t1[p'[Cf[PS[T1[L HH]]]]]]]].
    destruct (IHD1 p1 t1 P T1 Hok v1) as [P1[Tv1 E1]]. reflexivity. clear IHD1 D1.
    assert (heap_ok (P1 ++ P) heap1) as H1ok.
      eapply consistent_states. apply Hok. apply E1.
    assert (typing p2 (nil++nil) (P1 ++ P) (open e2 v1) t) as T2.
      pick fresh y.
      rewrite (subst_intro y).
      apply typing_subst with t1. rewrite_env (nil ++ ((y,t1)::nil)).
        apply typing_weakening. apply HH. decideFSet.
        simpl_env. auto.
        eauto.
        simpl. assumption. decideFSet.
        eauto using typing_regular_lc.
    simpl in *.
    destruct (IHD2 p2 t (P1 ++ P) T2 H1ok v2) as [P2[Tv E2]]. reflexivity. clear D2 IHD2.
    exists (P2 ++ P1). simpl_env.
    exists Tv.
    eauto using let_in_a.
  Case "if-t".
    destruct (typing_if_inv p nil P e1 e2 e3 t T)
      as [p1[p2[p'[t'[T1[T2[T3[Cf[PS Sub]]]]]]]]].
    destruct (IHD1 p1 typ_int P T1 Hok (e_nat 0))
      as [P1[T0 E1]]. reflexivity. clear D1 IHD1.
    assert (heap_ok (P1 ++ P) heap1) as H1ok by eauto.
    assert (typing p2 (nil ++ nil) (P1 ++ P) e2 t') as T2'.
      apply typing_weakening; simpl_env; eauto. clear T2.
    assert (typing p2 (nil ++ nil) (P1 ++ P) e3 t') as T3'.
      apply typing_weakening; simpl_env; eauto. clear T3.
    destruct (IHD2 p2 t' (P1 ++ P) T2' H1ok v) as [P2[Tv E2]].
      reflexivity. clear D2 IHD2.
    assert (typing phi_0 nil (P2 ++ P1 ++ P) v t) as Tv'.
      apply typing_sub with phi_0 t'; auto.
    exists (P2 ++ P1).
    simpl_env. exists Tv'.
    eauto using if_t_a.
  Case "if-f".
    destruct (typing_if_inv p nil P e1 e2 e3 t T)
      as [p1[p2[p'[t'[T1[T2[T3[Cf[PS Sub]]]]]]]]].
    destruct (IHD1 p1 typ_int P T1 Hok (e_nat n)) as [P1[T0 E1]].
      reflexivity. clear D1 IHD1.
    assert (heap_ok (P1 ++ P) heap1) as H1ok by eauto.
    assert (typing p2 (nil ++ nil) (P1 ++ P) e2 t') as T2'.
      apply typing_weakening; simpl_env; eauto. clear T2.
    assert (typing p2 (nil ++ nil) (P1 ++ P) e3 t') as T3'.
      apply typing_weakening; simpl_env; eauto. clear T3.
    destruct (IHD2 p2 t' (P1 ++ P) T3' H1ok v) as [P2[Tv E2]].
      reflexivity. clear D2 IHD2.
    assert (typing phi_0 nil (P2 ++ P1 ++ P) v t) as Tv'.
      apply typing_sub with phi_0 t'; auto.
    exists (P2 ++ P1).
    simpl_env. exists Tv'.
    eauto using if_f_a.
Qed.

Inductive sub_derivation :
  forall phi1 P1 P1' e1 v1 t1 (T1 : typing phi1 nil P1 e1 t1)
    fst1 rst1 heap1 eff1 Tv1 fst1' rst1' heap1'
    phi2 P2 P2' e2 v2 t2 T2 fst2 rst2 heap2 eff2 Tv2 fst2' rst2' heap2',
  typed_evaluation phi1 P1 P1' e1 v1 t1 T1 fst1 rst1 heap1 e1 eff1
    Tv1 fst1' rst1' heap1' v1 ->
  typed_evaluation phi2 P2 P2' e2 v2 t2 T2 fst2 rst2 heap2 e2 eff2
    Tv2 fst2' rst2' heap2' v2 ->
  Prop :=
  | call1 : forall e1 e2 e v2 v fst fst1 fst2 fst' rst rst1 rst2 rst'
      heap heap1 heap2 heap' eff1 eff2 eff3
      phi phi1 phi2 phif P P1 P2 P3 t1 t2 t
      (T1 : typing phi1 nil P e1 (typ_fun phif t1 t2))
      (Tlam : typing phi_0 nil P1 (e_lam e) (typ_fun phif t1 t2))
      (T2 : typing phi2 nil P1 e2 t1)
      (Tv2 : typing phi_0 nil P2 v2 t1)
      (T3 : typing phif nil P2 (open e v2) t)
      (T : typing phi nil P (e_app e1 e2) t)
      (Tv : typing phi_0 nil P3 v t)
      phi3 phi' Cf1 Cf2 Sub
      (E1 : typed_evaluation phi1 P P1 e1 (e_lam e) (typ_fun phif t1 t2)
        T1 fst rst heap e1 eff1 Tlam fst1 rst1 heap1 (e_lam e)) 
      (E2 : typed_evaluation phi2 P1 P2 e2 v2 t1
        T2 fst1 rst1 heap1 e2 eff2 Tv2 fst2 rst2 heap2 v2)
      (E3 : typed_evaluation phif P2 P3 (open e v2) v t
        T3 fst2 rst2 heap2 (open e v2) eff3 Tv fst' rst' heap' v),
      sub_derivation phi1 P P1 e1 (e_lam e) (typ_fun phif t1 t2)
        T1 fst rst heap eff1 Tlam fst1 rst1 heap1
        phi P P3 (e_app e1 e2) v t T fst rst heap (eff1 `U` eff2 `U` eff3)
        Tv fst' rst' heap'
        E1
        (call_a e1 e2 e v2 v fst fst1 fst2 fst' rst rst1 rst2 rst'
                    heap heap1 heap2 heap' eff1 eff2 eff3
                    phi phi1 phi2 phif P P1 P2 P3 t1 t2 t
                    T1 Tlam T2 Tv2 T3 T Tv
                    phi3 phi' Cf1 Cf2 Sub E1 E2 E3)
  | call2 : forall e1 e2 e v2 v fst fst1 fst2 fst' rst rst1 rst2 rst'
      heap heap1 heap2 heap' eff1 eff2 eff3
      phi phi1 phi2 phif P P1 P2 P3 t1 t2 t
      (T1 : typing phi1 nil P e1 (typ_fun phif t1 t2))
      (Tlam : typing phi_0 nil P1 (e_lam e) (typ_fun phif t1 t2))
      (T2 : typing phi2 nil P1 e2 t1)
      (Tv2 : typing phi_0 nil P2 v2 t1)
      (T3 : typing phif nil P2 (open e v2) t)
      (T : typing phi nil P (e_app e1 e2) t)
      (Tv : typing phi_0 nil P3 v t)
      phi3 phi' Cf1 Cf2 Sub
      (E1 : typed_evaluation phi1 P P1 e1 (e_lam e) (typ_fun phif t1 t2)
        T1 fst rst heap e1 eff1 Tlam fst1 rst1 heap1 (e_lam e)) 
      (E2 : typed_evaluation phi2 P1 P2 e2 v2 t1
        T2 fst1 rst1 heap1 e2 eff2 Tv2 fst2 rst2 heap2 v2)
      (E3 : typed_evaluation phif P2 P3 (open e v2) v t
        T3 fst2 rst2 heap2 (open e v2) eff3 Tv fst' rst' heap' v),
      sub_derivation phi2 P1 P2 e2 v2 t1 T2 fst1 rst1 heap1 eff2
        Tv2 fst2 rst2 heap2
        phi P P3 (e_app e1 e2) v t T fst rst heap (eff1 `U` eff2 `U` eff3)
        Tv fst' rst' heap'
        E2
        (call_a e1 e2 e v2 v fst fst1 fst2 fst' rst rst1 rst2 rst'
                    heap heap1 heap2 heap' eff1 eff2 eff3
                    phi phi1 phi2 phif P P1 P2 P3 t1 t2 t
                    T1 Tlam T2 Tv2 T3 T Tv
                    phi3 phi' Cf1 Cf2 Sub E1 E2 E3)
  | call3 : forall e1 e2 e v2 v fst fst1 fst2 fst' rst rst1 rst2 rst'
      heap heap1 heap2 heap' eff1 eff2 eff3
      phi phi1 phi2 phif P P1 P2 P3 t1 t2 t
      (T1 : typing phi1 nil P e1 (typ_fun phif t1 t2))
      (Tlam : typing phi_0 nil P1 (e_lam e) (typ_fun phif t1 t2))
      (T2 : typing phi2 nil P1 e2 t1)
      (Tv2 : typing phi_0 nil P2 v2 t1)
      (T3 : typing phif nil P2 (open e v2) t)
      (T : typing phi nil P (e_app e1 e2) t)
      (Tv : typing phi_0 nil P3 v t)
      phi3 phi' Cf1 Cf2 Sub
      (E1 : typed_evaluation phi1 P P1 e1 (e_lam e) (typ_fun phif t1 t2)
        T1 fst rst heap e1 eff1 Tlam fst1 rst1 heap1 (e_lam e)) 
      (E2 : typed_evaluation phi2 P1 P2 e2 v2 t1
        T2 fst1 rst1 heap1 e2 eff2 Tv2 fst2 rst2 heap2 v2)
      (E3 : typed_evaluation phif P2 P3 (open e v2) v t
        T3 fst2 rst2 heap2 (open e v2) eff3 Tv fst' rst' heap' v),
      sub_derivation phif P2 P3 (open e v2) v t T3 fst2 rst2 heap2 eff3
        Tv fst' rst' heap'
        phi P P3 (e_app e1 e2) v t T fst rst heap (eff1 `U` eff2 `U` eff3)
        Tv fst' rst' heap'
        E3
        (call_a e1 e2 e v2 v fst fst1 fst2 fst' rst rst1 rst2 rst'
                    heap heap1 heap2 heap' eff1 eff2 eff3
                    phi phi1 phi2 phif P P1 P2 P3 t1 t2 t
                    T1 Tlam T2 Tv2 T3 T Tv
                    phi3 phi' Cf1 Cf2 Sub E1 E2 E3)
  | ref1 : forall fst fst' rst rst' heap heap' e eff v r l
                   teff t phi phi' P P'
                   (T1 : typing phi' nil P e t)
                   (Tv : typing phi_0 nil P' v t)
                   (T : typing phi nil P (e_ref l e) (typ_ref teff t))
                   (Tloc : typing phi_0 nil ((r,t)::P') (e_loc r l) (typ_ref teff t))
                   PS
                   (E1 : typed_evaluation phi' P P' e v t T1 fst rst heap e eff
                        Tv fst' rst' heap' v)
                   Notin,
      sub_derivation phi' P P' e v t T1 fst rst heap eff Tv fst' rst' heap'
        phi P ((r,t)::P') (e_ref l e) (e_loc r l) (typ_ref teff t) T fst rst heap eff
        Tloc fst' rst' ((r,v)::heap')
        E1
        (ref_a fst fst' rst rst' heap heap' e eff v r l
           teff t phi phi' P P'
           (T1 : typing phi' nil P e t)
           (Tv : typing phi_0 nil P' v t)
           (T : typing phi nil P (e_ref l e) (typ_ref teff t))
           (Tloc : typing phi_0 nil ((r,t)::P') (e_loc r l) (typ_ref teff t))
           PS
           E1
           Notin)
  | deref1 : forall fst fst' rst rst' eff l heap heap' e r v
                     phi phi1 phi' P P' t t' teff fst2 rst2
                     (T1 : typing phi1 nil P e (typ_ref teff t'))
                     (Tloc : typing phi_0 nil P' (e_loc r l) (typ_ref teff t'))
                     (T : typing phi nil P (e_deref e) t)
                     (Tv : typing phi_0 nil P' v t)
                     Cf PS Sub
                     (E1 : typed_evaluation phi1 P P' e (e_loc r l) (typ_ref teff t')
                       T1 fst rst heap e eff
                       Tloc fst' (rst' `U` (singl l)) heap' (e_loc r l))
                     Ih B,
      sub_derivation phi1 P P' e (e_loc r l) (typ_ref teff t')
        T1 fst rst heap eff Tloc fst' (rst' `U` (singl l)) heap'
        phi P P' (e_deref e) v t T fst rst heap (eff `U` (singl l))
        Tv (fst' `U` (singl l)) rst' heap'
        E1
        (deref_a fst fst' rst rst' eff l heap heap' e r v
                     phi phi1 phi' P P' t t' teff fst2 rst2
                     T1 Tloc T Tv Cf PS Sub E1 Ih B)
  | assign1 : forall fst fst1 fst2 eff1 eff2 rst rst1 rst2
      e1 e2 heap heap1 heap2 r l v v' p p1 p2 p3 p'
      fst3 rst3 teff t t' P P1 P2
      (T: typing p nil P (e_assign e1 e2) t)
      (T1: typing p1 nil P e1 (typ_ref teff t'))
      (Tr: typing phi_0 nil P1 (e_loc r l) (typ_ref teff t'))
      (T2: typing p2 nil P1 e2 t')
      (Tv: typing phi_0 nil P2 v t')
      (Tv': typing phi_0 nil P2 v t)
      Cf1 Cf2 PS Sub
      (E1 : typed_evaluation p1 P P1 e1 (e_loc r l) (typ_ref teff t')
        T1 fst rst heap e1 eff1 Tr fst1 rst1 heap1 (e_loc r l))
      (E2 : typed_evaluation p2 P1 P2 e2 v t'
                 T2 fst1 rst1 heap1 e2 eff2
                 Tv fst2 (rst2 `U` (singl l)) heap2 v)
      B,
      sub_derivation p1 P P1 e1 (e_loc r l) (typ_ref teff t')
        T1 fst rst heap eff1 Tr fst1 rst1 heap1
        p P P2 (e_assign e1 e2) v t T fst rst heap
        ((eff1 `U` eff2) `U` (singl l))
        Tv' (fst2 `U` (singl l)) rst2 (replace heap2 r v)
        E1
        (assign_a fst fst1 fst2 eff1 eff2 rst rst1 rst2
          e1 e2 heap heap1 heap2 r l v v' p p1 p2 p3 p' fst3 rst3 teff t t' P P1 P2
          T T1 Tr T2 Tv Tv' PS Sub Cf1 Cf2 E1 E2 B)
  | assign2 : forall fst fst1 fst2 eff1 eff2 rst rst1 rst2
      e1 e2 heap heap1 heap2 r l v v' p p1 p2 p3 p'
      fst3 rst3 teff t t' P P1 P2
      (T: typing p nil P (e_assign e1 e2) t)
      (T1: typing p1 nil P e1 (typ_ref teff t'))
      (Tr: typing phi_0 nil P1 (e_loc r l) (typ_ref teff t'))
      (T2: typing p2 nil P1 e2 t')
      (Tv: typing phi_0 nil P2 v t')
      (Tv': typing phi_0 nil P2 v t)
      Cf1 Cf2 PS Sub
      (E1 : typed_evaluation p1 P P1 e1 (e_loc r l) (typ_ref teff t')
        T1 fst rst heap e1 eff1 Tr fst1 rst1 heap1 (e_loc r l))
      (E2 : typed_evaluation p2 P1 P2 e2 v t'
                 T2 fst1 rst1 heap1 e2 eff2
                 Tv fst2 (rst2 `U` (singl l)) heap2 v)
      B,
      sub_derivation p2 P1 P2 e2 v t'
        T2 fst1 rst1 heap1 eff2 Tv fst2 (rst2 `U` (singl l)) heap2
        p P P2 (e_assign e1 e2) v t T fst rst heap
        ((eff1 `U` eff2) `U` (singl l))
        Tv' (fst2 `U` (singl l)) rst2 (replace heap2 r v)
        E2
        (assign_a fst fst1 fst2 eff1 eff2 rst rst1 rst2
          e1 e2 heap heap1 heap2 r l v v' p p1 p2 p3 p' fst3 rst3 teff t t' P P1 P2
          T T1 Tr T2 Tv Tv' PS Sub Cf1 Cf2 E1 E2 B)
  | let_in1 : forall p p' p1 p2 P P1 P2 t1 t2 t
      fst rst heap e1 eff1 fst1 rst1 heap1 v1 
      e2 eff2 fst2 rst2 heap2 v2
      T T1 T2 Tv1 Tv2 Tv2'
      Cf PS Sub
      (E1: typed_evaluation p1 P P1 e1 v1 t1 T1 fst rst heap e1 eff1
                       Tv1 fst1 rst1 heap1 v1)
      (E2: typed_evaluation p2 P1 P2 (open e2 v1) v2 t2
                       T2 fst1 rst1 heap1 (open e2 v1) eff2
                       Tv2 fst2 rst2 heap2 v2),
      sub_derivation 
        p1 P P1 e1 v1 t1 T1 fst rst heap eff1 Tv1 fst1 rst1 heap1
        p' P P2 (e_let e1 e2) v2 t T fst rst heap (eff1 `U` eff2) Tv2' fst2 rst2 heap2
        E1
        (let_in_a p p' p1 p2 P P1 P2 t1 t2 t fst rst heap e1 eff1 fst1 rst1 heap1 v1 
          e2 eff2 fst2 rst2 heap2 v2 T T1 T2 Tv1 Tv2 Tv2' Cf PS Sub E1 E2)
  | let_in2 : forall p p' p1 p2 P P1 P2 t1 t2 t
      fst rst heap e1 eff1 fst1 rst1 heap1 v1 
      e2 eff2 fst2 rst2 heap2 v2
      T T1 T2 Tv1 Tv2 Tv2'
      Cf PS Sub
      (E1: typed_evaluation p1 P P1 e1 v1 t1 T1 fst rst heap e1 eff1
                       Tv1 fst1 rst1 heap1 v1)
      (E2: typed_evaluation p2 P1 P2 (open e2 v1) v2 t2
                       T2 fst1 rst1 heap1 (open e2 v1) eff2
                       Tv2 fst2 rst2 heap2 v2),
      sub_derivation 
        p2 P1 P2 (open e2 v1) v2 t2 T2 fst1 rst1 heap1 eff2 Tv2 fst2 rst2 heap2
        p' P P2 (e_let e1 e2) v2 t T fst rst heap (eff1 `U` eff2) Tv2' fst2 rst2 heap2
        E2
        (let_in_a p p' p1 p2 P P1 P2 t1 t2 t fst rst heap e1 eff1 fst1 rst1 heap1 v1 
          e2 eff2 fst2 rst2 heap2 v2 T T1 T2 Tv1 Tv2 Tv2' Cf PS Sub E1 E2)
  | if_t1 : forall fst rst heap e1 e2 e3 v
                   fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
                   p1 p2 p p' t t' P P1 P2
                   (T: typing p' nil P (e_if e1 e2 e3) t')
                   (T1: typing p1 nil P e1 typ_int)
                   (Tn: typing phi_0 nil P1 (e_nat 0) typ_int)
                   (T2: typing p2 nil P1 e2 t)
                   (T3: typing p2 nil P1 e3 t)
                   (Tv: typing phi_0 nil P2 v t)
                   (Tv': typing phi_0 nil P2 v t')
                   Cf PS Sub
      (E1: typed_evaluation p1 P P1 e1 (e_nat 0) typ_int
                       T1 fst rst heap e1 eff1
                       Tn fst1 rst1 heap1 (e_nat 0))
      (E2: typed_evaluation p2 P1 P2 e2 v t
                       T2 fst1 rst1 heap1 e2 eff2
                       Tv fst2 rst2 heap2 v),
      sub_derivation
        p1 P P1 e1 (e_nat 0) typ_int T1 fst rst heap eff1 Tn fst1 rst1 heap1
        p' P P2 (e_if e1 e2 e3) v t' T fst rst heap (eff1 `U` eff2) Tv' fst2 rst2 heap2
        E1
        (if_t_a fst rst heap e1 e2 e3 v fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
          p1 p2 p p' t t' P P1 P2 T T1 Tn T2 T3 Tv Tv' Cf PS Sub E1 E2)
  | if_t2 : forall fst rst heap e1 e2 e3 v
                   fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
                   p1 p2 p p' t t' P P1 P2
                   (T: typing p' nil P (e_if e1 e2 e3) t')
                   (T1: typing p1 nil P e1 typ_int)
                   (Tn: typing phi_0 nil P1 (e_nat 0) typ_int)
                   (T2: typing p2 nil P1 e2 t)
                   (T3: typing p2 nil P1 e3 t)
                   (Tv: typing phi_0 nil P2 v t)
                   (Tv': typing phi_0 nil P2 v t')
                   Cf PS Sub
      (E1: typed_evaluation p1 P P1 e1 (e_nat 0) typ_int
                       T1 fst rst heap e1 eff1
                       Tn fst1 rst1 heap1 (e_nat 0))
      (E2: typed_evaluation p2 P1 P2 e2 v t
                       T2 fst1 rst1 heap1 e2 eff2
                       Tv fst2 rst2 heap2 v),
      sub_derivation
        p2 P1 P2 e2 v t T2 fst1 rst1 heap1 eff2 Tv fst2 rst2 heap2
        p' P P2 (e_if e1 e2 e3) v t' T fst rst heap (eff1 `U` eff2) Tv' fst2 rst2 heap2
        E2
        (if_t_a fst rst heap e1 e2 e3 v fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
          p1 p2 p p' t t' P P1 P2 T T1 Tn T2 T3 Tv Tv' Cf PS Sub E1 E2)
  | if_f1 : forall fst rst heap e1 e2 e3 v
                   fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
                   p1 p2 p p' t t' P P1 P2 n
                   (T: typing p' nil P (e_if e1 e2 e3) t')
                   (T1: typing p1 nil P e1 typ_int)
                   (Tn: typing phi_0 nil P1 (e_nat n) typ_int)
                   (T2: typing p2 nil P1 e2 t)
                   (T3: typing p2 nil P1 e3 t)
                   (Tv: typing phi_0 nil P2 v t)
                   (Tv': typing phi_0 nil P2 v t')
                   NZ Cf PS Sub
      (E1: typed_evaluation p1 P P1 e1 (e_nat n) typ_int
                       T1 fst rst heap e1 eff1
                       Tn fst1 rst1 heap1 (e_nat n))
      (E2: typed_evaluation p2 P1 P2 e3 v t
                       T3 fst1 rst1 heap1 e3 eff2
                       Tv fst2 rst2 heap2 v),
      sub_derivation
        p1 P P1 e1 (e_nat n) typ_int T1 fst rst heap eff1 Tn fst1 rst1 heap1
        p' P P2 (e_if e1 e2 e3) v t' T fst rst heap (eff1 `U` eff2) Tv' fst2 rst2 heap2
        E1
        (if_f_a fst rst heap e1 e2 e3 v fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
          p1 p2 p p' t t' P P1 P2 n T T1 Tn T2 T3 Tv Tv' NZ Cf PS Sub E1 E2)
  | if_f2 : forall fst rst heap e1 e2 e3 v
                   fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
                   p1 p2 p p' t t' P P1 P2 n
                   (T: typing p' nil P (e_if e1 e2 e3) t')
                   (T1: typing p1 nil P e1 typ_int)
                   (Tn: typing phi_0 nil P1 (e_nat n) typ_int)
                   (T2: typing p2 nil P1 e2 t)
                   (T3: typing p2 nil P1 e3 t)
                   (Tv: typing phi_0 nil P2 v t)
                   (Tv': typing phi_0 nil P2 v t')
                   NZ Cf PS Sub
      (E1: typed_evaluation p1 P P1 e1 (e_nat n) typ_int
                       T1 fst rst heap e1 eff1
                       Tn fst1 rst1 heap1 (e_nat n))
      (E2: typed_evaluation p2 P1 P2 e3 v t
                       T3 fst1 rst1 heap1 e3 eff2
                       Tv fst2 rst2 heap2 v),
      sub_derivation
        p2 P1 P2 e3 v t T3 fst1 rst1 heap1 eff2 Tv fst2 rst2 heap2
        p' P P2 (e_if e1 e2 e3) v t' T fst rst heap (eff1 `U` eff2) Tv' fst2 rst2 heap2
        E2
        (if_f_a fst rst heap e1 e2 e3 v fst1 fst2 rst1 rst2 heap1 heap2 eff1 eff2
          p1 p2 p p' t t' P P1 P2 n T T1 Tn T2 T3 Tv Tv' NZ Cf PS Sub E1 E2)
  | transitive_sub_derivation :
      forall phi1 P1 P1' e1 v1 t1 (T1 : typing phi1 nil P1 e1 t1)
        fst1 rst1 heap1 eff1 Tv1 fst1' rst1' heap1'
        phi2 P2 P2' e2 v2 t2 T2 fst2 rst2 heap2 eff2 Tv2 fst2' rst2' heap2'
        phi3 P3 P3' e3 v3 t3 T3 fst3 rst3 heap3 eff3 Tv3 fst3' rst3' heap3'
        E1 E2 E3,
      sub_derivation
        phi1 P1 P1' e1 v1 t1 T1 fst1 rst1 heap1 eff1 Tv1 fst1' rst1' heap1'
        phi2 P2 P2' e2 v2 t2 T2 fst2 rst2 heap2 eff2 Tv2 fst2' rst2' heap2'
        E1 E2 ->
      sub_derivation
        phi2 P2 P2' e2 v2 t2 T2 fst2 rst2 heap2 eff2 Tv2 fst2' rst2' heap2'
        phi3 P3 P3' e3 v3 t3 T3 fst3 rst3 heap3 eff3 Tv3 fst3' rst3' heap3'
        E2 E3 ->
      sub_derivation
        phi1 P1 P1' e1 v1 t1 T1 fst1 rst1 heap1 eff1 Tv1 fst1' rst1' heap1'
        phi3 P3 P3' e3 v3 t3 T3 fst3 rst3 heap3 eff3 Tv3 fst3' rst3' heap3'
        E1 E3
.

Lemma propagate_fst_forward :
  forall fst fst' rst rst' eff heap heap' e v phi P P' t
    (T : typing phi nil P e t)
    (Tv : typing phi_0 nil P' v t)
    (E : typed_evaluation phi P P' e v t T fst rst heap e eff
      Tv fst' rst' heap' v),
    fst' = fst `U` eff.
Proof.
  intros.
  induction E; try assumption; try mysolve.
Qed.

Lemma propagate_rst_back :
  forall fst fst' rst rst' eff heap heap' e v phi P P' t
    (T : typing phi nil P e t)
    (Tv : typing phi_0 nil P' v t)
    (E : typed_evaluation phi P P' e v t T fst rst heap e eff
      Tv fst' rst' heap' v),
    rst = rst' `U` eff.
Proof.
  intros.
  induction E; try assumption; try mysolve.
Qed.

Lemma union_full_set2 : forall s, s `U` full_set = full_set.
Proof.
  intros.
  apply subseteq. split. apply subset_full_set.
  mysolve.
Qed.

Lemma eff_sound :
    forall fst fst' rst rst' eff heap heap' e v phi P P' t
    (T : typing phi nil P e t)
    (Tv : typing phi_0 nil P' v t)
    (E : typed_evaluation phi P P' e v t T fst rst heap e eff Tv fst' rst' heap' v),
    heap_ok P heap ->
    subset eff (phi_fld_eff phi).
Proof.
  intros.
  assert (evaluation fst rst heap e eff fst' rst' heap' (exp_result v)).
    eauto using strip_typings.
  assert (evaluation (fst `U` full_set) (rst `U` full_set) heap e
    eff (fst' `U` full_set) (rst' `U` full_set) heap' (exp_result v)).
    apply evaluation_weakening. assumption.
  repeat rewrite union_full_set2 in H1.
  destruct (standard_effect_soundness phi P heap heap' e eff t (exp_result v)
    full_set full_set full_set full_set) as [ P'' [ vv [ _ [ _ [ _ [ _ H' ]]]]]]; auto.
Qed.

Hint Resolve eff_sound.

Theorem prior_future_effect_soundness :
  forall phi P P' e v t T fst rst heap eff Tv fst' rst' heap'
    phi1 P1 P1' e1 v1 t1 T1 fst1 rst1 heap1 eff1 Tv1 fst1' rst1' heap1'
  (E : typed_evaluation phi P P' e v t T fst rst heap e eff Tv fst' rst' heap' v)
  (E1 : typed_evaluation
    phi1 P1 P1' e1 v1 t1 T1 fst1 rst1 heap1 e1 eff1 Tv1 fst1' rst1' heap1' v1),
  heap_ok P heap ->
  subset fst (phi_fld_fst phi) ->
  subset rst' (phi_fld_rst phi) ->
  sub_derivation
    phi1 P1 P1' e1 v1 t1 T1 fst1 rst1 heap1 eff1 Tv1 fst1' rst1' heap1'
    phi P P' e v t T fst rst heap eff Tv fst' rst' heap'
    E1 E ->
  heap_ok P1 heap1 /\
  subset fst1 (phi_fld_fst phi1) /\
  subset rst1' (phi_fld_rst phi1).
Proof.
  intros phi P P' e v t T fst rst heap eff Tv fst' rst' heap'
    phi1 P1 P1' e1 v1 t1 T1 fst1 rst1 heap1 eff1 Tv1 fst1' rst1' heap1'
    E E1 Hok Subfst Subrst SubD.
  induction SubD.
  Focus 1.
  Case "call1".
    assert (heap_ok P1 heap1) by eauto.
    assert (heap_ok P2 heap2) by eauto.
    assert (heap_ok P3 heap') by eauto.
    assert (value (e_lam e)) by eauto.
    assert (value v2) by eauto.
    assert (value v) by eauto.
    assert (subset eff1 (phi_fld_eff phi1)) by eauto.
    assert (subset eff2 (phi_fld_eff phi2)) by eauto.
    assert (subset eff3 (phi_fld_eff phif)) by eauto.
    inversion Cf1.
    inversion Cf2.
    inversion Sub. subst.
    inversion H17. subst. clear H17.
    inversion H11. subst. clear H11.
    simpl in *.
    clear Cf1 Cf2 Sub.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (rst2 = rst' `U` eff3). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    assert (fst' = fst2 `U` eff3). eauto using propagate_fst_forward.
    subst.
    split; auto.
    split; eauto 4 using subset_trans, subset_add.
  Case "call2".
    assert (heap_ok P1 heap1) by eauto.
    assert (heap_ok P2 heap2) by eauto.
    assert (heap_ok P3 heap') by eauto.
    assert (value (e_lam e)) by eauto.
    assert (value v2) by eauto.
    assert (value v) by eauto.
    assert (subset eff1 (phi_fld_eff phi1)). eauto.
    assert (subset eff2 (phi_fld_eff phi2)). eauto.
    assert (subset eff3 (phi_fld_eff phif)). eauto.
    inversion Cf1.
    inversion Cf2.
    inversion Sub. subst.
    inversion H17. subst. clear H17.
    inversion H11. subst. clear H11.
    simpl in *.
    clear Cf1 Cf2 Sub.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (rst2 = rst' `U` eff3). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    assert (fst' = fst2 `U` eff3). eauto using propagate_fst_forward.
    subst. split; auto.
    split; eauto 3 using subset_trans, subset_add.
  Case "call3".
    assert (heap_ok P1 heap1) by eauto.
    assert (heap_ok P2 heap2) by eauto.
    assert (heap_ok P3 heap') by eauto.
    assert (value (e_lam e)) by eauto.
    assert (value v2) by eauto.
    assert (value v) by eauto.
    assert (subset eff1 (phi_fld_eff phi1)). eauto.
    assert (subset eff2 (phi_fld_eff phi2)). eauto.
    assert (subset eff3 (phi_fld_eff phif)). eauto.
    inversion Cf1.
    inversion Cf2.
    inversion Sub. subst.
    inversion H17. subst. clear H17.
    inversion H11. subst. clear H11.
    simpl in *.
    clear Cf1 Cf2 Sub.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (rst2 = rst' `U` eff3). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    assert (fst' = fst2 `U` eff3). eauto using propagate_fst_forward.
    subst. rewrite union_assoc.
    split; auto.
    split; eauto 4 using subset_trans, subset_add.
  Case "ref".
    assert (heap_ok P' heap') by eauto.
    assert (value v) by eauto.
    assert (subset eff (phi_fld_eff phi')). eauto.
    inversion PS. subst. simpl in *.
    split; eauto 4 using subset_trans, subset_add.
  Case "deref".
    assert (heap_ok P' heap') by eauto.
    assert (value v). eauto using value_in_heap.
    assert (subset eff (phi_fld_eff phi1)). eauto.
    destruct (typing_loc_inv phi_0 nil P' r l (typ_ref teff t') Tloc)
      as [ _ [ _ [ t'' [ Sub' B' ]]]].
    inversion Sub'. subst. clear Sub'.
    assert (t'' = t'). eauto. subst. clear H6 H7.
    inversion PS. subst. clear PS.
    inversion Cf. subst. clear Cf.
    simpl in *.
    split; auto.
    split; eauto 3 using subset_trans, subset_add.
  Case "assign1".
    assert (heap_ok P1 heap1) by eauto.
    assert (heap_ok P2 heap2) by eauto.
    assert (value v) by eauto.
    assert (subset eff1 (phi_fld_eff p1)). eauto.
    assert (subset eff2 (phi_fld_eff p2)). eauto.
    inversion Cf1. subst p1 p2 p3.
    inversion Cf2. subst p' rst4 teff3 fst3 rst0 teff0 fst4.
    inversion PS. subst p rst3 teff0 fst3.
    clear Cf1 Cf2 PS. simpl in *.
    assert (rst1 = (rst2 `U` (singl l)) `U` eff2).
      eauto using propagate_rst_back.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    subst fst1 fst2 rst1 rst.
    destruct (typing_loc_inv phi_0 nil P1 r l (typ_ref teff t') Tr)
      as [ _ [ _ [ t'' [ Sub' B' ]]]].
    inversion Sub'. subst. clear Sub'.
    assert (t'' = t'). eauto. subst.
    split; auto.
    split; eauto 4 using subset_trans, subset_add.
  Case "assign2".
    assert (heap_ok P1 heap1) by eauto.
    assert (heap_ok P2 heap2) by eauto.
    assert (value v) by eauto.
    assert (subset eff1 (phi_fld_eff p1)). eauto.
    assert (subset eff2 (phi_fld_eff p2)). eauto.
    inversion Cf1. subst p1 p2 p3.
    inversion Cf2. subst p' rst4 teff3 fst3 rst0 teff0 fst4.
    inversion PS. subst p rst3 teff0 fst3.
    clear Cf1 Cf2 PS. simpl in *.
    assert (rst1 = (rst2 `U` (singl l)) `U` eff2).
      eauto using propagate_rst_back.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    subst fst1 fst2 rst1 rst.
    destruct (typing_loc_inv phi_0 nil P1 r l (typ_ref teff t') Tr)
      as [ _ [ _ [ t'' [ Sub' B' ]]]].
    inversion Sub'. subst. clear Sub'.
    assert (t'' = t'). eauto. subst.
    split; auto. 
    split; eauto 4 using subset_trans, subset_add.
  Case "let_in1".
    assert (heap_ok P1 heap1). eauto using consistent_states.
    assert (heap_ok P2 heap2). eauto using consistent_states.
    assert (value v1) by eauto.
    assert (value v2) by eauto.
    assert (subset eff1 (phi_fld_eff p1)). eauto.
    assert (subset eff2 (phi_fld_eff p2)). eauto.
    inversion Cf.
    inversion PS. subst.
    inversion H11. subst. simpl in *.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    subst.
    split. assumption.
    split; eauto 4 using subset_trans, subset_add.
  Case "let_in2".
    assert (heap_ok P1 heap1). eauto using consistent_states.
    assert (heap_ok P2 heap2). eauto using consistent_states.
    assert (value v1) by eauto.
    assert (value v2) by eauto.
    assert (subset eff1 (phi_fld_eff p1)). eauto.
    assert (subset eff2 (phi_fld_eff p2)). eauto.
    inversion Cf.
    inversion PS. subst.
    inversion H11. subst. simpl in *.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    subst.
    split. assumption.
    split; eauto 3 using subset_trans, subset_add.
  Case "if-t1".
    assert (heap_ok P1 heap1) by eauto.
    assert (heap_ok P2 heap2) by eauto.
    assert (value (e_nat 0)) by eauto.
    assert (value v) by eauto.
    assert (subset eff1 (phi_fld_eff p1)). eauto.
    assert (subset eff2 (phi_fld_eff p2)). eauto.
    inversion Cf.
    inversion PS. subst.
    inversion H11. subst. simpl in *.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    subst.
    split. assumption.
    split; eauto 3 using subset_trans, subset_add.
  Case "if-t2".
    assert (heap_ok P1 heap1). eauto.
    assert (heap_ok P2 heap2). eauto.
    assert (value (e_nat 0)). eauto.
    assert (value v). eauto.
    assert (subset eff1 (phi_fld_eff p1)). eauto.
    assert (subset eff2 (phi_fld_eff p2)). eauto.
    inversion Cf.
    inversion PS. subst.
    inversion H11. subst. simpl in *.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    subst.
    split. assumption. clear E1 E2 T T1 T2 T3.
    split; eauto 3 using subset_trans, subset_add.
  Case "if-f1".
    assert (heap_ok P1 heap1). eauto.
    assert (heap_ok P2 heap2). eauto.
    assert (value (e_nat 0)). eauto.
    assert (value v). eauto.
    assert (subset eff1 (phi_fld_eff p1)). eauto.
    assert (subset eff2 (phi_fld_eff p2)). eauto.
    inversion Cf.
    inversion PS. subst.
    inversion H11. subst. simpl in *.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    subst.
    split. assumption. clear E1 E2 T T1 T2 T3.
    split; eauto 3 using subset_trans, subset_add.
  Case "if-f2".
    assert (heap_ok P1 heap1). eauto.
    assert (heap_ok P2 heap2). eauto.
    assert (value (e_nat 0)). eauto.
    assert (value v). eauto.
    assert (subset eff1 (phi_fld_eff p1)). eauto.
    assert (subset eff2 (phi_fld_eff p2)). eauto.
    inversion Cf.
    inversion PS. subst.
    inversion H11. subst. simpl in *.
    assert (rst = rst1 `U` eff1). eauto using propagate_rst_back.
    assert (rst1 = rst2 `U` eff2). eauto using propagate_rst_back.
    assert (fst1 = fst `U` eff1). eauto using propagate_fst_forward.
    assert (fst2 = fst1 `U` eff2). eauto using propagate_fst_forward.
    subst.
    split. assumption. clear E1 E2 T T1 T2 T3.
    split; eauto 3 using subset_trans, subset_add.
  Case "transitive".
    destruct IHSubD2 as [H2ok [ S1 S2 ]]; auto.
Qed.