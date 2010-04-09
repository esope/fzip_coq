Add LoadPath "../metatheory".
Require Import FzipCore_init.

(** Lemmas about [zip] *)
Lemma zip_lc1 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → lc_env Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; auto with lngen.
Qed.

Lemma zip_lc2 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → lc_env Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; auto with lngen.
Qed.

Lemma zip_lc3 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → lc_env Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; auto with lngen.
Qed.
Hint Resolve zip_lc1 zip_lc2 zip_lc3: lngen.

Lemma zip_dom1 :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  dom Γ₁ [<=] dom Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; simpl in *; fsetdec.
Qed.

Lemma zip_dom2 :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  dom Γ₂ [=] dom Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; simpl in *; fsetdec.
Qed.

Lemma zip_dom3 :
  forall Γ₁ Γ₂ Γ₃, zip Γ₁ Γ₂ Γ₃ ->
  dom Γ₁ [<=] dom Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ H. rewrite (zip_dom2 Γ₁ Γ₂ Γ₃); auto. eapply zip_dom1; eauto.
Qed.
Hint Resolve zip_dom1 zip_dom2 zip_dom3: fzip.

Lemma zip_uniq1 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → uniq Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; auto.
Qed.

Lemma zip_uniq2 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → uniq Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; auto.
Qed.

Lemma zip_uniq3 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → uniq Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H; auto.
assert (x ∉ dom G). erewrite <- zip_dom2; eauto. auto.
assert (a ∉ dom G). erewrite <- zip_dom2; eauto. auto.
assert (a ∉ dom G). erewrite <- zip_dom2; eauto. auto.
assert (a ∉ dom G). erewrite <- zip_dom2; eauto. auto.
assert (a ∉ dom G). erewrite <- zip_dom2; eauto. auto.
Qed.
Hint Resolve zip_uniq1 zip_uniq2 zip_uniq3: lngen.

Lemma zip_binds_T12 :
  forall Γ₁ Γ₂ Γ₃ x τ, zip Γ₁ Γ₂ Γ₃ →
    binds x (T τ) Γ₁ → binds x (T τ) Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ x τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_T13 :
  forall Γ₁ Γ₂ Γ₃ x τ, zip Γ₁ Γ₂ Γ₃ →
    binds x (T τ) Γ₁ → binds x (T τ) Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ x τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_T23 :
  forall Γ₁ Γ₂ Γ₃ x τ, zip Γ₁ Γ₂ Γ₃ →
    binds x (T τ) Γ₂ → binds x (T τ) Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ x τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_T31 :
  forall Γ₁ Γ₂ Γ₃ x τ, zip Γ₁ Γ₂ Γ₃ →
    binds x (T τ) Γ₃ → binds x (T τ) Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₃ x τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.
Hint Resolve zip_binds_T12 zip_binds_T13 zip_binds_T23 zip_binds_T31: fzip.

Lemma zip_binds_Eq12 :
  forall Γ₁ Γ₂ Γ₃ a τ, zip Γ₁ Γ₂ Γ₃ →
    binds a (Eq τ) Γ₁ → binds a (Eq τ) Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_Eq13 :
  forall Γ₁ Γ₂ Γ₃ a τ, zip Γ₁ Γ₂ Γ₃ →
    binds a (Eq τ) Γ₁ → binds a (Eq τ) Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_Eq23 :
  forall Γ₁ Γ₂ Γ₃ a τ, zip Γ₁ Γ₂ Γ₃ →
    binds a (Eq τ) Γ₂ → binds a (Eq τ) Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_Eq31 :
  forall Γ₁ Γ₂ Γ₃ a τ, zip Γ₁ Γ₂ Γ₃ →
    binds a (Eq τ) Γ₃ → binds a (Eq τ) Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_Eq32 :
  forall Γ₁ Γ₂ Γ₃ a τ, zip Γ₁ Γ₂ Γ₃ →
    binds a (Eq τ) Γ₃ → binds a (Eq τ) Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ a τ H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.
Hint Resolve zip_binds_Eq12 zip_binds_Eq13 zip_binds_Eq23 zip_binds_Eq31 zip_binds_Eq32: fzip.

Lemma zip_binds_E12 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a E Γ₁ → binds a U Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_E13 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a E Γ₁ → binds a E Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_E23 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a E Γ₂ → binds a E Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_E3_inv :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a E Γ₃ →
    (binds a E Γ₁ ∧ binds a U Γ₂) ∨ (a ∉ dom Γ₁ ∧ binds a E Γ₂).
Proof.
intros Γ₁ Γ₂ Γ₃ a H H1. dependent induction H; auto.
Case "TT".
assert (uniq (x ~ T t ++ G)). erewrite zip_dom2 in H2; eauto. eauto with lngen.
destruct IHzip.
analyze_binds_uniq H1.
destruct H5; auto.
analyze_binds_uniq H1. destruct H5; auto.
Case "UU".
assert (uniq (a0 ~ U ++ G)). erewrite zip_dom2 in H0; eauto. eauto with lngen.
destruct IHzip.
analyze_binds_uniq H1.
destruct H4; auto.
analyze_binds_uniq H1. destruct H4; auto.
Case "EU".
assert (uniq (a0 ~ E ++ G)). erewrite zip_dom2 in H0; eauto. eauto with lngen.
destruct (a == a0); subst; auto.
destruct IHzip.
analyze_binds_uniq H1.
destruct H4; auto.
analyze_binds_uniq H1. destruct H4; auto.
Case "E".
assert (uniq (a0 ~ E ++ G)). erewrite zip_dom2 in H0; eauto. eauto with lngen.
destruct (a == a0); subst; auto.
destruct IHzip.
analyze_binds_uniq H1.
destruct H4; auto.
analyze_binds_uniq H1. destruct H4; auto.
Case "Eq".
assert (uniq (a0 ~ Eq t ++ G)). erewrite zip_dom2 in H2; eauto. eauto with lngen.
destruct IHzip.
analyze_binds_uniq H1.
destruct H5; auto.
analyze_binds_uniq H1. destruct H5; auto.
Qed.
Hint Resolve zip_binds_E12 zip_binds_E13 zip_binds_E23 zip_binds_E3_inv: fzip.

Lemma zip_binds_U12 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a U Γ₁ → binds a U Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0; intuition].
Qed.

Lemma zip_binds_U13 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a U Γ₁ → binds a U Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0].
Qed.

Lemma zip_binds_U23 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a U Γ₂ → binds a U Γ₃ ∨ binds a E Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0; intuition].
Qed.

Lemma zip_binds_U31 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a U Γ₃ → binds a U Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0; intuition].
Qed.

Lemma zip_binds_U32 :
  forall Γ₁ Γ₂ Γ₃ a, zip Γ₁ Γ₂ Γ₃ →
    binds a U Γ₃ → binds a U Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₃ a H H0. dependent induction H; auto; try solve [analyze_binds H0; intuition].
Qed.
Hint Resolve zip_binds_U12 zip_binds_U13 zip_binds_U23 zip_binds_U31 zip_binds_U32: fzip.

Ltac my_auto := try solve [ auto | auto with fzip | auto with lngen | solve_uniq].

Lemma zip_app : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃',
  disjoint Γ₁ Γ₁' → disjoint Γ₂ Γ₂' → disjoint Γ₃ Γ₃' →
  zip Γ₁ Γ₂ Γ₃ → zip Γ₁' Γ₂' Γ₃' →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' H H0 H1 H2 H3.
generalize dependent Γ₃'.
generalize dependent Γ₂'.
generalize dependent Γ₁'.
induction H2; intros; simpl_env in *; auto; constructor; my_auto.
Case "E". simpl_env. assert (dom Γ₁' [<=] dom Γ₃') by eauto with fzip. my_auto.
Qed.

Lemma zip_unique : forall Γ₁ Γ₂ Γ₃ Γ₄,
  zip Γ₁ Γ₂ Γ₃ → zip Γ₁ Γ₂ Γ₄ → Γ₃ = Γ₄.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₄ H H0.
generalize dependent Γ₄. induction H; intros Γ₄ H3; inversion H3; subst;
f_equal; auto.
Qed.

Lemma zip_nil : forall Γ Γ',
  zip nil Γ Γ' → Γ = Γ'.
Proof.
intros Γ Γ' H. dependent induction H; auto.
rewrite IHzip; auto.
Qed.

Lemma zip_T : forall x τ, lc_typ τ → zip (x ~ T τ) (x ~ T τ) (x ~ T τ).
Proof.
intros x τ. rewrite_env (x ~ T τ ++ nil). auto.
Qed.

Lemma zip_Eq : forall a τ, lc_typ τ → zip (a ~ Eq τ) (a ~ Eq τ) (a ~ Eq τ).
Proof.
intros a τ. rewrite_env (a ~ Eq τ ++ nil). auto.
Qed.

Lemma zip_U : forall a, zip (a ~ U) (a ~ U) (a ~ U).
Proof.
intros a. rewrite_env (a ~ (@U typ) ++ nil). auto.
Qed.

Lemma zip_EU : forall a, zip (a ~ E) (a ~ U) (a ~ E).
Proof.
intros a. rewrite_env (a ~ (@U typ) ++ nil). rewrite_env (a ~ (@E typ) ++ nil).  auto.
Qed.

Lemma zip_E : forall a, zip nil (a ~ E) (a ~ E).
Proof.
intros a. rewrite_env (a ~ (@E typ) ++ nil).  auto.
Qed.
Hint Resolve zip_T zip_Eq zip_U zip_EU zip_E: fzip.


Lemma zip_ftv_env1 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → ftv_env Γ₁ [=] ftv_env Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H.
rewrite ftv_env_nil. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
Qed.

Lemma zip_ftv_env2 : forall Γ₁ Γ₂ Γ₃,
  zip Γ₁ Γ₂ Γ₃ → ftv_env Γ₂ [=] ftv_env Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H. induction H.
rewrite ftv_env_nil. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
repeat rewrite ftv_env_app. fsetdec.
Qed.

Lemma zip_app_inv : forall Γ₁ Γ₂ Γ₃' Γ₃'',
  zip Γ₁ Γ₂ (Γ₃' ++ Γ₃'') →
  exists Γ₁', exists Γ₁'', exists Γ₂', exists Γ₂'',
    Γ₁ = Γ₁' ++ Γ₁'' ∧ Γ₂ = Γ₂' ++ Γ₂'' ∧
    zip Γ₁' Γ₂' Γ₃' ∧ zip Γ₁'' Γ₂'' Γ₃''.
Proof.
intros Γ₁ Γ₂ Γ₃' Γ₃'' H.
dependent induction H; intros.
Case "nil".
exists nil; exists nil; exists nil; exists nil.
destruct Γ₃'; auto; try solve [inversion H].
simpl in H; subst.
intuition auto.
Case "TT".
destruct Γ₃'; simpl_env in *. 
exists nil; exists (x ~ T t ++ G1); exists nil; exists (x ~ T t ++ G2).
subst. intuition auto.
inversion H3; subst.
destruct (IHzip Γ₃' Γ₃'') as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
exists (x ~ T t ++ x0); exists x1; exists (x ~ T t ++ x2); exists x3.
intuition auto.
Case "UU".
destruct Γ₃'; simpl_env in *. 
exists nil; exists (a ~ U ++ G1); exists nil; exists (a ~ U ++ G2).
subst. intuition auto.
inversion H2; subst.
destruct (IHzip Γ₃' Γ₃'') as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
exists (a ~ U ++ x); exists x0; exists (a ~ U ++ x1); exists x2.
intuition auto.
Case "EU".
destruct Γ₃'; simpl_env in *. 
exists nil; exists (a ~ E ++ G1); exists nil; exists (a ~ U ++ G2).
subst. intuition auto.
inversion H2; subst.
destruct (IHzip Γ₃' Γ₃'') as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
exists (a ~ E ++ x); exists x0; exists (a ~ U ++ x1); exists x2.
intuition auto.
Case "E".
destruct Γ₃'; simpl_env in *. 
exists nil; exists G1; exists nil; exists (a ~ E ++ G2).
subst. intuition auto.
inversion H2; subst.
destruct (IHzip Γ₃' Γ₃'') as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
exists x; exists x0; exists (a ~ E ++ x1) ; exists x2.
intuition auto.
Case "EqEq".
destruct Γ₃'; simpl_env in *. 
exists nil; exists (a ~ Eq t ++ G1); exists nil; exists (a ~ Eq t ++ G2).
subst. intuition auto.
inversion H3; subst.
destruct (IHzip Γ₃' Γ₃'') as [? [? [? [? [? [? [? ?]]]]]]]; auto; subst.
exists (a ~ Eq t ++ x); exists x0; exists (a ~ Eq t ++ x1); exists x2.
intuition auto.
Qed.

Lemma zip_app_weakening_strong : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'',
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃') →
  zip Γ₁ Γ₂ Γ₃ →
  zip Γ₁' Γ₂' Γ₃' →
  zip Γ₁'' Γ₂'' Γ₃'' →
  disjoint Γ₁'' (Γ₁ ++ Γ₁') →
  disjoint Γ₂'' (Γ₂ ++ Γ₂') →
  disjoint Γ₃'' (Γ₃ ++ Γ₃') →
  zip (Γ₁ ++ Γ₁'' ++ Γ₁') (Γ₂ ++ Γ₂'' ++ Γ₂') (Γ₃ ++ Γ₃'' ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' H H0 H1 H2 H3 H4 H5.
assert (uniq (Γ₁ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ Γ₃')) by eauto with lngen.
generalize dependent Γ₃''.
generalize dependent Γ₂''.
generalize dependent Γ₁''.
generalize dependent Γ₃'.
generalize dependent Γ₂'.
generalize dependent Γ₁'.
induction H0; intros; simpl_env in *.
Case "nil". apply zip_app; auto.
Case "TT". constructor; simpl_env; my_auto.
apply IHzip; my_auto. apply zip_app; my_auto.
Case "UU". constructor; simpl_env; my_auto.
apply IHzip; my_auto. apply zip_app; my_auto.
Case "EU". constructor; simpl_env; my_auto.
apply IHzip; my_auto. apply zip_app; my_auto.
Case "E".
assert (dom G1 [<=] dom G) by eauto with fzip.
assert (dom Γ₁' [<=] dom Γ₃') by eauto with fzip.
assert (dom Γ₁'' [<=] dom Γ₃'') by eauto with fzip.
constructor; simpl_env; my_auto.
apply IHzip; my_auto. apply zip_app; my_auto.
Case "Eq". constructor; simpl_env; my_auto.
apply IHzip; my_auto. apply zip_app; my_auto.
Qed.

Lemma zip_remove_U : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a,
  zip (Γ₁ ++ a ~ U ++ Γ₁') (Γ₂ ++ a ~ U ++ Γ₂') (Γ₃ ++ a ~ U ++ Γ₃') →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a H.
assert (uniq (Γ₁ ++ a ~ U ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ U ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ U ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
apply zip_app; my_auto.
Qed.

Lemma zip_remove_EU : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a,
  zip (Γ₁ ++ a ~ E ++ Γ₁') (Γ₂ ++ a ~ U ++ Γ₂') (Γ₃ ++ a ~ E ++ Γ₃') →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a H.
assert (uniq (Γ₁ ++ a ~ E ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ U ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ E ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
Case "EU".
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
apply zip_app; my_auto.
Case "E".
assert (@U typ = E).
apply binds_unique with (x := a) (E := Γ₂ ++ [(a, U)] ++ Γ₂'); auto.
rewrite H4; auto.
congruence.
Qed.

Lemma zip_remove_E : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a,
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ a ~ E ++ Γ₂') (Γ₃ ++ a ~ E ++ Γ₃') →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a H.
assert (uniq (Γ₁ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ E ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ E ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
Case "EU".
assert (@E typ = U).
apply binds_unique with (x := a) (E := Γ₂ ++ [(a, E)] ++ Γ₂'); auto.
rewrite H4; auto.
congruence.
Case "E".
apply uniq_app_inv in H4; my_auto.
destruct H4; subst. rewrite H3 in *.
apply zip_app; my_auto.
Qed.

Lemma zip_remove_Eq : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ,
  zip (Γ₁ ++ a ~ Eq τ ++ Γ₁') (Γ₂ ++ a ~ Eq τ ++ Γ₂') (Γ₃ ++ a ~ Eq τ ++ Γ₃') →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ H.
assert (uniq (Γ₁ ++ a ~ Eq τ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ Eq τ ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ Eq τ ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
apply zip_app; my_auto.
Qed.

Lemma zip_subst : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' x τ,
  zip (Γ₁ ++ x ~ T τ ++ Γ₁') (Γ₂ ++ x ~ T τ ++ Γ₂') (Γ₃ ++ x ~ T τ ++ Γ₃') →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' x τ H.
assert (uniq (Γ₁ ++ [(x, T τ)] ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ [(x, T τ)] ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ [(x, T τ)] ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
apply zip_app; my_auto.
Qed.

Lemma zip_stable_tsubst : forall Γ₁ Γ₂ Γ₃ a τ,
  lc_typ τ →
   zip Γ₁ Γ₂ Γ₃ →
   zip (env_map (tsubst_typ τ a) Γ₁)
       (env_map (tsubst_typ τ a) Γ₂)
       (env_map (tsubst_typ τ a) Γ₃).
Proof.
intros Γ₁ Γ₂ Γ₃ a τ Hlc H. induction H; simpl; simpl_env; auto;
constructor; solve [auto with lngen | unfold env_map; auto with lngen].
Qed.

Lemma zip_instantiate : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ,
  lc_typ τ →
  zip (Γ₁ ++ a ~ U ++ Γ₁') (Γ₂ ++ a ~ U ++ Γ₂') (Γ₃ ++ a ~ U ++ Γ₃') →
  zip (Γ₁ ++ a ~ Eq τ ++ Γ₁') (Γ₂ ++ a ~ Eq τ ++ Γ₂') (Γ₃ ++ a ~ Eq τ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ Hlc H.
assert (uniq (Γ₁ ++ a ~ U ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ U ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ U ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
apply zip_app; my_auto.
Qed.

Lemma zip_subst_eq : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ,
  zip (Γ₁ ++ a ~ Eq τ ++ Γ₁') (Γ₂ ++ a ~ Eq τ ++ Γ₂') (Γ₃ ++ a ~ Eq τ ++ Γ₃') →
  zip (env_map (tsubst_typ τ a) Γ₁ ++ Γ₁')
      (env_map (tsubst_typ τ a) Γ₂ ++ Γ₂')
      (env_map (tsubst_typ τ a) Γ₃ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ H.
assert (uniq (Γ₁ ++ a ~ Eq τ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ Eq τ ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ Eq τ ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
apply zip_app; auto using zip_stable_tsubst;
  unfold env_map; solve_uniq.
Qed.

Lemma zip_tsubst : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ,
  lc_typ τ →
  zip (Γ₁ ++ a ~ U ++ Γ₁') (Γ₂ ++ a ~ U ++ Γ₂') (Γ₃ ++ a ~ U ++ Γ₃') →
  zip (env_map (tsubst_typ τ a) Γ₁ ++ Γ₁')
      (env_map (tsubst_typ τ a) Γ₂ ++ Γ₂')
      (env_map (tsubst_typ τ a) Γ₃ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ Hlc H.
auto using zip_subst_eq, zip_instantiate.
Qed.

Lemma zip_app_T_inv : forall Γ₁ Γ₂ Γ₃' x τ Γ₃'',
  zip Γ₁ Γ₂ (Γ₃' ++ x ~ T τ ++ Γ₃'') →
  exists Γ₁', exists Γ₁'', exists Γ₂', exists Γ₂'',
    Γ₁ = Γ₁' ++ x ~ T τ ++ Γ₁'' ∧ Γ₂ = Γ₂' ++ x ~ T τ ++ Γ₂''.
Proof.
intros Γ₁ Γ₂ Γ₃' x τ Γ₃'' H.
dependent induction H.
Case "nil". destruct Γ₃'; inversion H.
Case "T". destruct Γ₃'; inversion H3; subst.
exists nil; exists G1; exists nil; exists G2; split; auto.
destruct (IHzip Γ₃' x0 τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (x ~ T t ++ x1); exists x2; exists (x ~ T t ++ x3); exists x4; split; auto.
Case "U". destruct Γ₃'; inversion H2; subst.
destruct (IHzip Γ₃' x τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ U ++ x0); exists x1; exists (a ~ U ++ x2); exists x3; split; auto.
Case "EU". destruct Γ₃'; inversion H2; subst.
destruct (IHzip Γ₃' x τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ E ++ x0); exists x1; exists (a ~ U ++ x2); exists x3; split; auto.
Case "E". destruct Γ₃'; inversion H2; subst.
destruct (IHzip Γ₃' x τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists x0; exists x1; exists (a ~ E ++ x2); exists x3; split; auto.
Case "Eq". destruct Γ₃'; inversion H3; subst.
destruct (IHzip Γ₃' x τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ Eq t ++ x0); exists x1; exists (a ~ Eq t ++ x2); exists x3; split; auto.
Qed.

Lemma zip_app_Eq_inv : forall Γ₁ Γ₂ Γ₃' a τ Γ₃'',
  zip Γ₁ Γ₂ (Γ₃' ++ a ~ Eq τ ++ Γ₃'') →
  exists Γ₁', exists Γ₁'', exists Γ₂', exists Γ₂'',
    Γ₁ = Γ₁' ++ a ~ Eq τ ++ Γ₁'' ∧ Γ₂ = Γ₂' ++ a ~ Eq τ ++ Γ₂''.
Proof.
intros Γ₁ Γ₂ Γ₃' a τ Γ₃'' H.
dependent induction H.
Case "nil". destruct Γ₃'; inversion H.
Case "T". destruct Γ₃'; inversion H3; subst.
destruct (IHzip Γ₃' a τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (x ~ T t ++ x0); exists x1; exists (x ~ T t ++ x2); exists x3; split; auto.
Case "U". destruct Γ₃'; inversion H2; subst.
destruct (IHzip Γ₃' a0 τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ U ++ x); exists x0; exists (a ~ U ++ x1); exists x2; split; auto.
Case "EU". destruct Γ₃'; inversion H2; subst.
destruct (IHzip Γ₃' a0 τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ E ++ x); exists x0; exists (a ~ U ++ x1); exists x2; split; auto.
Case "E". destruct Γ₃'; inversion H2; subst.
destruct (IHzip Γ₃' a0 τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists x; exists x0; exists (a ~ E ++ x1); exists x2; split; auto.
Case "Eq". destruct Γ₃'; inversion H3; subst.
exists nil; exists G1; exists nil; exists G2; split; auto.
destruct (IHzip Γ₃' a0 τ Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ Eq t ++ x); exists x0; exists (a ~ Eq t ++ x1); exists x2; split; auto.
Qed.

Lemma zip_app_U_inv : forall Γ₁ Γ₂ Γ₃' a Γ₃'',
  zip Γ₁ Γ₂ (Γ₃' ++ a ~ U ++ Γ₃'') →
  exists Γ₁', exists Γ₁'', exists Γ₂', exists Γ₂'',
    Γ₁ = Γ₁' ++ a ~ U ++ Γ₁'' ∧ Γ₂ = Γ₂' ++ a ~ U ++ Γ₂''.
Proof.
intros Γ₁ Γ₂ Γ₃' a Γ₃'' H.
dependent induction H.
Case "nil". destruct Γ₃'; inversion H.
Case "T". destruct Γ₃'; inversion H3; subst.
destruct (IHzip Γ₃' a Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (x ~ T t ++ x0); exists x1; exists (x ~ T t ++ x2); exists x3; split; auto.
Case "U". destruct Γ₃'; inversion H2; subst.
exists nil; exists G1; exists nil; exists G2; auto.
destruct (IHzip Γ₃' a0 Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ U ++ x); exists x0; exists (a ~ U ++ x1); exists x2; split; auto.
Case "EU". destruct Γ₃'; inversion H2; subst.
destruct (IHzip Γ₃' a0 Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ E ++ x); exists x0; exists (a ~ U ++ x1); exists x2; split; auto.
Case "E". destruct Γ₃'; inversion H2; subst.
destruct (IHzip Γ₃' a0 Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists x; exists x0; exists (a ~ E ++ x1); exists x2; split; auto.
Case "Eq". destruct Γ₃'; inversion H3; subst.
destruct (IHzip Γ₃' a0 Γ₃'') as [? [? [? [? [? ?]]]]]. simpl_env; auto.
subst. exists (a ~ Eq t ++ x); exists x0; exists (a ~ Eq t ++ x1); exists x2; split; auto.
Qed.

Lemma zip_renameU : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a b,
  b ∉ dom (Γ₁ ++ Γ₁') ∪ dom (Γ₂ ++ Γ₂') ∪ dom (Γ₃ ++ Γ₃') →
  zip (Γ₁ ++ a ~ U ++ Γ₁') (Γ₂ ++ a ~ U ++ Γ₂') (Γ₃ ++ a ~ U ++ Γ₃') →
  zip (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ U ++ Γ₁')
      (env_map (tsubst_typ (typ_var_f b) a) Γ₂ ++ b ~ U ++ Γ₂')
      (env_map (tsubst_typ (typ_var_f b) a) Γ₃ ++ b ~ U ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a b Hb H.
assert (uniq (Γ₁ ++ [(a, U)] ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ [(a, U)] ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ [(a, U)] ++ Γ₃')) by eauto with lngen.
simpl_env in *.
apply zip_app_inv in H. decompose record H; clear H; simpl_env in *.
inversion H7; subst.
apply uniq_app_inv in H3; auto.
apply uniq_app_inv in H4; auto.
destruct H3; destruct H4; subst; auto.
apply zip_app; auto.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) x ++ nil).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) x1 ++ nil).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) Γ₃ ++ nil).
apply zip_tsubst; auto.
simpl_env. apply zip_app; my_auto.
Qed.

Lemma zip_renameEU : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a b,
  b ∉ dom (Γ₁ ++ Γ₁') ∪ dom (Γ₂ ++ Γ₂') ∪ dom (Γ₃ ++ Γ₃') →
  zip (Γ₁ ++ a ~ E ++ Γ₁') (Γ₂ ++ a ~ U ++ Γ₂') (Γ₃ ++ a ~ E ++ Γ₃') →
  zip (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ E ++ Γ₁')
      (env_map (tsubst_typ (typ_var_f b) a) Γ₂ ++ b ~ U ++ Γ₂')
      (env_map (tsubst_typ (typ_var_f b) a) Γ₃ ++ b ~ E ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a b Hb H.
assert (uniq (Γ₁ ++ [(a, E)] ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ [(a, U)] ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ [(a, E)] ++ Γ₃')) by eauto with lngen.
simpl_env in *.
apply zip_app_inv in H. decompose record H; clear H; simpl_env in *.
inversion H7; subst.
SCase "EU".
apply uniq_app_inv in H3; auto.
apply uniq_app_inv in H4; auto.
destruct H3; destruct H4; subst; auto.
apply zip_app; auto.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) x ++ nil).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) x1 ++ nil).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) Γ₃ ++ nil).
apply zip_tsubst; auto.
simpl_env. apply zip_app; my_auto.
SCase "E (absurd)".
assert (@U typ = @E typ). apply binds_unique with (x := a) (E := Γ₂ ++ [(a, U)] ++ Γ₂'); auto.
  rewrite H4; auto.
congruence.
Qed.

Lemma zip_renameE : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a b,
  b ∉ dom (Γ₁ ++ Γ₁') ∪ dom (Γ₂ ++ Γ₂') ∪ dom (Γ₃ ++ Γ₃') →
  zip Γ₁ Γ₂ Γ₃ → zip Γ₁' Γ₂' Γ₃' →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ a ~ E ++ Γ₂') (Γ₃ ++ a ~ E ++ Γ₃') →
  zip (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ Γ₁')
      (env_map (tsubst_typ (typ_var_f b) a) Γ₂ ++ b ~ E ++ Γ₂')
      (env_map (tsubst_typ (typ_var_f b) a) Γ₃ ++ b ~ E ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a b Hb Hzip1 Hzip2 H.
assert (uniq (Γ₁ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ [(a, E)] ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ [(a, E)] ++ Γ₃')) by eauto with lngen.
simpl_env in *.
apply zip_app; auto.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ nil).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) Γ₂ ++ nil).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) Γ₃ ++ nil).
apply zip_tsubst; auto.
simpl_env. apply zip_app.
  assert (dom Γ₁ [<=] dom Γ₃) by eauto with fzip. destruct_uniq; fsetdec.
  assert (dom Γ₂ [=] dom Γ₃) by eauto with fzip. destruct_uniq; fsetdec.
  solve_uniq.
  auto.
  my_auto.
Qed.

Lemma zip_renameEq : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a b τ,
  b ∉ dom (Γ₁ ++ Γ₁') ∪ dom (Γ₂ ++ Γ₂') ∪ dom (Γ₃ ++ Γ₃') →
  zip (Γ₁ ++ a ~ Eq τ ++ Γ₁') (Γ₂ ++ a ~ Eq τ ++ Γ₂') (Γ₃ ++ a ~ Eq τ ++ Γ₃') →
  zip (env_map (tsubst_typ (typ_var_f b) a) Γ₁ ++ b ~ Eq τ ++ Γ₁')
      (env_map (tsubst_typ (typ_var_f b) a) Γ₂ ++ b ~ Eq τ ++ Γ₂')
      (env_map (tsubst_typ (typ_var_f b) a) Γ₃ ++ b ~ Eq τ ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a b τ Hb H.
assert (uniq (Γ₁ ++ [(a, Eq τ)] ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ [(a, Eq τ)] ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ [(a, Eq τ)] ++ Γ₃')) by eauto with lngen.
simpl_env in *.
apply zip_app_inv in H. decompose record H; clear H; simpl_env in *.
inversion H7; subst.
apply uniq_app_inv in H3; auto.
apply uniq_app_inv in H4; auto.
destruct H3; destruct H4; subst; auto.
apply zip_app; auto.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
  unfold env_map. solve_uniq.
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) x ++ nil).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) x1 ++ nil).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) Γ₃ ++ nil).
apply zip_tsubst; auto.
simpl_env. apply zip_app; my_auto.
Qed.

Lemma zip_remove_T1 : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' x τ,
  zip (Γ₁ ++ x ~ T τ ++ Γ₁') (Γ₂ ++ x ~ T τ ++ Γ₂') (Γ₃ ++ x ~ T τ ++ Γ₃') →
  zip Γ₁ Γ₂ Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' x τ H.
assert (uniq (Γ₁ ++ x ~ T τ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ x ~ T τ ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ x ~ T τ ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
auto.
Qed.

Lemma zip_remove_T2 : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' x τ,
  zip (Γ₁ ++ x ~ T τ ++ Γ₁') (Γ₂ ++ x ~ T τ ++ Γ₂') (Γ₃ ++ x ~ T τ ++ Γ₃') →
  zip Γ₁' Γ₂' Γ₃'.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' x τ H.
assert (uniq (Γ₁ ++ x ~ T τ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ x ~ T τ ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ x ~ T τ ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
auto.
Qed.

Lemma zip_remove_U1 : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a,
  zip (Γ₁ ++ a ~ U ++ Γ₁') (Γ₂ ++ a ~ U ++ Γ₂') (Γ₃ ++ a ~ U ++ Γ₃') →
  zip Γ₁ Γ₂ Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a H.
assert (uniq (Γ₁ ++ a ~ U ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ U ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ U ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
auto.
Qed.

Lemma zip_remove_U2 : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a,
  zip (Γ₁ ++ a ~ U ++ Γ₁') (Γ₂ ++ a ~ U ++ Γ₂') (Γ₃ ++ a ~ U ++ Γ₃') →
  zip Γ₁' Γ₂' Γ₃'.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a H.
assert (uniq (Γ₁ ++ a ~ U ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ U ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ U ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
auto.
Qed.

Lemma zip_remove_Eq1 : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ,
  zip (Γ₁ ++ a ~ Eq τ ++ Γ₁') (Γ₂ ++ a ~ Eq τ ++ Γ₂') (Γ₃ ++ a ~ Eq τ ++ Γ₃') →
  zip Γ₁ Γ₂ Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ H.
assert (uniq (Γ₁ ++ a ~ Eq τ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ Eq τ ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ Eq τ ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
auto.
Qed.

Lemma zip_remove_Eq2 : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ,
  zip (Γ₁ ++ a ~ Eq τ ++ Γ₁') (Γ₂ ++ a ~ Eq τ ++ Γ₂') (Γ₃ ++ a ~ Eq τ ++ Γ₃') →
  zip Γ₁' Γ₂' Γ₃'.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ H.
assert (uniq (Γ₁ ++ a ~ Eq τ ++ Γ₁')) by eauto with lngen.
assert (uniq (Γ₂ ++ a ~ Eq τ ++ Γ₂')) by eauto with lngen.
assert (uniq (Γ₃ ++ a ~ Eq τ ++ Γ₃')) by eauto with lngen.
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; my_auto.
apply uniq_app_inv in H3; my_auto.
destruct H4; destruct H3; subst.
auto.
Qed.

Lemma zip_app_inv_strong : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'',
  zip Γ₁ Γ₂ Γ₃ →
  zip (Γ₁' ++ Γ₁ ++ Γ₁'') (Γ₂' ++ Γ₂ ++ Γ₂'') (Γ₃' ++ Γ₃ ++ Γ₃'') →
  zip (Γ₁' ++ Γ₁'') (Γ₂' ++ Γ₂'') (Γ₃' ++ Γ₃'').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' H H0.
induction H; simpl_env in *; auto; apply IHzip.
eauto using zip_subst.
eauto using zip_remove_U.
eauto using zip_remove_EU.
eauto using zip_remove_E.
eauto using zip_remove_Eq.
Qed.

Lemma zip_app_inv1 : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃',
  zip Γ₁ Γ₂ Γ₃ →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃') →
  zip Γ₁' Γ₂' Γ₃'.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' H H0.
rewrite_env (nil ++ Γ₁ ++ Γ₁') in H0.
rewrite_env (nil ++ Γ₂ ++ Γ₂') in H0. 
rewrite_env (nil ++ Γ₃ ++ Γ₃') in H0. 
apply zip_app_inv_strong in H0; auto.
Qed.

Lemma zip_app_inv2 : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃',
  zip Γ₁' Γ₂' Γ₃' →
  zip (Γ₁ ++ Γ₁') (Γ₂ ++ Γ₂') (Γ₃ ++ Γ₃') →
  zip Γ₁ Γ₂ Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' H H0.
rewrite_env (Γ₁ ++ Γ₁' ++ nil) in H0. 
rewrite_env (Γ₂ ++ Γ₂' ++ nil) in H0. 
rewrite_env (Γ₃ ++ Γ₃' ++ nil) in H0.
apply zip_app_inv_strong in H0; auto.
simpl_env in H0; auto.
Qed.

Lemma zip_upperU : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a,
  zip (Γ₁ ++ a ~ U ++ Γ₁' ++ Γ₁'')
      (Γ₂ ++ a ~ U ++ Γ₂' ++ Γ₂'')
      (Γ₃ ++ a ~ U ++ Γ₃' ++ Γ₃'') →
  zip Γ₁' Γ₂' Γ₃' →
  zip Γ₁'' Γ₂'' Γ₃'' →
  zip (Γ₁ ++ Γ₁' ++ a ~ U ++ Γ₁'')
      (Γ₂ ++ Γ₂' ++ a ~ U ++ Γ₂'')
      (Γ₃ ++ Γ₃' ++ a ~ U ++ Γ₃'').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a H H' H''.
assert (uniq (Γ₁ ++ [(a, U)] ++ Γ₁' ++ Γ₁'')) by eauto with lngen. 
assert (uniq (Γ₂ ++ [(a, U)] ++ Γ₂' ++ Γ₂'')) by eauto with lngen. 
assert (uniq (Γ₃ ++ [(a, U)] ++ Γ₃' ++ Γ₃'')) by eauto with lngen. 
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; auto.
apply uniq_app_inv in H3; auto.
destruct H4; destruct H3; subst.
apply zip_app; my_auto.
apply zip_app; my_auto.
Qed.

Lemma zip_upperEU : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a,
  zip (Γ₁ ++ a ~ E ++ Γ₁' ++ Γ₁'')
      (Γ₂ ++ a ~ U ++ Γ₂' ++ Γ₂'')
      (Γ₃ ++ a ~ E ++ Γ₃' ++ Γ₃'') →
  zip Γ₁' Γ₂' Γ₃' →
  zip Γ₁'' Γ₂'' Γ₃'' →
  zip (Γ₁ ++ Γ₁' ++ a ~ E ++ Γ₁'')
      (Γ₂ ++ Γ₂' ++ a ~ U ++ Γ₂'')
      (Γ₃ ++ Γ₃' ++ a ~ E ++ Γ₃'').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a H H' H''.
assert (uniq (Γ₁ ++ [(a, E)] ++ Γ₁' ++ Γ₁'')) by eauto with lngen. 
assert (uniq (Γ₂ ++ [(a, U)] ++ Γ₂' ++ Γ₂'')) by eauto with lngen. 
assert (uniq (Γ₃ ++ [(a, E)] ++ Γ₃' ++ Γ₃'')) by eauto with lngen. 
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
Case "EU".
apply uniq_app_inv in H4; auto.
apply uniq_app_inv in H3; auto.
destruct H4; destruct H3; subst.
apply zip_app; my_auto.
apply zip_app; my_auto.
Case "E".
assert (@E typ = U).
apply binds_unique with (x := a) (E := Γ₂ ++ [(a, U)] ++ Γ₂' ++ Γ₂''); auto.
rewrite H4; auto.
congruence.
Qed.

Lemma zip_upperE : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a,
  zip (Γ₁ ++ Γ₁' ++ Γ₁'')
      (Γ₂ ++ a ~ E ++ Γ₂' ++ Γ₂'')
      (Γ₃ ++ a ~ E ++ Γ₃' ++ Γ₃'') →
  zip Γ₁' Γ₂' Γ₃' →
  zip Γ₁'' Γ₂'' Γ₃'' →
  zip (Γ₁ ++ Γ₁' ++ Γ₁'')
      (Γ₂ ++ Γ₂' ++ a ~ E ++ Γ₂'')
      (Γ₃ ++ Γ₃' ++ a ~ E ++ Γ₃'').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a H H' H''.
assert (uniq (Γ₁ ++ Γ₁' ++ Γ₁'')) by eauto with lngen. 
assert (uniq (Γ₂ ++ [(a, E)] ++ Γ₂' ++ Γ₂'')) by eauto with lngen. 
assert (uniq (Γ₃ ++ [(a, E)] ++ Γ₃' ++ Γ₃'')) by eauto with lngen.
assert (a ∉ dom (Γ₁ ++ Γ₁' ++ Γ₁'')).
  assert (binds a E (Γ₃ ++ [(a, E)] ++ Γ₃' ++ Γ₃'')) by auto.
  eapply zip_binds_E3_inv in H3; eauto. destruct H3 as [[? ?] | [? ?]]; auto.
  elimtype False. analyze_binds_uniq H4; auto.
assert (zip Γ₁ Γ₂ Γ₃).
  eapply zip_app_inv2 with (Γ₁' := Γ₁' ++ Γ₁''); eauto.
  constructor; auto. solve_uniq.
  apply zip_app; my_auto.
apply zip_app; try solve_uniq.
apply zip_app; try solve_uniq.
Qed.

Lemma zip_lowerU : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a,
  zip (Γ₁ ++ Γ₁' ++ a ~ U ++ Γ₁'')
      (Γ₂ ++ Γ₂' ++ a ~ U ++ Γ₂'')
      (Γ₃ ++ Γ₃' ++ a ~ U ++ Γ₃'') →
  zip Γ₁' Γ₂' Γ₃' →
  zip Γ₁'' Γ₂'' Γ₃'' →
  zip (Γ₁ ++ a ~ U ++ Γ₁' ++ Γ₁'')
      (Γ₂ ++ a ~ U ++ Γ₂' ++ Γ₂'')
      (Γ₃ ++ a ~ U ++ Γ₃' ++ Γ₃'').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a H H' H''.
assert (uniq (Γ₁ ++ Γ₁' ++ [(a, U)] ++ Γ₁'')) by eauto with lngen. 
assert (uniq (Γ₂ ++ Γ₂' ++ [(a, U)] ++ Γ₂'')) by eauto with lngen. 
assert (uniq (Γ₃ ++ Γ₃' ++ [(a, U)] ++ Γ₃'')) by eauto with lngen. 
rewrite_env ((Γ₁ ++ Γ₁') ++ [(a, U)] ++ Γ₁'') in H. 
rewrite_env ((Γ₂ ++ Γ₂') ++ [(a, U)] ++ Γ₂'') in H. 
rewrite_env ((Γ₃ ++ Γ₃') ++ [(a, U)] ++ Γ₃'') in H. 
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
apply uniq_app_inv in H4; simpl_env; auto.
apply uniq_app_inv in H3; simpl_env; auto.
destruct H4; destruct H3; subst.
apply zip_app_inv2 in H5; auto.
apply zip_app; my_auto.
apply zip_app; my_auto.
apply zip_app; my_auto.
Qed.

Lemma zip_lowerEU : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a,
  zip (Γ₁ ++ Γ₁' ++ a ~ E ++ Γ₁'')
      (Γ₂ ++ Γ₂' ++ a ~ U ++ Γ₂'')
      (Γ₃ ++ Γ₃' ++ a ~ E ++ Γ₃'') →
  zip Γ₁' Γ₂' Γ₃' →
  zip Γ₁'' Γ₂'' Γ₃'' →
  zip (Γ₁ ++ a ~ E ++ Γ₁' ++ Γ₁'')
      (Γ₂ ++ a ~ U ++ Γ₂' ++ Γ₂'')
      (Γ₃ ++ a ~ E ++ Γ₃' ++ Γ₃'').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a H H' H''.
assert (uniq (Γ₁ ++ Γ₁' ++ [(a, E)] ++ Γ₁'')) by eauto with lngen. 
assert (uniq (Γ₂ ++ Γ₂' ++ [(a, U)] ++ Γ₂'')) by eauto with lngen. 
assert (uniq (Γ₃ ++ Γ₃' ++ [(a, E)] ++ Γ₃'')) by eauto with lngen. 
rewrite_env ((Γ₁ ++ Γ₁') ++ [(a, E)] ++ Γ₁'') in H. 
rewrite_env ((Γ₂ ++ Γ₂') ++ [(a, U)] ++ Γ₂'') in H. 
rewrite_env ((Γ₃ ++ Γ₃') ++ [(a, E)] ++ Γ₃'') in H. 
apply zip_app_inv in H. decompose record H; clear H.
inversion H7; subst.
Case "EU".
apply uniq_app_inv in H4; simpl_env; auto.
apply uniq_app_inv in H3; simpl_env; auto.
destruct H4; destruct H3; subst.
apply zip_app_inv2 in H5; auto.
apply zip_app; my_auto.
apply zip_app; my_auto.
apply zip_app; my_auto.
Case "E".
assert (@E typ = U). simpl_env in *.
apply binds_unique with (x := a) (E := Γ₂ ++ Γ₂' ++ [(a, U)] ++ Γ₂''); auto.
rewrite H4; auto.
congruence.
Qed.

Lemma zip_lowerE : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a,
  zip (Γ₁ ++ Γ₁' ++ Γ₁'')
      (Γ₂ ++ Γ₂' ++ a ~ E ++ Γ₂'')
      (Γ₃ ++ Γ₃' ++ a ~ E ++ Γ₃'') →
  zip Γ₁' Γ₂' Γ₃' →
  zip Γ₁'' Γ₂'' Γ₃'' →
  zip (Γ₁ ++ Γ₁' ++ Γ₁'')
      (Γ₂ ++ a ~ E ++ Γ₂' ++ Γ₂'')
      (Γ₃ ++ a ~ E ++ Γ₃' ++ Γ₃'').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' Γ₁'' Γ₂'' Γ₃'' a H H' H''.
assert (uniq (Γ₁ ++ Γ₁' ++ Γ₁'')) by eauto with lngen. 
assert (uniq (Γ₂ ++ Γ₂' ++ [(a, E)] ++ Γ₂'')) by eauto with lngen. 
assert (uniq (Γ₃ ++ Γ₃' ++ [(a, E)] ++ Γ₃'')) by eauto with lngen.
assert (a ∉ dom (Γ₁ ++ Γ₁' ++ Γ₁'')).
  assert (binds a E (Γ₃ ++ Γ₃' ++ [(a, E)] ++ Γ₃'')) by auto.
  eapply zip_binds_E3_inv in H3; eauto. destruct H3 as [[? ?] | [? ?]]; auto.
  elimtype False. analyze_binds_uniq H4; auto. solve_uniq.
assert (zip Γ₁ Γ₂ Γ₃).
  eapply zip_app_inv2 with (Γ₁' := Γ₁' ++ Γ₁''); eauto.
  apply zip_app; my_auto.
apply zip_app; try solve_uniq.
constructor; my_auto.
apply zip_app; try solve_uniq.
Qed.

Lemma zip_swap_Eq : forall Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ a' τ',
  zip (Γ₁ ++ a ~ Eq τ ++ a' ~ Eq τ' ++ Γ₁')
      (Γ₂ ++ a ~ Eq τ ++ a' ~ Eq τ' ++ Γ₂')
      (Γ₃ ++ a ~ Eq τ ++ a' ~ Eq τ' ++ Γ₃') →
  zip (Γ₁ ++ a' ~ Eq τ' ++ a ~ Eq (tsubst_typ τ' a' τ) ++ Γ₁')
      (Γ₂ ++ a' ~ Eq τ' ++ a ~ Eq (tsubst_typ τ' a' τ) ++ Γ₂')
      (Γ₃ ++ a' ~ Eq τ' ++ a ~ Eq (tsubst_typ τ' a' τ) ++ Γ₃').
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁' Γ₂' Γ₃' a τ a' τ' H.
assert (uniq (Γ₁ ++ [(a, Eq τ)] ++ [(a', Eq τ')] ++ Γ₁')) by eauto with lngen. 
assert (uniq (Γ₂ ++ [(a, Eq τ)] ++ [(a', Eq τ')] ++ Γ₂')) by eauto with lngen. 
assert (uniq (Γ₃ ++ [(a, Eq τ)] ++ [(a', Eq τ')] ++ Γ₃')) by eauto with lngen. 
apply zip_app_inv in H. decompose record H; clear H; subst.
inversion H7; subst. inversion H14; subst.
apply uniq_app_inv in H3; auto. apply uniq_app_inv in H4; auto.
destruct H3; destruct H4; subst. inversion H6; inversion H3; subst.
apply zip_app; my_auto.
Qed.

(*
Lemma zip_assoc : forall Γ₁ Γ₂ Γ₃ Γ₁₂ Γ₂₃ Γ₁₂₃ Γ₁₂₃',
  zip Γ₁ Γ₂ Γ₁₂ → zip Γ₁₂ Γ₃ Γ₁₂₃ →
  zip Γ₁ Γ₂₃ Γ₁₂₃' → zip Γ₂ Γ₃ Γ₂₃ →
  Γ₁₂₃ = Γ₁₂₃'.
Proof.
intros Γ₁ Γ₂ Γ₃ Γ₁₂ Γ₂₃ Γ₁₂₃ Γ₁₂₃' H H0 H1 H2.
generalize dependent Γ₃. generalize dependent Γ₂₃.
generalize dependent Γ₁₂₃. generalize dependent Γ₁₂₃'.
induction H; intros.
Case "nil".
inversion H0; subst; auto. inversion H1; subst.
auto.
inversion H2.
inversion H2; subst. inversion H1; subst.
  replace G3 with G in * by eauto using zip_unique.
  f_equal. auto using zip_nil.
Case "TT".
inversion H1; subst.
  inversion H2; subst.
    inversion H3; subst. f_equal. eauto.
    inversion H3; subst.
  clear H1. inversion H3; subst. clear H3. inversion H2; subst. clear H2. f_equal.
    eapply IHzip; eauto.
*)
