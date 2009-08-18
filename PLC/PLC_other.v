Add LoadPath "../metatheory".
Require Export PLC_init.

(* Mutual induction principles *)
Scheme pval_mut_ind_aux := Induction for pval Sort Prop
with   val_mut_ind_aux  := Induction for val  Sort Prop.
Combined Scheme pval_val_mut_ind from pval_mut_ind_aux, val_mut_ind_aux.

(* Administrative lemmas *)
Lemma pval_val_regular :
  (forall p, pval p → lc_term p) ∧ (forall v, val v → lc_term v).
Proof.
apply pval_val_mut_ind; eauto.
Qed.

Lemma pval_regular : forall p, pval p → lc_term p.
Proof.
intros; destruct pval_val_regular as [H1 _]; auto.
Qed.

Lemma val_regular : forall v, val v → lc_term v.
Proof.
intros; destruct pval_val_regular as [_ H2]; auto.
Qed.
Hint Resolve pval_regular val_regular.

(* Lemmas about values *)
Lemma value_is_normal_aux :
  (forall v, pval v → ~ exists e, v ⇝ e) ∧
  (forall v, val v → ~ exists e, v ⇝ e).
Proof.
apply pval_val_mut_ind; intros; intros [e0 Hred]; inversion Hred; subst; eauto.
inversion H.
inversion H1; subst. inversion p.
inversion H0.
pick fresh x. eapply H; eauto.
Qed.

Lemma value_is_normal : forall v, val v → ~ exists e, v ⇝ e.
Proof.
destruct value_is_normal_aux as [_ Th]. intuition auto.
Qed.

(* Administrative lemmas *)
Lemma var_subst : forall e x, subst_term e x (term_var_f x) = e.
Proof.
intros e x; simpl; destruct (x == x); congruence.
Qed.
Hint Rewrite var_subst : lngen.

Lemma red0_regular1 : forall e1 e2, red0 e1 e2 → lc_term e1.
Proof.
intros e1 e2 H; destruct H; auto.
Qed.

Lemma red0_regular2 : forall e1 e2, red0 e1 e2 → lc_term e2.
Proof.
intros e1 e2 H; destruct H; auto with lngen.
Qed.
Hint Resolve red0_regular1 red0_regular2.

Lemma red1_regular1 : forall e1 e2, e1 ⇝ e2 → lc_term e1.
Proof.
intros e1 e2 H; induction H; eauto.
Qed.

Lemma red1_regular2 : forall e1 e2, e1 ⇝ e2 → lc_term e2.
Proof.
intros e1 e2 H; induction H; eauto.
Qed.
Hint Resolve red1_regular1 red1_regular2.

Lemma red_star_regular1 : forall e1 e2, e1 ⇝⋆ e2 →
  lc_term e2 → lc_term e1.
Proof.
intros e1 e2 H Hlc; induction H; eauto.
Qed.

Lemma red_star_regular2 : forall e1 e2, e1 ⇝⋆ e2 →
  lc_term e1 → lc_term e2.
Proof.
intros e1 e2 H Hlc; induction H; eauto.
Qed.
Hint Resolve red_star_regular1 red_star_regular2.

Lemma para_red_regular1 : forall e1 e2, e1 ⇒ e2 → lc_term e1.
Proof.
intros e1 e2 H; induction H; eauto.
Qed.

Lemma para_red_regular2 : forall e1 e2, e1 ⇒ e2 → lc_term e2.
Proof.
intros e1 e2 H; induction H; eauto.
Qed.
Hint Resolve para_red_regular1 para_red_regular2.

Lemma can_regular1 : forall e1 e2, e1↓ = e2 → lc_term e1.
Proof.
intros e1 e2 H; induction H; auto.
Qed.

Lemma can_regular2 : forall e1 e2, e1↓ = e2 → lc_term e2.
Proof.
intros e1 e2 H; induction H; auto.
pick fresh x; auto with lngen.
Qed.
Hint Resolve can_regular1 can_regular2.

(* Renaming lemmas *)
Lemma red0_renaming : forall x y e e', red0 e e' →
  red0 (subst_term (term_var_f y) x e) (subst_term (term_var_f y) x e').
Proof.
intros x y e e' H.
inversion H; subst.
simpl. rewrite subst_term_open_term_wrt_term; auto. apply red0_beta; auto with lngen.
assert (lc_term (subst_term (term_var_f y) x (term_abs e1))) by auto with lngen; auto.
Qed.
Hint Resolve red0_renaming.

Lemma red1_renaming : forall x y e e', e ⇝ e' →
  (subst_term (term_var_f y) x e) ⇝ (subst_term (term_var_f y) x e').
Proof.
intros x y e e' H.
induction H; subst; simpl; auto.
apply red1_appL; auto with lngen.
apply red1_appR; auto with lngen.
apply red1_abs with (L := L `union` {{x}}); intros z Hz.
replace (term_var_f z) with (subst_term (term_var_f y) x (term_var_f z)) by auto with lngen.
repeat rewrite <- subst_term_open_term_wrt_term; eauto.
Qed.
Hint Resolve red1_renaming.

Lemma red_star_renaming : forall x y e e', e ⇝⋆ e' →
  (subst_term (term_var_f y) x e) ⇝⋆ (subst_term (term_var_f y) x e').
Proof.
intros x y e e' H.
induction H.
apply rt_step; auto.
apply rt_refl.
eapply rt_trans; eauto.
Qed.
Hint Resolve red_star_renaming.

(* Lemmas about red_star *)
Lemma red_star_context_appL : forall e1 e1' e2,
  lc_term e2 → e1 ⇝⋆ e1' →
  term_app e1 e2 ⇝⋆ term_app e1' e2.
Proof.
intros e1 e1' e2 Hlc Hred.
induction Hred.
apply rt_step; auto.
apply rt_refl.
eapply rt_trans; eauto.
Qed.

Lemma red_star_context_appR : forall e1 e2 e2',
  lc_term e1 → e2 ⇝⋆ e2' →
  term_app e1 e2 ⇝⋆ term_app e1 e2'.
Proof.
intros e1 e2 e2' Hlc Hred.
induction Hred.
apply rt_step; auto.
apply rt_refl.
eapply rt_trans; eauto.
Qed.

Lemma red_star_context_app : forall e1 e1' e2 e2',
  lc_term e1 → lc_term e2 → e1 ⇝⋆ e1' → e2 ⇝⋆ e2' →
  term_app e1 e2 ⇝⋆ term_app e1' e2'.
Proof.
intros e1 e1' e2 e2' Hlc1 Hlc2 Hred1 Hred2.
eapply rt_trans; eauto using red_star_context_appL, red_star_context_appR.
Qed.

Lemma red_star_context_abs : forall L e e',
  (forall x, x `notin` L → e ^ x ⇝⋆ e' ^ x) →
  term_abs e ⇝⋆ term_abs e'.
Proof.
intros L e e' H. pick fresh x.
remember (e ^ x) as e1.
remember (e' ^ x) as e1'.
assert (e1 ⇝⋆ e1') as Hred by solve [subst; apply H; auto]. clear H.
generalize dependent x. generalize dependent e'. generalize dependent e.
induction Hred; intros; subst.
Case "step".
apply rt_step.
apply red1_abs with (L := L `union` fv_term e `union` fv_term e'); intros.
rewrite <- var_subst with (e := term_var_f x) (x := x0).
replace e with (subst_term (term_var_f x) x0 e) by auto with lngen.
replace e' with (subst_term (term_var_f x) x0 e') by auto with lngen.
repeat rewrite <- subst_term_open_term_wrt_term; eauto.
Case "refl".
assert (e = e'). eapply open_term_wrt_term_inj; eauto. subst. apply rt_refl.
Case "trans".
apply rt_trans with (y := term_abs (close_term_wrt_term x0 y)).
apply IHHred1 with (x := x0); autorewrite with lngen; auto.
apply IHHred2 with (x := x0); autorewrite with lngen; auto.
Qed.
Hint Resolve red_star_context_appL red_star_context_appR red_star_context_app red_star_context_abs.
