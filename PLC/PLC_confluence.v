Add LoadPath "../metatheory".
Require Export PLC_init.
Require Export PLC_other.
Add LoadPath "../lib".
Require Export Rel.

(* Lemmas about canonize *)
Lemma can_renaming : forall e1 e2 x y,
  e1 ↓ = e2 →
  (subst_term (term_var_f y) x e1) ↓ = (subst_term (term_var_f y) x e2).
Proof.
assert (forall n e1, size_term e1 <= n → forall e2 (x y: termvar),
  can e1 e2 → can (subst_term (term_var_f y) x e1) (subst_term (term_var_f y) x e2)) as Th.
intro n; induction n; intros e1 Hsize e2 x y H.
size_term_absurd e1.
destruct H; simpl in *.
Case "var". destruct (x0 == x); subst; auto.
Case "abs". apply can_abs with (L := L `union` {{ x }}); intros.
  replace (term_var_f x0) with (subst_term (term_var_f y) x (term_var_f x0)) by auto with lngen.
  repeat rewrite <- subst_term_open_term_wrt_term; auto.
  apply IHn; auto; autorewrite with lngen; omega.
Case "app1". apply can_app1; try solve [apply IHn; auto; omega].
  intro; destruct e1; simpl; try congruence. destruct (t == x); congruence.
Case "app2".
  rewrite subst_term_open_term_wrt_term; auto.
  apply can_app2 with (L := L `union` {{x}}); intros.
  replace (term_var_f x0) with (subst_term (term_var_f y) x (term_var_f x0)) by auto with lngen.
  repeat rewrite <- subst_term_open_term_wrt_term; auto.
  apply IHn; auto; autorewrite with lngen; omega.
  apply IHn; auto; omega.

intros e1 e2 x y H; apply Th with (n := size_term e1); auto.
Qed.

Lemma can_deterministic : forall e e1 e2,
  e↓ = e1 → e↓ = e2 → e1 = e2.
Proof.
intros e e1 e2 H. generalize dependent e2. induction H; intros.
inversion H; reflexivity.
inversion H1; subst; f_equal; pick fresh x;
  apply open_term_wrt_term_inj with (x1 := x); auto.
inversion H2; subst.
  erewrite IHcan1; eauto; erewrite IHcan2; eauto.
  edestruct H; eauto.
inversion H2; subst.
  edestruct H5; eauto.
  f_equal; auto.
  pick fresh x; eauto using open_term_wrt_term_inj.
Qed.

Lemma can_total : forall e1, lc_term e1 → exists e2, e1↓ = e2.
Proof.
intros e1 Hlc; induction Hlc; eauto.
Case "abs". pick fresh x; destruct (H0 x) as [e2 H2].
  exists (term_abs (close_term_wrt_term x e2)).
  apply can_abs with (L := {{x}}); intros.
  rewrite <- (close_term_wrt_term_open_term_wrt_term e x); auto.
  repeat rewrite <- subst_term_spec.
  auto using can_renaming.
Case "app". destruct IHHlc1 as [e1' H1]. destruct IHHlc2 as [e2' H2].
destruct Hlc1; try solve [exists (term_app e1' e2'); apply can_app1; auto; congruence].
SCase "abs".
inversion H1; subst. exists (e' ^^ e2'). apply can_app2 with (L := L); auto.
Qed.

(*
Lemma can_fv : forall e1 e2, e1↓ = e2 → fv_term e2 [<=] fv_term e1.
Proof.
intros e1 e2 H; induction H; simpl; try fsetdec.
Case "app1".
  pick fresh x.
  assert (fv_term (e' ^ x) [<=]
    fv_term (e ^ x)) by auto.
  assert (fv_term (e ^ x) [<=]
    fv_term (term_var_f x) `union` fv_term e) by auto with lngen.
  assert (fv_term e' [<=] fv_term (e' ^ x))
    by auto with lngen.
  simpl in *; fsetdec.
Case "app2".
  assert (fv_term (e1' ^^ e2')
    [<=] union (fv_term e2') (fv_term e1')) by auto with lngen.
  intros y Hy. pick fresh x.
  assert (fv_term e1' [<=] fv_term (e1' ^ x)) as H3 by auto with lngen.
  assert (fv_term (e1 ^ x) [<=] fv_term (term_var_f x) `union` fv_term e1) as H4 by auto with lngen.
  assert (fv_term (e1' ^ x) [<=] fv_term (e1 ^ x)) as H5 by auto.
  assert (fv_term e1' [<=] fv_term (term_var_f x) `union` fv_term e1) as H6 by fsetdec; clear H3 H4 H5.
  assert (y `in` fv_term (term_var_f x) `union` fv_term e1 `union` fv_term e2) as H3 by fsetdec; clear H6.
  simpl in *; fsetdec.
Qed.
Hint Resolve can_fv.
*)

(* Lemmas about para_red *)
Lemma para_red_refl : forall e, lc_term e → e ⇒ e.
Proof.
intros e H. induction H; try solve [constructor; auto].
apply para_red_abs with (L := fv_term e); auto.
Qed.
Hint Resolve para_red_refl.

Lemma red0_para_red : forall e1 e2, red0 e1 e2 → e1 ⇒ e2.
Proof.
intros e1 e2 H. inversion H; subst.
apply para_red_app2 with (L := fv_term e0); eauto.
Qed.
Hint Resolve red0_para_red.

Lemma red1_para_red : forall e1 e2, e1 ⇝ e2 → e1 ⇒ e2.
Proof.
intros e1 e2 H. induction H; auto.
apply para_red_abs with (L := L); auto.
Qed.

Lemma para_red_subst : forall e1 e1' e2 e2' x,
  e1 ⇒ e1' → e2 ⇒ e2' →
  (subst_term e2 x e1) ⇒ (subst_term e2' x e1').
Proof.
intros e1 e1' e2 e2' x H.
assert (lc_term e1) as Hlc by eauto.
generalize dependent e1'.
generalize dependent e2.
generalize dependent e2'.
generalize dependent x.
induction Hlc; intros y f2' f2 e1' Htt' Huu'; inversion Htt'; subst; simpl.
destruct (x == y); auto.
apply para_red_abs with (L := L `union` singleton y); intros.
  assert (term_var_f x = subst_term f2 y (term_var_f x)) as H3. autorewrite with lngen; reflexivity.
  assert (term_var_f x = subst_term f2' y (term_var_f x)) as H4. autorewrite with lngen; reflexivity.
  rewrite H3 at 1; clear H3.
  rewrite H4 at 2; clear H4.
  repeat rewrite <- subst_term_open_term_wrt_term; eauto.
apply para_red_app1; auto.
rewrite subst_term_open_term_wrt_term; eauto.
  assert (para_red (subst_term f2 y (term_abs e0)) (subst_term f2' y (term_abs e1'0))) as Ht.
    apply IHHlc1; auto;
    apply para_red_abs with (L := L); auto.
  simpl in Ht; inversion Ht; subst; clear Ht.
  apply para_red_app2 with (L := L `union` L0 `union` {{y}}); auto.
Qed.

Lemma para_red_canonize : forall e1 e2 e1',
  e1 ⇒ e2 → e1 ↓ = e1' → e2 ⇒ e1'.
Proof.
intros e1 e2 e1' Hpara Hcan. generalize dependent e1'.
induction Hpara; intros v Hcan.
inversion Hcan; subst; constructor.
inversion Hcan; subst; apply para_red_abs with (L := L `union` L0); intros; auto.
inversion Hcan; subst.
  constructor; auto.
  inversion Hpara1; subst; pick fresh x; assert (para_red (term_abs e') (term_abs e1'0)) as H by eauto.
    inversion H; subst; apply para_red_app2 with (L := L1); intros; auto.
inversion Hcan; subst.
  absurdity with congruence.
  pick fresh x for (fv_term e1' `union` fv_term e1'0 `union` L `union` L0).
  rewrite <- (close_term_wrt_term_open_term_wrt_term e1' x); auto.
  rewrite <- (close_term_wrt_term_open_term_wrt_term e1'0 x); auto.
  repeat rewrite <- subst_term_spec.
  apply para_red_subst; auto.
Qed.

Lemma para_red_diamond : diamond (para_red⁻¹).
Proof.
intros e1 e2 [e [H1 H2]]. unfold transp in *|-.
destruct (can_total e) as [e' H']; eauto.
exists e'; unfold transp; split; eauto using para_red_canonize.
Qed.

Lemma para_red_plus_diamond : diamond (para_red⁻¹⁺).
Proof.
auto using diamond_plus, para_red_diamond.
Qed.

Lemma para_red_red_star : forall e1 e2, e1 ⇒ e2 → e1 ⇝⋆ e2.
Proof.
intros e1 e2 H.
assert (lc_term e1) as Hlc by eauto.
generalize dependent e2.
induction Hlc; intros e0 Hpara; inversion Hpara; subst; eauto.
apply rt_refl.
apply rt_trans with (y := term_app (term_abs e1') e2'); eauto.
apply rt_step; apply red1_empty; apply red0_beta; eauto.
Qed.

Lemma red_star_para_red_plus_equiv : forall t t',
  (lc_term t ∧ t ⇝⋆ t') ↔ t ⇒⁺ t'.
Proof.
intros t t'; split; intro H.
destruct H. induction H0.
  eauto using t_step, red1_para_red.
  eauto using t_step, para_red_refl.
  eauto using t_trans.
induction H; split; eauto.
  auto using para_red_red_star.
  intuition auto.
  intuition eauto using rt_trans.
Qed.

Theorem church_rosser : forall t t1 t2,
  lc_term t → t ⇝⋆ t1 → t ⇝⋆ t2 →
  exists t', t1 ⇝⋆ t' ∧ t2 ⇝⋆ t'.
Proof.
intros t t1 t2 Hlc H1 H2.
assert (t ⇒⁺ t1) as H3. rewrite <- red_star_para_red_plus_equiv; auto.
assert (t ⇒⁺ t2) as H4. rewrite <- red_star_para_red_plus_equiv; auto.
clear H1 H2.
edestruct (para_red_plus_diamond t1 t2) as [t' [H1' H2']].
exists t; split.
  rewrite (transp_plus_commute _ _ _); auto.
  unfold transp at 1; rewrite (transp_plus_commute _ _ _); auto.
unfold transp at 1 in H1'; rewrite (transp_plus_commute _ _ _) in H1'.
rewrite (transp_plus_commute _ _ _) in H2'.
unfold transp in *|-.
rewrite <- red_star_para_red_plus_equiv in *|-.
intuition eauto.
Qed.
