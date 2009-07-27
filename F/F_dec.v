Add LoadPath "metatheory".
Require Export F_soundness.

Lemma eq_typ_dec : forall (τ₁ τ₂: typ), {τ₁ = τ₂} + {τ₁ ≠ τ₂}.
Proof.
decide equality.
apply eq_nat_dec.
Qed.

Lemma in_dom_dec : forall x (Γ: typing_env), {x ∈ dom Γ} + {~x ∈ dom Γ}.
Proof.
intros x Γ. induction Γ; simpl.
auto.
destruct a; destruct IHΓ; auto.
destruct (x == a); subst; auto.
Qed.

Lemma uniq_dec : forall (Γ: typing_env), {uniq Γ} + {~uniq Γ}.
Proof.
intro Γ; induction Γ.
auto.
destruct IHΓ.
  destruct a as [x τ]; destruct (in_dom_dec x Γ); [right | left]; auto.
    intro; solve_uniq.
  right; intro; inversion H; subst; auto.
Qed.

Lemma lc_typ_dec : forall τ, {lc_typ τ} + {~lc_typ τ}.
Proof.
assert (forall n t, size_typ t ≤ n -> {lc_typ t} + {~lc_typ t}) as Th.
intro n; induction n; intros t Hsize; destruct t; simpl in *; try solve [absurdity with omega]; auto.
Case "bound var". right; intro H; inversion H.
Case "arrow".
  destruct (IHn t1).
    omega. destruct (IHn t2). omega. auto.
    right; intro H; inversion H; auto.
    right; intro H; inversion H; auto.
Case "forall".
  assert (forall a, {lc_typ (open_typ_wrt_typ t (typ_var_f a))} + {⌉lc_typ (open_typ_wrt_typ t (typ_var_f a))}) as H.
    intro a; apply IHn; autorewrite with lngen; omega.
  pick fresh a; destruct (H a); [left | right]. eauto using lc_typ_forall_exists.
  intro H0; apply n0; inversion H0; subst; auto.

intro τ; apply (Th (size_typ τ)); auto.
Qed.

Lemma wftyp_forall_exists : forall a Γ τ,
  a ∉ ftv_typ τ →
  wftyp (a ~ None ++ Γ) (open_typ_wrt_typ τ (typ_var_f a)) →
  wftyp Γ (typ_forall τ).
Proof.
intros a Γ τ H H0.
assert (wfenv Γ). assert (wfenv (a~None ++ Γ)) by eauto. inversion H1; subst; auto.
assert (uniq Γ) by auto.
apply wftyp_forall with (L := {{a}} ∪ dom Γ); intros b Hb. assert (b ≠ a) by auto.
replace (open_typ_wrt_typ τ (typ_var_f b)) with (tsubst_typ (typ_var_f b) a (open_typ_wrt_typ τ (typ_var_f a))).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) nil ++ [(b, None)] ++ Γ).
apply wftyp_tsubst; simpl; simpl_env.
apply wftyp_weakening; simpl_env; auto. constructor; auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
autorewrite with lngen. reflexivity.
Qed.

Lemma wftyp_forall_exists_inv : forall a τ Γ,
  a ∉ ftv_typ τ ∪ dom Γ →
  wftyp Γ (typ_forall τ) →
  wftyp (a ~ None ++ Γ) (open_typ_wrt_typ τ (typ_var_f a)).
Proof.
intros a τ Γ Ha H.
inversion H; subst. pick fresh b.
assert (wftyp ([(b, None)] ++ Γ) (open_typ_wrt_typ τ (typ_var_f b))) by auto.
replace (open_typ_wrt_typ τ (typ_var_f a)) with (tsubst_typ (typ_var_f a) b (open_typ_wrt_typ τ (typ_var_f b))).
assert (wfenv ([(a, None)] ++ Γ)). assert (wfenv ([(b, None)] ++ Γ)) by eauto; inversion H1; subst; constructor; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ [(a, None)] ++ Γ).
apply wftyp_tsubst; simpl; simpl_env.
apply wftyp_weakening; auto. constructor; auto.
assert (uniq ([(b, None)] ++ Γ)) as H1 by eauto; inversion H1; subst; auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
autorewrite with lngen. reflexivity.
Qed.

Lemma wfenv_wftyp_aux : forall τ Γ, wfenv Γ →
  {wftyp Γ τ} + {~wftyp Γ τ}.
Proof.
intro τ.
destruct (lc_typ_dec τ).
assert (lc_set_typ τ) as H by auto with lngen.
induction H; intros.
Case "var".
destruct (binds_lookup _ a1 Γ).
destruct s; destruct x; [right | left]; auto.
intro H0; inversion H0; subst. assert (uniq Γ) by eauto.
  assert (Some t = None). eapply binds_unique; eauto. congruence.
right. intro H0; inversion H0; subst; apply (n None); auto.
Case "arrow".
edestruct (IHlc_set_typ1); auto with lngen. eauto.
edestruct (IHlc_set_typ2); auto with lngen. eauto.
auto.
right. intro H2; apply n; inversion H2; subst; auto.
right. intro H2; apply n; inversion H2; subst; auto.
Case "forall".
pick fresh a.
assert (lc_typ (open_typ_wrt_typ t1 (typ_var_f a))) as H1. inversion l; subst; auto.
destruct (H a H1 (a~None ++ Γ)); auto.
left. eapply wftyp_forall_exists; eauto.
right. intro H2; apply n; apply wftyp_forall_exists_inv; auto.
Case "not lc".
intros. right. intro H0; apply n; eauto.
Qed.

Lemma wfenv_wftyp_dec : forall Γ,
  ({wfenv Γ} + {~wfenv Γ}) * (forall τ, {wftyp Γ τ} + {~wftyp Γ τ}).
Proof.
intro Γ; induction Γ; simpl_env in *; auto.
Case "wfenv_empty".
split; auto.
intros; apply wfenv_wftyp_aux with (Γ := nil); auto.
destruct a; destruct o; destruct IHΓ as [H1 H2].
Case "wfenv_cons_x".
split.
SCase "first part".
destruct H1 as [H1 | H1]. destruct (in_dom_dec a Γ).
right. intro H; inversion H; subst; contradiction.
destruct (H2 t); auto.
right. intro H; apply n0; inversion H; subst; auto.
right. intro H; apply H1; inversion H; subst; eauto.
SCase "second part".
destruct H1 as [H1 | H1]; intros. destruct (in_dom_dec a Γ).
right. intro H. assert (uniq (a ~ Some t ++ Γ)) by eauto.
  destruct_uniq. contradiction.
destruct (H2 t); auto.
apply (wfenv_wftyp_aux τ (a ~ Some t ++ Γ)); auto.
right. intro H; apply n0; assert (wfenv (a ~ Some t ++ Γ)) as H3 by eauto; inversion H3; subst; auto.
right. intro H; apply H1. assert (wfenv (a ~ Some t ++ Γ)) as H3 by eauto; inversion H3; subst; eauto.
Case "wfenv_cons_a".
split.
SCase "first part".
destruct H1 as [H1 | H1]. destruct (in_dom_dec a Γ); auto.
right. intro H; inversion H; subst; contradiction.
right. intro H; apply H1; inversion H; subst; eauto.
SCase "second part".
destruct H1 as [H1 | H1]; intros. destruct (in_dom_dec a Γ).
right. intro H. assert (uniq (a ~ None ++ Γ)) by eauto.
  destruct_uniq. contradiction.
apply (wfenv_wftyp_aux τ (a ~ None ++ Γ)); auto.
right. intro H; apply H1; assert (wfenv (a ~ None ++ Γ)) as H3 by eauto; inversion H3; subst; auto.
Qed.

Lemma wftyp_dec : forall Γ τ, {wftyp Γ τ} + {~wftyp Γ τ}.
Proof.
intros Γ τ. destruct (wfenv_wftyp_dec Γ); auto.
Qed.

Lemma wfenv_dec : forall Γ, {wfenv Γ} + {~wfenv Γ}.
Proof.
intros Γ. destruct (wfenv_wftyp_dec Γ); auto.
Qed.

Lemma lc_term_dec : forall t, {lc_term t} + {~lc_term t}.
Proof.
assert (forall n t, size_term t ≤ n -> {lc_term t} + {~lc_term t}) as Th.
intro n; induction n; intros t Hsize; destruct t; simpl in *; try solve [absurdity with omega]; auto.
Case "bound var". right; intro H; inversion H.
Case "abs".
  assert (forall x, {lc_term (t0 ^ x)} + {⌉lc_term (t0 ^ x)}) as H.
    intro x; apply IHn; autorewrite with lngen; omega.
  destruct (lc_typ_dec t).
  pick fresh x; destruct (H x); [left | right]. eauto using lc_term_abs_exists.
  intro H0; apply n0; inversion H0; subst; auto.
  right. intro H0; apply n0; inversion H0; subst; auto.
Case "app".
  destruct (IHn t1).
    omega. destruct (IHn t2). omega. auto.
    right; intro H; inversion H; auto.
    right; intro H; inversion H; auto.
Case "gen".
  assert (forall a, {lc_term (open_term_wrt_typ t (typ_var_f a))} + {⌉lc_term (open_term_wrt_typ t (typ_var_f a))}) as H.
    intro a; apply IHn; autorewrite with lngen; omega.
  pick fresh x; destruct (H x); [left | right]. eauto using lc_term_gen_exists.
  intro H0; apply n0; inversion H0; subst; auto.
Case "inst".
  destruct (lc_typ_dec t0). destruct (IHn t).
    omega. auto.
  right. intro H0; apply n0; inversion H0; subst; auto.
  right. intro H0; apply n0; inversion H0; subst; auto.

intro t; apply (Th (size_term t)); auto.
Qed.

Lemma wfterm_abs_exists : forall x τ Γ e τ',
  x ∉ fv_term e →
  wfterm (x ~ Some τ ++ Γ) (e ^ x) τ' → wfterm Γ (term_abs τ e) (typ_arrow τ τ').
Proof.
intros x τ Γ e τ' Hx H.
assert (uniq Γ). assert (uniq ([(x, Some τ)] ++ Γ)) as H1 by eauto. inversion H1; auto.
apply wfterm_abs with (L := {{x}} ∪ dom Γ); intros y Hy. assert (y ≠ x) by auto.
replace (e ^ y) with (subst_term (term_var_f y) x (e ^ x)).
apply wfterm_subst with (τ₂ := τ) (Γ₁ := nil); simpl; simpl_env.
apply wfterm_weakening; simpl_env; auto. constructor; eauto.
constructor; auto. constructor; eauto.
rewrite subst_term_open_term_wrt_term; auto.
autorewrite with lngen. reflexivity.
Qed.

Lemma wfterm_gen_exists : forall a τ Γ e,
  a ∉ ftv_term e ∪ ftv_typ τ →
  wfterm (a ~ None ++ Γ) (open_term_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ τ (typ_var_f a)) →
  wfterm Γ (term_gen e) (typ_forall τ).
Proof.
intros a τ Γ e Ha H.
assert (uniq Γ). assert (uniq ([(a, None)] ++ Γ)) as H1 by eauto. inversion H1; auto.
apply wfterm_gen with (L := {{a}} ∪ dom Γ); intros b Hb. assert (b ≠ a) by auto.
replace (open_term_wrt_typ e (typ_var_f b)) with (tsubst_term (typ_var_f b) a (open_term_wrt_typ e (typ_var_f a))).
replace (open_typ_wrt_typ τ (typ_var_f b)) with (tsubst_typ (typ_var_f b) a (open_typ_wrt_typ τ (typ_var_f a))).
rewrite_env (env_map (tsubst_typ (typ_var_f b) a) nil ++ b ~ None ++ Γ).
assert (wfenv ([(b, None)] ++ Γ)). constructor; auto.
assert (wfenv (a ~ None ++ Γ)) by eauto; inversion H2; subst; auto.
apply wfterm_tsubst; simpl; simpl_env.
apply wfterm_weakening; simpl_env; auto. constructor; auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
autorewrite with lngen. reflexivity.
rewrite tsubst_term_open_term_wrt_typ; auto.
autorewrite with lngen. reflexivity.
Qed.

Lemma wfterm_abs_exists_inv : forall x τ Γ e τ',
  x ∉ fv_term e ∪ dom Γ →
  wfterm Γ (term_abs τ e) (typ_arrow τ τ') →
  wfterm (x ~ Some τ ++ Γ) (e ^ x) τ'.
Proof.
intros x τ Γ e τ' Hx H.
inversion H; subst. pick fresh y.
assert (wfterm ([(y, Some τ)] ++ Γ) (e ^ y) τ') by auto.
replace (e ^ x) with (subst_term (term_var_f x) y (e ^ y)).
assert (wfenv ([(x, Some τ)] ++ Γ)). assert (wfenv ([(y, Some τ)] ++ Γ)) by eauto; inversion H1; subst; constructor; auto.
apply wfterm_subst with (τ₂ := τ) (Γ₁ := nil); simpl; simpl_env.
apply wfterm_weakening; auto. constructor; auto.
assert (uniq ([(y, Some τ)] ++ Γ)) as H1 by eauto; inversion H1; subst; auto.
rewrite subst_term_open_term_wrt_term; auto.
autorewrite with lngen. reflexivity.
Qed.

Lemma wfterm_gen_exists_inv : forall a τ Γ e,
  a ∉ fv_term e ∪ ftv_typ τ ∪ dom Γ →
  wfterm Γ (term_gen e) (typ_forall τ) →
  wfterm (a ~ None ++ Γ) (open_term_wrt_typ e (typ_var_f a)) (open_typ_wrt_typ τ (typ_var_f a)).
Proof.
intros a τ Γ e Ha H.
inversion H; subst. pick fresh b.
assert (wfterm ([(b, None)] ++ Γ) (open_term_wrt_typ e (typ_var_f b)) (open_typ_wrt_typ τ (typ_var_f b))) by auto.
replace (open_term_wrt_typ e (typ_var_f a)) with (tsubst_term (typ_var_f a) b (open_term_wrt_typ e (typ_var_f b))).
replace (open_typ_wrt_typ τ (typ_var_f a)) with (tsubst_typ (typ_var_f a) b (open_typ_wrt_typ τ (typ_var_f b))).
assert (wfenv ([(a, None)] ++ Γ)). assert (wfenv ([(b, None)] ++ Γ)) by eauto; inversion H1; subst; constructor; auto.
rewrite_env (env_map (tsubst_typ (typ_var_f a) b) nil ++ [(a, None)] ++ Γ).
apply wfterm_tsubst; simpl; simpl_env.
apply wfterm_weakening; auto. constructor; auto.
assert (uniq ([(b, None)] ++ Γ)) as H1 by eauto; inversion H1; subst; auto.
rewrite tsubst_typ_open_typ_wrt_typ; auto.
autorewrite with lngen. reflexivity.
rewrite tsubst_term_open_term_wrt_typ; auto.
autorewrite with lngen. reflexivity.
Qed.

Lemma wfterm_dec : forall Γ e,
  {τ | wfterm Γ e τ} + {forall τ, ~wfterm Γ e τ}.
Proof.
intros Γ e.
destruct (wfenv_dec Γ); eauto.
destruct (lc_term_dec e) as [H | H]; eauto.
assert (lc_set_term e) as H' by auto with lngen; clear H.
generalize dependent Γ. induction H'; intros.
Case "var". destruct (binds_lookup _ x1 Γ) as [[o H] | H].
  destruct o; eauto. right. intros τ H0; inversion H0; subst.
  assert (uniq Γ) by eauto. assert (Some τ = None). eapply binds_unique; eauto. congruence.
  right; intros τ H0; inversion H0; subst; eapply H; eauto.
Case "abs".
destruct (wftyp_dec Γ t1).
pick fresh x.
edestruct (H x (x ~ Some t1 ++ Γ)) as [[τ H1] | H1]; auto.
left; eauto using wfterm_abs_exists.
right; intros τ H0; inversion H0; subst; eapply H1; eauto using wfterm_abs_exists_inv.
right; intros τ H0; inversion H0; subst; eapply n; inversion H0; subst; pick fresh y; eauto.
Case "app".
edestruct (IHH'1 Γ) as [[τ₁ H1] | H1]; auto.
SCase "wfterm e1".
destruct τ₁.
SSCase "bound var".
assert (lc_typ (typ_var_b n)) as H by eauto; assert False by inversion H; contradiction.
SSCase "free var".
right; intros τ H; inversion H; subst;
  assert (typ_var_f t = typ_arrow t2 τ) by eauto using wfterm_uniqueness;
    congruence.
SSCase "typ_arrow".
edestruct (IHH'2 Γ) as [[τ₂ H2] | H2]; auto.
SSSCase "wfterm e2".
destruct (eq_typ_dec τ₁1 τ₂); subst.
SSSSCase "τ₁1 = τ₂". eauto.
SSSSCase "τ₁1 ≠ τ₂". right. intros τ H. inversion H; subst.
assert (typ_arrow τ₁1 τ₁2 = typ_arrow t2 τ) by eauto using wfterm_uniqueness.
assert (τ₂ = t2) by eauto using wfterm_uniqueness.
congruence.
SSSCase "~ wfterm e2".
right; intros τ H; inversion H; subst; eapply H2; eauto.
SSCase "forall".
right; intros τ H; inversion H; subst;
  assert (typ_forall τ₁ = typ_arrow t2 τ) by eauto using wfterm_uniqueness;
    congruence.
SCase "~ wfterm e1".
right; intros τ H; inversion H; subst; eapply H1; eauto.
Case "gen".
pick fresh a.
edestruct (H a (a ~ None ++ Γ)) as [[τ H1] | H1]; auto.
left. exists (typ_forall (close_typ_wrt_typ a τ)).
  apply wfterm_gen_exists with (a := a).
  autorewrite with lngen; auto.
  autorewrite with lngen; auto.
right. intros τ H0. inversion H0; subst.
  apply (H1 (open_typ_wrt_typ t (typ_var_f a))).
  apply wfterm_gen_exists_inv; auto.
  assert (a ∉ ftv_typ (typ_forall t)). assert (ftv_typ (typ_forall t) [<=] dom Γ) by eauto; auto. auto.
Case "inst".
destruct (wftyp_dec Γ t1).
SCase "wftyp t1".
edestruct (IHH' Γ) as [[τ H1] | H1]; auto.
SSCase "wfterm e1".
destruct τ.
SSSCase "bound var".
assert (lc_typ (typ_var_b n)) as H by eauto; assert False by inversion H; contradiction.
SSSCase "free var".
right; intros τ H; inversion H; subst;
  assert (typ_var_f t = typ_forall t') by eauto using wfterm_uniqueness;
    congruence.
SSSCase "typ_arrow".
right; intros τ H; inversion H; subst;
  assert (typ_arrow τ1 τ2 = typ_forall t') by eauto using wfterm_uniqueness;
    congruence.
SSSCase "typ_forall".
eauto.
SSCase "~ wfterm e1".
right; intros τ H; inversion H; subst; eapply H1; eauto.
SCase "~wftyp t1".
right; intros τ H; inversion H; subst; eapply n; eauto.
Qed.
