Add LoadPath "../metatheory".
Require Export STLC_soundness.

Lemma eq_typ_dec : forall (τ₁ τ₂: typ), {τ₁ = τ₂} + {τ₁ ≠ τ₂}.
Proof.
decide equality.
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

Lemma lc_term_dec : forall t, {lc_term t} + {~lc_term t}.
Proof.
assert (forall n t, size_term t ≤ n -> {lc_term t} + {~lc_term t}) as Th.
intro n; induction n; intros t Hsize; destruct t; simpl in *; try solve [absurdity with omega]; auto.
Case "bound var". right; intro H; inversion H.
Case "abs".
  assert (forall x, {lc_term (t0 ^ x)} + {⌉lc_term (t0 ^ x)}) as H.
    intro x; apply IHn; autorewrite with lngen; omega.
  pick fresh x; destruct (H x); [left | right]; eauto using lc_term_abs_exists.
Case "app".
  destruct (IHn t1).
    omega. destruct (IHn t2). omega. auto.
    right; intro H; inversion H; auto.
    right; intro H; inversion H; auto.

intro t; apply (Th (size_term t)); auto.
Qed.

Lemma wfterm_abs_exists : forall x τ Γ e τ',
  x ∉ fv_term e →
  wfterm (x ~ τ ++ Γ) (e ^ x) τ' → wfterm Γ (term_abs τ e) (typ_arrow τ τ').
Proof.
intros x τ Γ e τ' Hx H.
assert (uniq Γ). assert (uniq ([(x, τ)] ++ Γ)) as H1 by eauto. inversion H1; auto.
apply wfterm_abs with (L := {{x}} ∪ dom Γ); intros y Hy. assert (y ≠ x) by auto.
replace (e ^ y) with (subst_term (term_var_f y) x (e ^ x)).
apply wfterm_subst with (τ₂ := τ) (Γ₁ := nil); simpl; simpl_env.
apply wfterm_weakening; simpl_env; eauto.
constructor; eauto.
rewrite subst_term_open_term_wrt_term; auto.
autorewrite with lngen. reflexivity.
Qed.

Lemma wfterm_abs_exists_inv : forall x τ Γ e τ',
  x ∉ fv_term e ∪ dom Γ →
  wfterm Γ (term_abs τ e) (typ_arrow τ τ') →
  wfterm (x ~ τ ++ Γ) (e ^ x) τ'.
Proof.
intros x τ Γ e τ' Hx H.
inversion H; subst. pick fresh y.
assert (wfterm ([(y, τ)] ++ Γ) (e ^ y) τ') by auto.
replace (e ^ x) with (subst_term (term_var_f x) y (e ^ y)).
apply wfterm_subst with (τ₂ := τ) (Γ₁ := nil); simpl; simpl_env.
eauto using wfterm_weakening. constructor; auto.
assert (uniq ([(y, τ)] ++ Γ)) as H1 by eauto; inversion H1; subst; auto.
rewrite subst_term_open_term_wrt_term; auto.
autorewrite with lngen. reflexivity.
Qed.

Lemma wfterm_dec : forall Γ e,
  {τ | wfterm Γ e τ} + {forall τ, ~wfterm Γ e τ}.
Proof.
intros Γ e.
destruct (uniq_dec Γ); eauto.
destruct (lc_term_dec e) as [H | H]; eauto.
assert (lc_set_term e) as H' by auto with lngen; clear H.
generalize dependent Γ. induction H'; intros.
Case "var". destruct (binds_lookup _ x1 Γ) as [[τ H] | H]; eauto.
  right; intros τ H0; inversion H0; subst; eapply H; eauto.
Case "abs". pick fresh x.
edestruct (H x (x ~ t1 ++ Γ)) as [[τ H1] | H1]; auto.
left; eauto using wfterm_abs_exists.
right; intros τ H0; inversion H0; subst; eapply H1; eauto using wfterm_abs_exists_inv.
Case "app".
edestruct (IHH'1 Γ) as [[τ₁ H1] | H1]; auto.
SCase "wfterm e1".
destruct τ₁.
SSCase "typ_base".
right; intros τ H; inversion H; subst;
  assert (typ_base = typ_arrow t2 τ) by eauto using wfterm_uniqueness;
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
SCase "~ wfterm e1".
right; intros τ H; inversion H; subst; eapply H1; eauto.
Qed.
