Add LoadPath "metatheory".
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
Hint Resolve in_dom_dec.

Lemma binds_dec : forall x τ (Γ: typing_env), {binds x τ Γ} + {~binds x τ Γ}.
Proof.
intros x τ Γ. induction Γ; auto.
destruct a as [y τ']; destruct (x == y); subst.
Case "x = y".
destruct (eq_typ_dec τ τ'); subst; auto.
SCase "τ ≠ τ'".
destruct IHΓ; auto.
SSCase "~ binds y τ Γ".
right; intro H; unfold binds in *; simpl in H; destruct H; congruence.
Case "x ≠ y".
destruct IHΓ; [left | right]; auto.
SSCase "~ binds y τ Γ".
intro H; unfold binds in *; simpl in H; destruct H; congruence.
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
  wfterm (x ~ τ ++ Γ) (e ^ x) τ' → wfterm Γ (term_abs τ e) (typ_arrow τ τ').
Proof.
intros x τ Γ e τ' H.
assert (uniq Γ). assert (uniq ([(x, τ)] ++ Γ)) as H1 by eauto. inversion H1; auto.
apply wfterm_abs with (L := {{x}} ∪ dom Γ); intros y Hy. assert (y ≠ x) by auto.
replace (e ^ y) with (subst_term (term_var_f y) x (e ^ x)).
apply wfterm_subst with (τ₂ := τ) (Γ₁ := nil); simpl; simpl_env.
apply wfterm_weakening; simpl_env; eauto.
constructor; eauto.
replace (e ^ y) with (e ^^ (subst_term (term_var_f y) x (term_var_f y))).
(* ICI *)


Lemma wfterm_dec : forall Γ e τ, {wfterm Γ e τ} + {~wfterm Γ e τ}.
Proof.
intros Γ e.
destruct (uniq_dec Γ); eauto.
destruct (lc_term_dec e) as [H | H]; eauto.
assert (lc_set_term e) as H' by auto with lngen; clear H.
generalize dependent Γ. induction H'; intros.
Case "var". destruct (binds_dec x1 τ Γ); auto.
  right; intro H; inversion H; contradiction.
Case "abs".
destruct τ.
SCase "typ_base". right; intro H1; inversion H1.
SCase "typ_arrow". pick fresh x.
destruct (eq_typ_dec t1 τ1); subst.
SSCase "t1 = τ1".
assert ({wfterm (x ~ τ1 ++ Γ) (e1 ^ x) τ2} + {⌉ wfterm (x ~ τ1 ++ Γ) (e1 ^ x) τ2}) as H1 by auto.
destruct H1 as [H1 | H1]; [left | right].
apply wfterm_abs with (L := {{x}}). intros y Hy.

SSCase "t1 ≠ τ1".


