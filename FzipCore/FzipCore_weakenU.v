Add LoadPath "../metatheory".
Require Import FzipCore_init.

(** Definition of [weakenU]: weakening with universal variables only *)
Inductive weakenU : typing_env → typing_env → Prop :=
| wUnil : weakenU nil nil
| wUT : forall G1 G2 x t, lc_typ t → x ∉ dom G1 → weakenU G1 G2 →
    weakenU (x ~ T t ++ G1) (x ~ T t ++ G2)
| wUU : forall G1 G2 a, a ∉ dom G1 → weakenU G1 G2 →
    weakenU (a ~ U ++ G1) (a ~ U ++ G2)
| wUE : forall G1 G2 a, a ∉ dom G1 → weakenU G1 G2 →
    weakenU (a ~ E ++ G1) (a ~ E ++ G2)
| wUEq : forall G1 G2 a t, lc_typ t → a ∉ dom G1 → weakenU G1 G2 →
    weakenU (a ~ Eq t ++ G1) (a ~ Eq t ++ G2)
| wUweaken : forall a G1 G2,
    a ∉ dom G1 → weakenU G1 G2 → weakenU (a ~ U ++ G1) G2.
Hint Constructors weakenU.

(** Lemmas about [dom] *)
Lemma weakenU_dom : forall Γ₁ Γ₂, weakenU Γ₁ Γ₂ → dom Γ₂ [<=] dom Γ₁.
Proof.
intros Γ₁ Γ₂ H. induction H; simpl_env; fsetdec.
Qed.

Lemma weakenU_uniq1 : forall Γ₁ Γ₂, weakenU Γ₁ Γ₂ → uniq Γ₁.
Proof.
intros Γ₁ Γ₂ H. induction H; solve_uniq.
Qed.

Lemma weakenU_uniq2 : forall Γ₁ Γ₂, weakenU Γ₁ Γ₂ → uniq Γ₂.
Proof.
intros Γ₁ Γ₂ H. induction H; auto.
assert (dom G2 [<=] dom G1) by eauto using weakenU_dom.
  assert (x ∉ dom G2) by solve_notin. solve_uniq.
assert (dom G2 [<=] dom G1) by eauto using weakenU_dom.
  assert (a ∉ dom G2) by solve_notin. solve_uniq.
assert (dom G2 [<=] dom G1) by eauto using weakenU_dom.
  assert (a ∉ dom G2) by solve_notin. solve_uniq.
assert (dom G2 [<=] dom G1) by eauto using weakenU_dom.
  assert (a ∉ dom G2) by solve_notin. solve_uniq.
Qed.
Hint Resolve weakenU_uniq1 weakenU_uniq2 : lngen.

(** Lemmas about [binds] *)
Lemma bindsT_weakenU1 : forall Γ₁ Γ₂ x τ,
  weakenU Γ₁ Γ₂ → binds x (T τ) Γ₁ → binds x (T τ) Γ₂.
Proof.
intros Γ₁ Γ₂ x τ H H0. induction H; auto; analyze_binds H0; auto.
Qed.

Lemma bindsT_weakenU2 : forall Γ₁ Γ₂ x τ,
  weakenU Γ₁ Γ₂ → binds x (T τ) Γ₂ → binds x (T τ) Γ₁.
Proof.
intros Γ₁ Γ₂ x τ H H0. induction H; auto; analyze_binds H0; auto.
Qed.

Lemma bindsEq_weakenU1 : forall Γ₁ Γ₂ a τ,
  weakenU Γ₁ Γ₂ → binds a (Eq τ) Γ₁ → binds a (Eq τ) Γ₂.
Proof.
intros Γ₁ Γ₂ a τ H H0. induction H; auto; analyze_binds H0; auto.
Qed.

Lemma bindsEq_weakenU2 : forall Γ₁ Γ₂ a τ,
  weakenU Γ₁ Γ₂ → binds a (Eq τ) Γ₂ → binds a (Eq τ) Γ₁.
Proof.
intros Γ₁ Γ₂ a τ H H0. induction H; auto; analyze_binds H0; auto.
Qed.

Lemma bindsE_weakenU1 : forall Γ₁ Γ₂ a,
  weakenU Γ₁ Γ₂ → binds a E Γ₁ → binds a E Γ₂.
Proof.
intros Γ₁ Γ₂ a H H0. induction H; auto; analyze_binds H0; auto.
Qed.

Lemma bindsE_weakenU2 : forall Γ₁ Γ₂ a,
  weakenU Γ₁ Γ₂ → binds a E Γ₂ → binds a E Γ₁.
Proof.
intros Γ₁ Γ₂ a H H0. induction H; auto; analyze_binds H0; auto.
Qed.

Lemma bindsU_weakenU1 : forall Γ₁ Γ₂ a,
  weakenU Γ₁ Γ₂ → binds a U Γ₁ → a ∈ dom Γ₂ → binds a U Γ₂.
Proof.
intros Γ₁ Γ₂ a H H0 H1. induction H; auto; analyze_binds H0; auto.
assert (binds a U G2); auto. apply IHweakenU; auto.
  assert (a ≠ x). intro; subst. eauto with lngen.
  simpl_env in *; fsetdec.
destruct (a0 == a); subst; auto.
  assert (binds a U G2); auto. apply IHweakenU; auto. simpl_env in *; fsetdec.
assert (binds a U G2); auto. apply IHweakenU; auto.
  assert (a ≠ a0). intro; subst. eauto with lngen.
  simpl_env in *; fsetdec.
assert (binds a U G2); auto. apply IHweakenU; auto.
  assert (a ≠ a0). intro; subst. eauto with lngen.
  simpl_env in *; fsetdec.
assert (a0 ∉ dom G2); try contradiction.
  assert (dom G2 [<=] dom G1) by eauto using weakenU_dom. solve_notin.
Qed.

Lemma bindsU_weakenU2 : forall Γ₁ Γ₂ a,
  weakenU Γ₁ Γ₂ → binds a U Γ₂ → binds a U Γ₁.
Proof.
intros Γ₁ Γ₂ a H H0. induction H; auto; analyze_binds H0; auto.
Qed.
Hint Resolve bindsT_weakenU1 bindsT_weakenU2 bindsEq_weakenU1 bindsEq_weakenU2
bindsE_weakenU1 bindsE_weakenU2 bindsU_weakenU1 bindsU_weakenU2 : fzip.

(** [weakenU] is reflexive and transitive *)
Lemma weakenU_refl : forall Γ, uniq Γ → lc_env Γ →
  weakenU Γ Γ.
Proof.
intros Γ H H0. induction Γ; simpl_env in *; auto.
destruct a; destruct t.
constructor. destruct H0; eauto. solve_uniq.
  apply IHΓ. solve_uniq. eauto with lngen.
constructor. solve_uniq.
  apply IHΓ. solve_uniq. eauto with lngen.
constructor. solve_uniq.
  apply IHΓ. solve_uniq. eauto with lngen.
constructor. destruct H0; eauto. solve_uniq.
  apply IHΓ. solve_uniq. eauto with lngen.
Qed.

Lemma weakenU_trans : forall Γ₁ Γ₂ Γ₃,
  weakenU Γ₁ Γ₂ → weakenU Γ₂ Γ₃ → weakenU Γ₁ Γ₃.
Proof.
intros Γ₁ Γ₂ Γ₃ H H0. generalize dependent Γ₃.
induction H; intros; auto.
inversion H2; subst; auto.
inversion H1; subst; auto.
inversion H1; subst; auto.
inversion H2; subst; auto.
Qed.

(** Lemmas about concatenation of environments *)
Lemma weakenU_app : forall Γ₁ Γ₂ Γ₁' Γ₂',
  weakenU Γ₁' Γ₁ → weakenU Γ₂' Γ₂ →
  disjoint Γ₁' Γ₂' → weakenU (Γ₁' ++ Γ₂') (Γ₁ ++ Γ₂).
Proof.
intros Γ₁ Γ₂ Γ₁' Γ₂' H H0 H1. induction H; simpl_env in *; auto;
constructor; auto; try solve [solve_uniq | apply IHweakenU; solve_uniq].
Qed.

Lemma weakenU_app_invE1 : forall Γ₁ Γ₂ Γ₁' Γ₂' a,
  weakenU (Γ₁' ++ a ~ E ++ Γ₂') (Γ₁ ++ a ~ E ++ Γ₂) →
  weakenU Γ₁' Γ₁.
Proof.
intros Γ₁ Γ₂ Γ₁' Γ₂' a H. dependent induction H; auto.
Case "nil". destruct Γ₁'; inversion H.
Case "T". destruct Γ₁'; inversion H2; subst; simpl_env in *; auto.
destruct Γ₁; inversion H3; subst; simpl_env in *; eauto.
Case "U". destruct Γ₁'; inversion H1; subst; simpl_env in *; auto.
destruct Γ₁; inversion H2; subst; simpl_env in *; eauto.
Case "E". destruct Γ₁'; inversion H1; subst; simpl_env in *; auto.
destruct Γ₁; inversion H2; subst; simpl_env in *; eauto.
assert (a0 ∈ dom Γ₂').
  assert (dom (Γ₁ ++ a0 ~ E ++ Γ₂) [<=] dom Γ₂') by eauto using weakenU_dom.
  simpl_env in *. auto.
contradiction.
destruct Γ₁; inversion H2; subst; simpl_env in *; eauto.
assert (a0 ≠ a0) by auto. congruence.
Case "Eq". destruct Γ₁'; inversion H2; subst; simpl_env in *; auto.
destruct Γ₁; inversion H3; subst; simpl_env in *; eauto.
Case "weaken". destruct Γ₁'; inversion H1; subst; simpl_env in *; eauto.
Qed.

Lemma weakenU_app_invE2 : forall Γ₁ Γ₂ Γ₁' Γ₂' a,
  weakenU (Γ₁' ++ a ~ E ++ Γ₂') (Γ₁ ++ a ~ E ++ Γ₂) →
  weakenU Γ₂' Γ₂.
Proof.
intros Γ₁ Γ₂ Γ₁' Γ₂' a H. dependent induction H; auto.
Case "nil". destruct Γ₁'; inversion H.
Case "T". destruct Γ₁'; inversion H2; subst; simpl_env in *; auto.
destruct Γ₁; inversion H3; subst; simpl_env in *; eauto.
Case "U". destruct Γ₁'; inversion H1; subst; simpl_env in *; auto.
destruct Γ₁; inversion H2; subst; simpl_env in *; eauto.
Case "E". destruct Γ₁'; inversion H1; subst; simpl_env in *; auto.
destruct Γ₁; inversion H2; subst; simpl_env in *; eauto.
assert (a0 ∈ dom Γ₂').
  assert (dom (Γ₁ ++ a0 ~ E ++ Γ₂) [<=] dom Γ₂') by eauto using weakenU_dom.
  simpl_env in *. auto.
contradiction.
destruct Γ₁; inversion H2; subst; simpl_env in *; eauto.
assert (a0 ≠ a0) by auto. congruence.
Case "Eq". destruct Γ₁'; inversion H2; subst; simpl_env in *; auto.
destruct Γ₁; inversion H3; subst; simpl_env in *; eauto.
Case "weaken". destruct Γ₁'; inversion H1; subst; simpl_env in *; eauto.
Qed.

