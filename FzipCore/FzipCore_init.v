Add LoadPath "../metatheory".
Require Export Relations.
Require Export FzipCore_inf.
Require Export Utf8.
Require Export Coq.Program.Equality.

(** Notations *)
(*
Notation "[ e2 / x ] e1" := (subst_term e2 x e1) (at level 67).
Notation "[ y → x ] e" := (subst_term (term_var_f y) x e) (at level 67).
*)
Notation "e1 ^^ e2" := (open_term_wrt_term e1 e2) (at level 67).
Notation "e ^ x" := (e ^^ (term_var_f x)).
Notation "e1 '⇝' e2" := (red1 e1 e2) (at level 68).
Notation "e1 '⇝⋆' e2" := (clos_refl_trans _ red1 e1 e2) (at level 68).
Notation "G '⊢' t 'ok'" := (wftyp G t) (at level 67).
Notation "G '⊢' 'ok'" := (wfenv G) (at level 67).
Notation "G '⊢' e ':' t" := (wfterm G e t) (at level 67).
Notation "x '∉' L" := (x `notin` L) (at level 70).
Notation "x '∈' L" := (x `in` L) (at level 70) : set_hs_scope.
Notation "E '∪' F" := (E `union` F) (at level 65, right associativity, format "E '∪' '/' F") : set_hs_scope.

(** Tactics *)
Tactic Notation "absurdity" "with" tactic(tac) :=
  assert False by tac; contradiction.
Ltac absurdity := absurdity with auto.
Ltac size_absurd size t :=
  assert (1 <= size t) by auto with lngen; absurdity with omega.
Ltac size_term_absurd t := size_absurd size_term t.

(** env_map *)
Definition tag_map {A B : Type} (f : A → B) (t : @tag A) :=
  match t with
    | U => U
    | E => E
    | T a => T (f a)
    | Eq a => Eq (f a)
  end.
Hint Unfold tag_map.

Definition env_map {A : Type} (f : typ → A) (env : typing_env) :=
  map (tag_map f) env.
Hint Unfold env_map.

Definition binding_fold {A B : Type} (f : B → A → B)  (acc : B) (b : atom * @tag A) :=
  match b with
    | (_, U) => acc
    | (_, E) => acc
    | (_, T a) => f acc a
    | (_, Eq a) => f acc a
  end.
Hint Unfold binding_fold.

Definition env_fold {A : Type} (f : A → typ → A) (env : typing_env) (acc : A) :=
  fold_left (binding_fold f) env acc.
Hint Unfold env_fold.

Definition ftv_env (G : typing_env) :=
  env_fold (fun acc t => ftv_typ t ∪ acc) G {}.
Hint Unfold ftv_env.

Lemma ftv_env_nil : ftv_env nil [=] {}.
Proof.
reflexivity.
Qed.

Lemma ftv_env_app_aux (G : typing_env) (s : atoms) :
  env_fold (fun acc t => ftv_typ t ∪ acc) G s [=] ftv_env G ∪ s.
Proof.
intros G. induction G; intros; simpl in *.
fsetdec.
destruct a; destruct t;
unfold ftv_env; simpl; repeat rewrite IHG; fsetdec.
Qed.

Lemma ftv_env_app (G1 G2 : typing_env) :
  ftv_env (G1 ++ G2) [=] ftv_env G1 ∪ ftv_env G2.
Proof.
intro G1. induction G1; intros; simpl_env in *.
fsetdec.
destruct a. unfold ftv_env. destruct t; simpl;
repeat rewrite ftv_env_app_aux; rewrite IHG1; fsetdec.
Qed.
Hint Rewrite ftv_env_nil ftv_env_app : lngen.

Lemma tsubst_env_fresh_eq :
forall G t a,
  a ∉ ftv_env G ->
  env_map (tsubst_typ t a) G = G.
Proof.
intros G t a H.
induction G; simpl in *; simpl_env in *.
auto.
autorewrite with lngen in *.
f_equal; auto.
destruct a0; destruct t0; auto.
assert (a ∉ ftv_typ t0). unfold ftv_env in H; simpl in H; auto.
simpl; autorewrite with lngen; auto.
assert (a ∉ ftv_typ t0). unfold ftv_env in H; simpl in H; auto.
simpl; autorewrite with lngen; auto.
Qed.

Definition lc_env Γ :=
  (forall x τ, binds x (T τ) Γ → lc_typ τ) ∧
  (forall a τ, binds a (Eq τ) Γ → lc_typ τ).

Lemma lc_env_app_inv1 Γ Γ' :
  lc_env (Γ ++ Γ') → lc_env Γ.
Proof.
intros Γ Γ' H. destruct H. split; intros; eauto.
Qed.

Lemma lc_env_app_inv2 Γ Γ' :
  lc_env (Γ ++ Γ') → lc_env Γ'.
Proof.
intros Γ Γ' H. destruct H. split; intros; eauto.
Qed.

Lemma lc_env_app Γ Γ' :
  lc_env Γ → lc_env Γ' → lc_env (Γ ++ Γ').
Proof.
intros Γ Γ' H H0. induction Γ; simpl_env in *; auto.
destruct a; destruct t; split; intros;
destruct IHΓ; eauto using lc_env_app_inv2, uniq_app_2.
analyze_binds H1.
  replace t with τ in * by congruence. destruct H. apply (H a); auto.
  apply (H2 x); auto.
  apply (H2 x); auto.
analyze_binds H1.
  apply (H3 a0); auto.
  apply (H3 a0); auto.
analyze_binds H1; apply (H2 x); auto.
analyze_binds H1; apply (H3 a0); auto.
analyze_binds H1; apply (H2 x); auto.
analyze_binds H1; apply (H3 a0); auto.
analyze_binds H1; apply (H2 x); auto.
analyze_binds H1.
  replace t with τ in * by congruence. destruct H. apply (H1 a); auto.
  apply (H3 a0); auto.
  apply (H3 a0); auto.
Qed.

Lemma lc_env_nil : lc_env nil.
Proof.
  split; intros; analyze_binds H.
Qed.

Lemma lc_env_T : forall x τ, lc_typ τ → lc_env (x ~ T τ).
Proof.
intros x τ H. split; intros; analyze_binds H0; congruence.
Qed.

Lemma lc_env_Eq : forall a τ, lc_typ τ → lc_env (a ~ Eq τ).
Proof.
intros x τ H. split; intros; analyze_binds H0; congruence.
Qed.

Lemma lc_env_U : forall a, lc_env (a ~ U).
Proof.
intro a; split; intros; analyze_binds H.
Qed.

Lemma lc_env_E : forall a, lc_env (a ~ E).
Proof.
intro a; split; intros; analyze_binds H.
Qed.

Hint Resolve lc_env_app_inv1 lc_env_app_inv2 lc_env_app
  lc_env_nil lc_env_T lc_env_Eq lc_env_U lc_env_E: lngen.

(** Additional lemmas *)
Lemma var_subst : forall e x, subst_term e x (term_var_f x) = e.
Proof.
intros e x; simpl; destruct (x == x); congruence.
Qed.
Hint Rewrite var_subst : lngen.

Lemma tvar_tsubst : forall t a, tsubst_typ t a (typ_var_f a) = t.
Proof.
intros t a; simpl; destruct (a == a); congruence.
Qed.
Hint Rewrite tvar_tsubst : lngen.

Lemma tsubst_typ_var_twice :
  forall τ a b,
    lc_typ τ →
    a ∉ ftv_typ τ →
    tsubst_typ (typ_var_f b) a (tsubst_typ (typ_var_f a) b τ) = τ.
Proof.
intros τ a b H H0.
induction H; simpl in *; try solve [f_equal; auto].
Case "var". destruct (a0 == b); subst.
SCase "a0 = b". rewrite tvar_tsubst. auto.
SCase "a0 ≠ b". simpl. destruct (a0 == a); subst; auto.
SSCase "a0 = a". simpl in H0. elimtype False; auto.
Case "forall". f_equal. pick fresh c.
  apply open_typ_wrt_typ_inj with (a1 := c); auto.
  assert (ftv_typ (tsubst_typ (typ_var_f b) a (tsubst_typ (typ_var_f a) b t))
    [<=] ftv_typ (typ_var_f b) ∪ remove a (ftv_typ (tsubst_typ (typ_var_f a) b t)))
  by auto with lngen.
  assert (ftv_typ (tsubst_typ (typ_var_f a) b t) [<=] ftv_typ (typ_var_f a) ∪ remove b (ftv_typ t))
    by auto with lngen.
  simpl in *; fsetdec.
  repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto. apply H1.
  assert (ftv_typ (open_typ_wrt_typ t (typ_var_f c)) [<=]
    ftv_typ (typ_var_f c) ∪ ftv_typ t) by auto with lngen.
  simpl in *. fsetdec.
Case "exists". f_equal. pick fresh c.
  apply open_typ_wrt_typ_inj with (a1 := c); auto.
  assert (ftv_typ (tsubst_typ (typ_var_f b) a (tsubst_typ (typ_var_f a) b t))
    [<=] ftv_typ (typ_var_f b) ∪ remove a (ftv_typ (tsubst_typ (typ_var_f a) b t)))
  by auto with lngen.
  assert (ftv_typ (tsubst_typ (typ_var_f a) b t) [<=] ftv_typ (typ_var_f a) ∪ remove b (ftv_typ t))
    by auto with lngen.
  simpl in *; fsetdec.
  repeat rewrite tsubst_typ_open_typ_wrt_typ_var; auto. apply H1.
  assert (ftv_typ (open_typ_wrt_typ t (typ_var_f c)) [<=]
    ftv_typ (typ_var_f c) ∪ ftv_typ t) by auto with lngen.
  simpl in *. fsetdec.
Qed.

Lemma tsubst_typ_lc_typ_inv :
  forall t1 a1 t2,
    lc_typ t1 →
    lc_typ (tsubst_typ t1 a1 t2) →
    lc_typ t2.
Proof.
intros t1 a1.
assert (forall n m t2, size_typ t2 <= n →
  degree_typ_wrt_typ m (tsubst_typ t1 a1 t2) →
  degree_typ_wrt_typ m t2) as H_strong.
  intro n; induction n; intros m t2 H H0;
    destruct t2; simpl in *;
      try solve [absurdity with omega |
      inversion H0; subst; constructor; apply IHn; try omega; auto].
  auto.
intros t2 H H0. eauto with lngen.
Qed.
