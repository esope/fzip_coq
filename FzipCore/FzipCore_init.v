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
Notation "e1 '⇝[' A ']' e2" := (red1 e1 A e2) (at level 68).
Notation "e1 '⇝⋆[' A ']' e2" :=
  (clos_refl_trans _ (fun x y => red1 x A y) e1 e2) (at level 68).
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

Lemma env_map_app {A : Type} (f : typ → A) (Γ₁ Γ₂ : typing_env) :
env_map f (Γ₁ ++ Γ₂) = env_map f Γ₁ ++ env_map f Γ₂.
Proof.
intros A f Γ₁ Γ₂. unfold env_map. simpl_env. auto.
Qed.

Lemma list_map_id {A : Type} (l : list A) :
  List.map (fun x => x) l = l.
Proof.
intros A l. induction l; simpl; congruence.
Qed.

Lemma env_map_id (env : typing_env) :
  env_map (fun x => x) env = env.
Proof.
intro env. unfold env_map. unfold map. rewrite map_ext with (g := fun x => x).
apply list_map_id.
intros [x a]. destruct a; simpl; auto.
Qed.

Lemma env_map_ext {A : Type} (f g: typ → A):
  (forall a, f a = g a) → forall Γ, env_map f Γ = env_map g Γ.
Proof.
intros A f g H Γ.
unfold env_map. unfold map.
apply map_ext. intros [x a]; destruct a; simpl; congruence.
Qed.

Lemma binds_E_tsubst_inv : forall a Γ b τ,
  binds a E (env_map (tsubst_typ τ b) Γ) → binds a E Γ.
Proof.
intros a Γ b τ H. induction Γ; simpl in *; simpl_env in *; auto.
destruct a0; destruct t; analyze_binds H.
Qed.

Lemma binds_U_tsubst_inv : forall a Γ b τ,
  binds a U (env_map (tsubst_typ τ b) Γ) → binds a U Γ.
Proof.
intros a Γ b τ H. induction Γ; simpl in *; simpl_env in *; auto.
destruct a0; destruct t; analyze_binds H.
Qed.
Hint Resolve binds_E_tsubst_inv binds_U_tsubst_inv: lngen.

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

Lemma ftv_env_binds : forall Γ a,
  a ∈ ftv_env Γ → exists x, exists τ,
    a ∈ ftv_typ τ ∧ (binds x (T τ) Γ ∨ binds x (Eq τ) Γ).
Proof.
intros Γ a H. induction Γ; simpl_env in *.
Case "nil". rewrite ftv_env_nil in H. elimtype False; fsetdec.
Case "cons". destruct a0; destruct t; rewrite ftv_env_app in H;
unfold ftv_env at 1 in H; simpl in H.
SCase "T".
assert (a ∈ ftv_typ t ∨ a ∈ ftv_env Γ) as [? | ?] by fsetdec; eauto 7.
destruct IHΓ as [x [τ [? [? | ?]]]]; eauto 6.
SCase "U". destruct IHΓ as [x [τ [? [? | ?]]]]; eauto 6. fsetdec.
SCase "E". destruct IHΓ as [x [τ [? [? | ?]]]]; eauto 6. fsetdec.
SCase "Eq".
assert (a ∈ ftv_typ t ∨ a ∈ ftv_env Γ) as [? | ?] by fsetdec; eauto 7.
destruct IHΓ as [x [τ [? [? | ?]]]]; eauto 6.
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

Lemma tsubst_typ_var_self : forall τ a,
  tsubst_typ (typ_var_f a) a τ = τ.
Proof.
intros τ a. induction τ; simpl; try congruence.
destruct (t == a); subst; auto.
Qed.

Lemma tsubst_term_var_self : forall e a,
  tsubst_term (typ_var_f a) a e = e.
Proof.
intros e a. induction e; simpl; f_equal; try congruence; auto using tsubst_typ_var_self.
Qed.

Lemma subst_term_var_self : forall e x,
  subst_term (term_var_f x) x e = e.
Proof.
intros e x. induction e; simpl; try congruence.
destruct (t == x); subst; auto.
Qed.

Lemma tsubst_env_var_self : forall Γ a,
  env_map (tsubst_typ (typ_var_f a) a) Γ = Γ.
Proof.
intros Γ a.
rewrite env_map_ext with (g := fun x => x).
apply env_map_id.
intro. apply tsubst_typ_var_self.
Qed.

Lemma degree_typ_wrt_typ_trenaming: forall a1 t1 m t2,
degree_typ_wrt_typ m (tsubst_typ t1 a1 t2) → degree_typ_wrt_typ m t2.
Proof.
intros a1 t1.
assert (forall n m t2, size_typ t2 <= n →
  degree_typ_wrt_typ m (tsubst_typ t1 a1 t2) →
  degree_typ_wrt_typ m t2).
  intro n; induction n; intros m t2 H H0;
    destruct t2; simpl in *;
      try solve [absurdity with omega |
      inversion H0; subst; constructor; apply IHn; try omega; auto].
  auto.
intros. eauto.
Qed.

Lemma degree_term_wrt_typ_trenaming: forall a1 t1 m e1,
degree_term_wrt_typ m (tsubst_term t1 a1 e1) → degree_term_wrt_typ m
e1.
Proof.
intros a1 t1.
assert (forall n m e1, size_term e1 <= n →
  degree_term_wrt_typ m (tsubst_term t1 a1 e1) →
  degree_term_wrt_typ m e1).
  intro n; induction n; intros m e1 H H0;
    destruct e1; simpl in *; try solve
      [absurdity with omega
      | inversion H0; subst; constructor; solve
        [eauto using degree_typ_wrt_typ_trenaming
        | apply IHn; simpl; try omega; auto]].
intros. eauto.
Qed.

Lemma degree_term_wrt_term_trenaming: forall a1 t1 m e1,
degree_term_wrt_term m (tsubst_term t1 a1 e1) → degree_term_wrt_term m
e1.
Proof.
intros a1 t1.
assert (forall n m e1, size_term e1 <= n →
  degree_term_wrt_term m (tsubst_term t1 a1 e1) →
  degree_term_wrt_term m e1).
  intro n; induction n; intros m e1 H H0;
    destruct e1; simpl in *; try solve
      [absurdity with omega
      | inversion H0; subst; constructor;
        apply IHn; simpl; try omega; auto].
  auto.
intros. eauto.
Qed.

Lemma tsubst_typ_lc_typ_inv :
  forall t1 a1 t2,
    lc_typ t1 →
    lc_typ (tsubst_typ t1 a1 t2) →
    lc_typ t2.
Proof.
eauto using degree_typ_wrt_typ_trenaming with lngen.
Qed.

Lemma tsubst_term_lc_term_inv :
  forall t1 a1 e1,
    lc_typ t1 →
    lc_term (tsubst_term t1 a1 e1) →
    lc_term e1.
Proof.
eauto 6 using degree_term_wrt_term_trenaming,
 degree_term_wrt_typ_trenaming with lngen.
Qed.

Lemma binds_decomp : forall (Γ: typing_env) x b,
  binds x b Γ → exists Γ', exists Γ'', Γ = Γ' ++ x ~ b ++ Γ''.
Proof.
intros Γ x b H. induction Γ.
inversion H.
destruct a as [x' b']. analyze_binds H.
exists nil; exists Γ; auto.
destruct IHΓ as [? [? ?]]; auto. subst.
exists (x' ~ b' ++ x0); exists x1; simpl_env; auto.
Qed.

Lemma uniq_app_inv : forall (Γ₁ Γ₂ Γ₁' Γ₂': typing_env) x b,
  Γ₁ ++ x ~ b ++ Γ₂ = Γ₁' ++ x ~ b ++ Γ₂' →
  uniq (Γ₁ ++ x ~ b ++ Γ₂) →
  Γ₁ = Γ₁' ∧ Γ₂ = Γ₂'.
Proof.
intro Γ₁. induction Γ₁; intros; destruct Γ₁'; simpl in *.
split; congruence.
inversion H; subst. elimtype False. solve_uniq.
inversion H; subst. elimtype False. solve_uniq.
inversion H; subst.
destruct (IHΓ₁ Γ₂ Γ₁' Γ₂' x b H3).
simpl_env in *. solve_uniq.
split; congruence.
Qed.

(*
Lemma open_typ_wrt_typ_var_swap_rec : forall t a1 a2 n1 n2,
  n1 < n2 →
  open_typ_wrt_typ_rec n2 (typ_var_f a2)
  (open_typ_wrt_typ_rec n1 (typ_var_f a1) t) =
  open_typ_wrt_typ_rec n1 (typ_var_f a1)
  (open_typ_wrt_typ_rec (S n2) (typ_var_f a2) t).
Proof with try solve [auto | elimtype False; omega].
intros t a1 a2. induction t; intros n1 n2 Hle; simpl; auto;
try solve [f_equal; auto | f_equal; apply IHt; omega].
Case "typ_var_b". destruct (lt_eq_lt_dec n n1). destruct s.
SCase "n < n1". destruct (lt_eq_lt_dec n (S n2))... destruct s... simpl.
destruct (lt_eq_lt_dec n n2)... destruct s...
destruct (lt_eq_lt_dec n n1)... destruct s...
SCase "n = n1". destruct (lt_eq_lt_dec n (S n2))... destruct s... simpl.
destruct (lt_eq_lt_dec n n1)... destruct s...
SCase "n > n1". destruct (lt_eq_lt_dec n (S n2))... destruct s...
SSCase "n < S n2". simpl. destruct (lt_eq_lt_dec (n - 1) n2)... destruct s...
destruct (lt_eq_lt_dec n n1)... destruct s...
SSCase "n = S n2". simpl. destruct (lt_eq_lt_dec (n - 1) n2)... destruct s...
SSCase "S n2 < n". simpl. destruct (lt_eq_lt_dec (n - 1) n2)... destruct s...
destruct (lt_eq_lt_dec (n - 1) n1)... destruct s...
Qed.

Lemma open_term_wrt_term_var_swap_rec : forall e a1 a2 n1 n2,
  n1 < n2 →
  open_term_wrt_typ_rec n2 (typ_var_f a2)
  (open_term_wrt_typ_rec n1 (typ_var_f a1) e) =
  open_term_wrt_typ_rec n1 (typ_var_f a1)
  (open_term_wrt_typ_rec (S n2) (typ_var_f a2) e).
Proof with try solve [auto | elimtype False; omega].
intros e a1 a2. induction e; intros n1 n2 Hle; simpl; auto;
try solve [f_equal; auto using open_typ_wrt_typ_var_swap_rec
  | f_equal; auto using open_typ_wrt_typ_var_swap_rec; apply IHe; omega].
Qed.
*)

Lemma open_typ_wrt_typ_close_typ_wrt_typ_twice : forall a1 a2 a t n,
  open_typ_wrt_typ_rec n (typ_var_f a1)
  (open_typ_wrt_typ_rec (S n) (typ_var_f a2)
    (close_typ_wrt_typ_rec (S n) a t)) =
  open_typ_wrt_typ_rec n (typ_var_f a2)
  (open_typ_wrt_typ_rec (S n) (typ_var_f a1)
    (close_typ_wrt_typ_rec n a t)).
Proof with try solve [auto | elimtype False; omega].
intros a1 a2 a t. induction t; intro; simpl;
try solve [f_equal; auto].
Case "typ_var_b". destruct (lt_ge_dec n n0).
SCase "n < n0". destruct (lt_ge_dec n (S n0))... simpl.
destruct (lt_eq_lt_dec n (S n0))... destruct s... simpl.
destruct (lt_eq_lt_dec n n0)... destruct s...
SCase "n ≥ n0". destruct (lt_ge_dec n (S n0)).
SSCase "n < S n0". simpl.
destruct (lt_eq_lt_dec n (S n0))... destruct s...
destruct (lt_eq_lt_dec n n0)... destruct s... simpl.
destruct (lt_eq_lt_dec n n0)... destruct s...
SSCase "n ≥ S n0". simpl. destruct (lt_eq_lt_dec n n0)... destruct s... simpl.
destruct (lt_eq_lt_dec (n-0) n0)... destruct s...
Case "typ_var_f". destruct (a == t); subst...
simpl. destruct (lt_eq_lt_dec n n)... destruct s... simpl.
destruct (lt_eq_lt_dec n (S n))... destruct s... simpl.
destruct (lt_eq_lt_dec n n)... destruct s...
Qed.

Lemma open_term_wrt_typ_close_term_wrt_typ_twice : forall a1 a2 a e n,
  open_term_wrt_typ_rec n (typ_var_f a1)
  (open_term_wrt_typ_rec (S n) (typ_var_f a2)
    (close_term_wrt_typ_rec (S n) a e)) =
  open_term_wrt_typ_rec n (typ_var_f a2)
  (open_term_wrt_typ_rec (S n) (typ_var_f a1)
    (close_term_wrt_typ_rec n a e)).
Proof.
intros a1 a2 a e. induction e; intro; simpl;
try solve [auto | f_equal; auto using open_typ_wrt_typ_close_typ_wrt_typ_twice].
Qed.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : typing_env => dom x) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  let D2 := gather_atoms_with (fun x => ftv_typ x) in
  let D3 := gather_atoms_with (fun x => ftv_term x) in
  let D4 := gather_atoms_with (fun x => ftv_env x) in
  constr:(A \u B \u C \u D1 \u D2 \u D3 \u D4).

Hint Resolve rt_refl rt_step rt_trans : clos_refl_trans.