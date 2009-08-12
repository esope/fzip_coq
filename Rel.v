Require Import Utf8.
Require Import Relations.

Parameter A : Type.

Implicit Arguments clos_refl_trans [A].
Implicit Arguments clos_trans [A].
Implicit Arguments transp [A].
Hint Resolve rt_refl rt_trans rt_step.
Hint Resolve t_trans t_step.
Hint Unfold transp.

Definition concat (R1 R2: relation A) x y :=
  ∃ z, R1 x z ∧ R2 z y.
Hint Unfold concat.
Inductive union (R1 R2: relation A) (x y: A): Prop :=
| Left : R1 x y → union R1 R2 x y
| Right : R2 x y → union R1 R2 x y.
Hint Constructors union.
Notation "R ; S" := (concat R S) (at level 30).
Notation "R ∪ S" := (union R S) (at level 30).
Notation "R '⋆'" := (clos_refl_trans R) (at level 29).
Notation "R '⁺'" := (clos_trans R) (at level 29).
Notation "R '⁻¹'" := (transp R) (at level 29).
Notation "R '?'" := (@eq A ∪ R) (at level 29).
Notation "R ⊆ S" := (forall x y, R x y → S x y) (at level 31).
Notation "R ≡ S" := (forall x y, R x y ↔ S x y) (at level 31).

Definition diamond (R: relation A) := (R; R⁻¹) ⊆ (R⁻¹; R).
Definition confluent (R: relation A) := diamond (R⋆).
Definition weakly_confluent (R: relation A) := (R; R⁻¹) ⊆ (R⋆⁻¹; R⋆).
Definition commute (R1 R2: relation A) := (R2 ; R1⁻¹) ⊆ (R1⁻¹ ; R2).
Hint Unfold diamond confluent weakly_confluent commute.

Lemma star_involutive (R: relation A):
  R⋆⋆ ≡ R⋆.
Proof.
intros R x y; split; intro H; induction H; eauto.
Qed.

Lemma plus_involutive (R: relation A):
  R⁺⁺ ≡ R⁺.
Proof.
intros R x y; split; intro H; induction H; eauto.
Qed.

Lemma plus_star_equiv (R: relation A):
  R⋆⁺ ≡ R⁺⋆.
Proof.
intros R x y; split; intro H; induction H; eauto; induction H; eauto.
Qed.

Lemma star_plus_star_equiv (R: relation A):
  R⋆⁺ ≡ R⋆.
Proof.
intros R x y; split; intro H; induction H; eauto.
Qed.

Lemma plus_star_star_equiv (R: relation A):
  R⁺⋆ ≡ R⋆.
Proof.
intros R; split; intros.
rewrite <- plus_star_equiv in *|-; rewrite star_plus_star_equiv in *|-; auto.
rewrite <- plus_star_equiv; rewrite star_plus_star_equiv; auto.
Qed.

Lemma plus_star_concat_equiv (R: relation A):
  R⁺ ≡ R⋆;R.
Proof.
intros R x y; split; intro H.
rewrite tn1_trans_equiv in H; induction H; try rewrite <- tn1_trans_equiv in *|-; eauto.
destruct IHclos_trans_n1 as [? [? ?]].
eauto 6.
destruct H as [? [? ?]]. generalize dependent y.
rewrite rtn1_trans_equiv in H; induction H; try rewrite <- rtn1_trans_equiv in *|-; eauto.
Qed.

Lemma plus_star_included (R: relation A):
  R⁺ ⊆ R⋆.
Proof.
intros R x y H.
induction H; eauto.
Qed.

Lemma concat_assoc (R1 R2 R3: relation A):
  (R1; R2); R3 ≡ R1; (R2; R3).
Proof.
intros R1 R2 R3 x y; split; intro H.
destruct H as [z [Hxz Hzy]].
destruct Hxz as [t [Hxt Htz]]; eauto 6.
destruct H as [z [Hxz [t [Hzt Hty]]]]; eauto 6.
Qed.

Lemma star_equiv (R: relation A):
  R⋆ ≡ R⋆ ; R⋆.
Proof.
intros; split; intro H; eauto.
destruct H as [z [Hxz Hzy]]; eauto.
Qed.

Lemma transp_concat_commute (R1 R2: relation A):
  (R1; R2)⁻¹ ≡ (R2⁻¹; R1⁻¹).
Proof.
intros R1 R2 x y; split; intro H;
destruct H as [z [Hxz Hzy]]; eauto.
Qed.

Lemma commute_sym (R1 R2: relation A):
  commute R1 R2 → commute R2 R1.
Proof.
intros R1 R2 Hcomm.
intros x y H. unfold commute in *.
assert (((R1; R2⁻¹)⁻¹) y x) as H' by auto.
rewrite transp_concat_commute in H'.
assert ((R2; R1 ⁻¹) y x). destruct H' as [? [? ?]]; eauto.
apply Hcomm in H0. destruct H0 as [? [? ?]].
assert ((R2⁻¹) x x0) by auto.
eauto.
Qed.

Lemma commute_star1 (R1 R2:relation A):
  commute R1 R2 → commute (R1⋆) R2.
Proof.
intros R1 R2 Hcomm x y H.
destruct H as [z [Hxz Hyz]].
unfold transp in Hyz.
rewrite rt1n_trans_equiv in Hyz.
generalize dependent x; induction Hyz; intros; eauto.
apply IHHyz in Hxz. destruct Hxz as [? [? ?]].
assert ((R2; R1⁻¹) x1 x) by eauto. apply Hcomm in H2.
destruct H2 as [? [? ?]]; eauto 7.
Qed.

Lemma commute_star2 (R1 R2:relation A):
  commute R1 R2 → commute R1 (R2⋆).
Proof.
intros R1 R2 H.
apply commute_sym. apply commute_sym in H.
auto using commute_star1.
Qed.

Lemma commute_star (R1 R2:relation A):
  commute R1 R2 → commute (R1⋆) (R2⋆).
Proof.
intros R1 R2 H.
auto using commute_star1, commute_star2.
Qed.

Lemma commute_union (R1 R2 R3: relation A):
  commute R1 R2 →
  commute R1 R3 →
  commute R1 (R2 ∪ R3).
Proof.
intros R1 R2 R3 H12 H13 x y H.
destruct H as [z [Hxz Hyz]].
unfold transp in Hyz.
destruct Hxz.
assert ((R2; R1⁻¹) x y) by eauto.
apply H12 in H0.
destruct H0 as [? [? ?]]; eauto.
assert ((R3; R1⁻¹) x y) by eauto.
apply H13 in H0.
destruct H0 as [? [? ?]]; eauto.
Qed.

Lemma confluent_commute_star_refl_equiv (R: relation A):
  confluent R ↔ commute (R⋆) (R⋆).
Proof.
intuition auto.
Qed.

Lemma transp_star_commute (R: relation A):
  R⁻¹⋆ ≡ R⋆⁻¹.
Proof.
intro R. split; intro H.
induction H; unfold transp in *; eauto.
unfold transp in H. induction H; eauto.
Qed.

Lemma transp_plus_commute (R: relation A):
  R⁻¹⁺ ≡ R⁺⁻¹.
Proof.
intro R. split; intro H.
induction H; unfold transp in *; eauto.
unfold transp in H. induction H; eauto.
Qed.

Lemma union_star_equiv (R1 R2: relation A):
  (R1 ∪ R2)⋆ ≡ (R1⋆; R2⋆)⋆.
Proof.
intros R1 R2 x y; split; intro H.
induction H; eauto.
destruct H; apply rt_step; eauto.
induction H; eauto.
destruct H as [z [Hxz Hzy]].
generalize dependent y. induction Hxz; intros; eauto.
apply rt_trans with (y := y); auto.
clear H; induction Hzy; eauto.
induction Hzy; eauto.
Qed.

Lemma concat_star_included1 (R1 R2: relation A):
  R1⋆ ⊆ (R1; R2⋆)⋆.
Proof.
intros R1 R2 x y H.
induction H; eauto.
Qed.

Lemma concat_star_included2 (R1 R2: relation A):
  R2⋆ ⊆ (R1⋆; R2)⋆.
Proof.
intros R1 R2 x y H.
induction H; eauto.
Qed.

Lemma union_star_included1 (R1 R2: relation A):
  R1⋆ ⊆ (R1 ∪ R2)⋆.
Proof.
intros R1 R2 x y H. induction H; eauto.
Qed.

Lemma union_star_included2 (R1 R2: relation A):
  R2⋆ ⊆ (R1 ∪ R2)⋆.
Proof.
intros R1 R2 x y H. induction H; eauto.
Qed.

Lemma union_star_equiv2 (R1 R2: relation A):
  (R1 ∪ R2)⋆ ≡ (R1⋆ ∪ R2⋆)⋆.
Proof.
intros R1 R2 x y; split; intro H; induction H; eauto.
destruct H; eauto.
destruct H; eauto using union_star_included1, union_star_included2.
Qed.

Lemma union_plus_included1 (R1 R2: relation A):
  R1⁺ ⊆ (R1 ∪ R2)⁺.
Proof.
intros R1 R2 x y H. induction H; eauto.
Qed.

Lemma union_plus_included2 (R1 R2: relation A):
  R2⁺ ⊆ (R1 ∪ R2)⁺.
Proof.
intros R1 R2 x y H. induction H; eauto.
Qed.

Lemma union_plus_equiv2 (R1 R2: relation A):
  (R1 ∪ R2)⁺ ≡ (R1⁺ ∪ R2⁺)⁺.
Proof.
intros R1 R2 x y; split; intro H; induction H; eauto.
destruct H; eauto.
destruct H; eauto using union_plus_included1, union_plus_included2.
Qed.

Lemma concat_wf_equiv (R1 R2: relation A):
  well_founded (R1 ; R2) → well_founded (R2 ; R1).
Proof.
intros R1 R2 H.
intro x.
constructor; intros y [z [Hyz _]].
assert (Acc (R1; R2) z) as H0 by auto; clear H.
generalize dependent y.
induction H0; intros.
constructor; intros z [t [Hzt Hty]].
eapply H0; eauto.
Qed.

Lemma wf_plus_equiv (R: relation A):
  well_founded (R⁺) ↔ well_founded R.
Proof.
intro R; split; intros H x.
(* → *)
assert (Acc (R⁺) x) by auto; induction H0.
constructor; intros; eauto.
(* ← *)
constructor.
assert (Acc R x) as H0 by auto; induction H0.
intros y H2; rewrite tn1_trans_equiv in H2; induction H2; constructor; intros.
  eauto.
  rewrite <- tn1_trans_equiv in H3; eauto.
Qed.

Lemma concat_star_equiv (R1 R2: relation A):
  (R1; R2⋆) ≡ (R1; R2⋆) ; R2⋆.
Proof.
intros R1 R2 x y; split; intro H; eauto.
rewrite concat_assoc in H.
destruct H as [z [Hxz Hzy]].
rewrite <- star_equiv in Hzy; eauto.
Qed.

Lemma union_wf (R1 R2: relation A):
  well_founded (R1⋆ ; R2) →
  well_founded (R2⋆ ; R1) →
  well_founded (R1 ∪ R2).
Proof.
intros R1 R2 HR1R2 HR2R1.
assert (well_founded (R1 ; (R2)⋆)) as wfR1R2 by auto using concat_wf_equiv.
assert (well_founded (R2 ; (R1)⋆)) as wfR2R1 by auto using concat_wf_equiv.
intro x.
assert (Acc (R1 ; (R2)⋆) x) as Hx1 by auto; induction Hx1.
assert (Acc (R2 ; (R1)⋆) x) as Hx2 by auto; induction Hx2.
constructor; intros y [Hy | Hy]; eauto.
eapply H2; eauto.
intros z Hz.
eapply H0; eauto. rewrite concat_star_equiv; eauto.
Qed.

Lemma newman (R: relation A):
  well_founded R →
  weakly_confluent R →
  confluent R.
Proof.
intros R Hwf Hwc.
intros y1 y2 [x [Hxy1 Hxy2]]. unfold transp in Hxy2.
rewrite rtn1_trans_equiv in * |-.
assert (Acc R x) by auto.
generalize dependent y1; generalize dependent y2.
induction H; intros.
generalize dependent y2.
induction Hxy1; intros; eauto.
rewrite <- rtn1_trans_equiv in * |-; eauto.
generalize dependent y1; generalize dependent y.
induction Hxy2; intros; eauto.
rewrite <- rtn1_trans_equiv in * |-; eauto 7.
assert (((R ⋆) ⁻¹; R ⋆) y y0) as [x [Hxy Hxy0]] by eauto.
unfold transp in Hxy.
assert (((R ⋆) ⁻¹; R ⋆) x y1) as [t [Htx Hty1]].
  apply (H0 y0); auto.
  rewrite <- rtn1_trans_equiv; auto.
assert (((R ⋆) ⁻¹; R ⋆) y2 x) as [u [Huy2 Hux]].
  apply (H0 y); auto.
  rewrite <- rtn1_trans_equiv; auto.
unfold transp in Htx. unfold transp in Huy2.
assert (((R ⋆) ⁻¹; R ⋆) t u) as [v [Hvt Hvu]].
  eapply H0; eauto.
  rewrite <- rtn1_trans_equiv; eauto.
  rewrite <- rtn1_trans_equiv; eauto.
unfold transp in Hvt; eauto 7.
Qed.

Lemma diamond_union (R1 R2: relation A):
  commute R1 R2 →
  diamond R1 →
  diamond R2 →
  diamond (R1 ∪ R2).
Proof.
intros R1 R2 Hcomm HR1 HR2 x y [z [Hxz Hyz]].
destruct Hxz; destruct Hyz.
  assert ((R1⁻¹; R1) x y) as [? [? ?]] by eauto; eauto 7.
  assert (commute R2 R1) as Hcomm' by auto using commute_sym.
    assert ((R2⁻¹; R1) x y) as [? [? ?]] by eauto; eauto 7.
  assert ((R1⁻¹; R2) x y) as [? [? ?]] by eauto; eauto 7.
  assert ((R2⁻¹; R2) x y) as [? [? ?]] by eauto; eauto 7.
Qed.

Inductive my_rt_clos (R: relation A) : nat → A → A → Prop :=
| my_rt_refl : forall x, my_rt_clos R 0 x x
| my_rt_trans : forall x y z n,
  my_rt_clos R n x y → R y z → my_rt_clos R (1+n) x z.
Hint Constructors my_rt_clos.

Lemma my_rt_clos_equiv (R: relation A) :
  R⋆ ≡ (fun x y => exists n, my_rt_clos R n x y).
Proof.
intros R x y; rewrite rtn1_trans_equiv; split; intro H.
induction H; eauto.
  destruct IHclos_refl_trans_n1; eauto.
destruct H as [n H]; induction H; rewrite <- rtn1_trans_equiv in *; eauto.
Qed.

Require Import Omega.
Lemma my_rt_clos_transitivity (R: relation A) : forall n m x y z,
  my_rt_clos R n x y →
  my_rt_clos R m y z →
  my_rt_clos R (n+m) x z.
Proof.
intro R.
assert (forall n x y z, my_rt_clos R n x y → R y z → my_rt_clos R (1+n) x z).
  intros n x y z Hn; induction Hn; intros; eauto.
intros n m x y z Hn Hm.
generalize dependent x. generalize dependent n.
induction Hm; intros.
replace (n+0) with n by auto; auto.
replace (n0+(1+n)) with (1+(n0+n)) by omega; eauto.
Qed.

Lemma my_rt_clos_0_self (R: relation A) :
  forall x y, my_rt_clos R 0 x y → x = y.
Proof.
intros R x y H.
remember 0 as n.
induction H; auto.
assert False by omega; contradiction.
Qed.

Lemma diamond_confluent (R: relation A) :
  diamond R → confluent R.
Proof.
intros R Hdiamond.
assert (forall p n m x y z, n ≤ p → m ≤ p →
  my_rt_clos R m x z →
  my_rt_clos R n y z →
  exists t, my_rt_clos R n t x ∧ my_rt_clos R m t y).
intro p; induction p; intros n m x y z Hn Hm Hx Hy.
(* case p = 0 *)
assert (n = 0) by omega; assert (m = 0) by omega; subst.
assert (x = z) by eauto using my_rt_clos_0_self;
assert (y = z) by eauto using my_rt_clos_0_self;
subst; eauto.
(* case p > 0 *)
destruct Hx; eauto.
destruct Hy; eauto.
assert ((R⁻¹; R) y y0) as [t [Htx Hty]] by eauto 7.
assert (exists u, my_rt_clos R 1 u x0 ∧ my_rt_clos R n u t) as [u [Hux0 Hut]].
  destruct n.
  (* n = 0 *)
  assert (x0 = y) by eauto using my_rt_clos_0_self; subst.
  replace 1 with (1+0) by reflexivity; eauto.
  (* n > 0 *)
  apply IHp with (z := y); try omega; eauto.
    replace 1 with (1+0) by reflexivity; eauto.
assert (exists v, my_rt_clos R 1 v x ∧ my_rt_clos R n0 v t) as [v [Hvx Hvt]].
  destruct n0.
  (* n0 = 0 *)
  assert (x = y0) by eauto using my_rt_clos_0_self; subst.
  replace 1 with (1+0) by reflexivity; eauto.
  (* n0 > 0 *)
  apply IHp with (z := y0); try omega; eauto.
    replace 1 with (1+0) by reflexivity; eauto.
assert (exists w, my_rt_clos R n0 w u ∧ my_rt_clos R n w v) as [w [Hwu Hwv]].
  apply IHp with (z := t); try omega; eauto.
exists w; split.
replace (1+n) with (n+1) by omega; eauto using my_rt_clos_transitivity.
replace (1+n0) with (n0+1) by omega; eauto using my_rt_clos_transitivity.
(*
            z
           / \
          1   1
         /     \
        y       y0
       / \     / \
      n   1   1   n0
     /     \ /     \
    x0      t       x
     \     / \     /
      1   n   n0  1
       \ /     \ /
        u       v
         \     /
          n0  n
           \ /
            w
*)
intros x y [z [Hxz Hyz]].
unfold transp in Hyz.
rewrite my_rt_clos_equiv in * |-.
destruct Hxz as [n Hxz].
destruct Hyz as [m Hyz].
assert (exists t, my_rt_clos R m t x ∧ my_rt_clos R n t y) as [t [Htx Hty]].
  eapply (H (n+m)); try omega; eauto.
exists t; split; unfold transp; rewrite my_rt_clos_equiv; eauto.
Qed.

Lemma hindley_rosen1 (R1 R2: relation A):
  commute R1 R2 →
  diamond R1 →
  diamond R2 →
  confluent (R1 ∪ R2).
Proof.
intros R1 R2 Hcomm HR1 HR2.
eauto using diamond_confluent, diamond_union.
Qed.

Lemma hindley_rosen2 (R1 R2: relation A):
  commute (R1⋆) (R2⋆) →
  confluent R1 →
  confluent R2 →
  confluent (R1 ∪ R2).
Proof.
intros R1 R2 Hcomm HR1 HR2.
apply hindley_rosen1 in Hcomm; auto.
intros x y [z [Hxz Hyz]].
assert (((R1⋆∪R2⋆)⋆; (R1⋆∪R2⋆)⋆⁻¹) x y).
  unfold transp in Hyz.
  rewrite union_star_equiv2 in * |-.
  eauto.
clear Hxz Hyz z.
apply Hcomm in H.
destruct H as [z [Hzx Hzy]].
unfold transp in Hzx.
rewrite <- union_star_equiv2 in * |-.
eauto.
Qed.

Definition nf (R: relation A) (x: A) :=
  forall y, ~(R y x).
Hint Unfold nf.

(* x is a normal form of y *)
Definition is_nf_of (R: relation A) (x y: A) :=
  nf R x ∧ (R⋆) x y.
Hint Unfold is_nf_of.

Lemma confluent_nf_unique (R: relation A) (x: A):
  confluent R →
  forall y z, is_nf_of R y x → is_nf_of R z x →
    y = z.
Proof.
intros R x H y z Hy Hz.
destruct Hy as [Hy Hyx]; destruct Hz as [Hz Hzx].
assert ((R⋆⁻¹; R⋆) y z) as [t [Hyt Htz]] by eauto.
unfold transp in Hyt.
rewrite rtn1_trans_equiv in *|-.
assert (t = y).
 destruct Hyt; rewrite <- rtn1_trans_equiv in *|-; auto. edestruct Hy; eauto.
assert (t = z).
 destruct Htz; rewrite <- rtn1_trans_equiv in *|-; auto. edestruct Hz; eauto.
congruence.
Qed.

Lemma well_founded_nf_exists (R: relation A) (x: A) :
  well_founded R → exists y, is_nf_of R y x.
Proof.
intros R x Hwf.
assert (Acc R x) as Hacc by auto; induction Hacc.
Require Import Classical.
destruct (classic (exists y, R y x)) as [[y Hy] | ?].
assert (exists z, is_nf_of R z y) as [z [Hyz Hz]] by auto; eauto 7.
eauto 8.
Qed.

(* R1 preserves R2's normal forms *)
Definition preserves_nf (R1 R2: relation A) :=
  forall x y x' y',
    is_nf_of R2 x' x → is_nf_of R2 y' y →
    R1 x y →
    (R1⁺) x' y'.
Hint Unfold preserves_nf.

(*
Lemma akama1 (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  preserves_nf R1 R2 →
  well_founded (R1∪R2).
Proof.
intros R1 R2 Hc1 Hc2 Hwf1 Hwf2 Hnf x.
constructor.
assert (Acc R1 x) as Hacc by auto; induction Hacc.
assert (exists y, nf R2 x y) as [y [Hyx Hy]] by auto using well_founded_nf_exists.
assert (y = x ∨ (R2⁺) y x) as H.
  clear Hy.
  induction Hyx; eauto.
    destruct IHHyx1; destruct IHHyx2; subst; eauto.
clear Hyx; destruct H; subst.



constructor.
assert (Acc R1 x) as Hacc by auto; induction Hacc.
assert (Acc R2 x) as Hacc by auto; induction Hacc.
intros; destruct H3.
constructor; intros; destruct H4; eauto.
constructor; intros; destruct H4; eauto.


Lemma akama2 (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  preserves_nf R1 R2 →
  confluent (R1∪R2).
Proof.
Admitted.
*)

(*
Lemma akama (R1 R2: relation A):
  confluent R1 → confluent R2 →
  well_founded R1 → well_founded R2 →
  preserves_nf R1 R2 →
  confluent (R1∪R2) ∧ well_founded (R1∪R2).
Proof.
intros R1 R2 Hc1 Hc2 Hwf1 Hwf2 Hnf.
assert (forall x, (forall y z, ((R1 ∪ R2) ⋆) y x → ((R1 ∪ R2) ⋆) z x → (((R1 ∪ R2) ⋆) ⁻¹; (R1 ∪ R2) ⋆) y z) ∧ Acc (R1∪R2) x).
intro x.
assert (Acc R2 x) as Hacc by auto; induction Hacc.
assert (Acc R1 x) as Hacc by auto; induction Hacc.
split.
(* proving confluence *)
intros y z Hyz Hzx.
generalize dependent z.
rewrite rtn1_trans_equiv in Hyz; induction Hyz; try rewrite <- rtn1_trans_equiv in *|-; intros; eauto.
generalize dependent z.
rewrite rtn1_trans_equiv in Hyz; induction Hyz; try rewrite <- rtn1_trans_equiv in *|-; intros; eauto.



(* proving well-foundedness *)





split.
intros ? ? [? [? ?]]; edestruct H; eauto.
intros ?; edestruct H; eauto.
Qed.
*)

Lemma commutation_condition (R1 R2: relation A):
  (R1; R2⁻¹) ⊆ (R2⋆⁻¹; R1?) →
  commute (R1⋆) (R2⋆).
Proof.
intros R1 R2 Hcomm1.
assert (R1; R2⋆⁻¹ ⊆ (R2 ⋆) ⁻¹; R1⋆) as Hcomm2.
  intros x y [z [Hxz Hyz]]. unfold transp in Hyz.
  generalize dependent x.
  rewrite rtn1_trans_equiv in Hyz; induction Hyz; try rewrite <- rtn1_trans_equiv in *|-; intros.
   eauto 7.
   assert (((R2 ⋆) ⁻¹; R1 ?) x y0) as [t [Htx Hty0]] by eauto.
   destruct Hty0; subst.
     eauto 6.
     apply IHHyz in H0; destruct H0 as [? [? ?]]; eauto 6.
intros x y [z [Hxz Hyz]].
unfold transp in Hyz.
generalize dependent x; rewrite rtn1_trans_equiv in Hyz; induction Hyz; try rewrite <- rtn1_trans_equiv in *|-; intros; eauto.
assert (((R2 ⋆) ⁻¹; R1 ⋆) y0 x) as [t [Hty0 Htx]] by eauto.
apply IHHyz in Hty0. destruct Hty0 as [? [? ?]].
eauto 6.
Qed.

Definition DPG (R1 R2: relation A) :=
  (R2;R1⁻¹) ⊆ (R1⁺⁻¹;R2⋆).

Lemma commutation_condition_DPG (R1 R2: relation A):
  well_founded R1 → DPG R1 R2 →
  commute (R1⋆) (R2⋆).
Proof.
intros R1 R2 Hwf HDPG y.
rewrite <- wf_plus_equiv in Hwf.
assert (Acc (R1⁺) y) as Hacc by auto; induction Hacc.
rename x into y.
intros z [x [Hyx Hzx]]. unfold transp in Hzx.
generalize dependent z.
rewrite rtn1_trans_equiv in Hyx; induction Hyx; try rewrite <- rtn1_trans_equiv in *|-; intros.
eauto 7.
rewrite rtn1_trans_equiv in Hzx; destruct Hzx; try rewrite <- rtn1_trans_equiv in *|-; eauto.
eauto 7.
assert ((R1⁺⁻¹;R2⋆) y0 y1) as [t [Hty0 Hty1]] by eauto.
unfold transp in Hty0.
assert (((R1 ⋆) ⁻¹; R2 ⋆) y t) as [u [Huy Hut]] by auto using plus_star_included.
unfold transp in Huy.
assert (((R1 ⋆) ⁻¹; R2 ⋆) u z0) as [v [Hvu Hvz0]]; eauto 6.
  apply H0; eauto.
