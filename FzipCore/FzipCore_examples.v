Add LoadPath "../metatheory".
Require Import FzipCore_init.
Require Import FzipCore_pure.
Require Import FzipCore_zip.

Ltac simpl_close a :=
  unfold close_typ_wrt_typ; simpl close_typ_wrt_typ_rec;
  unfold close_term_wrt_typ; simpl close_term_wrt_typ_rec;
  unfold close_term_wrt_term; simpl close_term_wrt_term_rec;
  unfold typvar in *; unfold termvar in *;
    destruct (a == a); try congruence.

Ltac simpl_open_typ_wrt_typ :=
  unfold open_typ_wrt_typ; simpl open_typ_wrt_typ_rec.

Ltac simpl_open_term_wrt_typ :=
  unfold open_term_wrt_typ; simpl open_term_wrt_typ_rec.

Ltac simpl_open_term_wrt_term :=
  unfold open_term_wrt_term; simpl open_term_wrt_term_rec.

Ltac simpl_open :=
  simpl_open_typ_wrt_typ; simpl_open_term_wrt_typ; simpl_open_term_wrt_term.

Definition a0: atom. Proof. pick fresh a0. exact a0. Defined.
Definition a1: atom. Proof. pick fresh a1. exact a1. Defined.
Definition a2: atom. Proof. pick fresh a2. exact a2. Defined.
Definition a3: atom. Proof. pick fresh a3. exact a3. Defined.
Definition a4: atom. Proof. pick fresh a4. exact a4. Defined.
Definition a5: atom. Proof. pick fresh a5. exact a5. Defined.
Definition a6: atom. Proof. pick fresh a6. exact a6. Defined.
Definition a7: atom. Proof. pick fresh a7. exact a7. Defined.

Definition x0: atom. Proof. pick fresh x0. exact x0. Defined.
Definition x1: atom. Proof. pick fresh x1. exact x1. Defined.
Definition x2: atom. Proof. pick fresh x2. exact x2. Defined.
Definition x3: atom. Proof. pick fresh x3. exact x3. Defined.
Definition x4: atom. Proof. pick fresh x4. exact x4. Defined.
Definition x5: atom. Proof. pick fresh x5. exact x5. Defined.
Definition x6: atom. Proof. pick fresh x6. exact x6. Defined.
Definition x7: atom. Proof. pick fresh x7. exact x7. Defined.

Definition Abs x t e := term_abs t (close_term_wrt_term x e).
Definition App := term_app.
Definition Gen a e := term_gen (close_term_wrt_typ a e).
Definition Inst := term_inst.
Definition Pair := term_pair.
Definition Fst := term_fst.
Definition Snd := term_snd.
Definition Ex a e := term_exists (close_term_wrt_typ a e).
Definition Open a e := term_open (typ_var_f a) e.
Definition Nu a e := term_nu (close_term_wrt_typ a e).
Definition Sig b a t e := term_sigma (typ_var_f b) t (close_term_wrt_typ a e).
Definition Coerce := term_coerce.

Definition Arrow := typ_arrow.
Definition Prod := typ_prod.
Definition Forall a t := typ_forall (close_typ_wrt_typ a t).
Definition Exists a t := typ_forall (close_typ_wrt_typ a t).

Ltac unfold_smart_cons :=
  unfold Abs; unfold App;
  unfold Gen; unfold Inst;
  unfold Pair; unfold Fst; unfold Snd;
  unfold Ex; unfold Open;
  unfold Nu; unfold Sig; unfold Coerce;
  unfold Arrow; unfold Prod; unfold Forall; unfold Exists.

Ltac unfold_fzip := repeat progress unfold_smart_cons.

Definition term_identity :=
  Gen a1 (Abs x1 (typ_var_f a1) (term_var_f x1)).

Definition typ_identity :=
  Forall a1 (Arrow (typ_var_f a1) (typ_var_f a1)).
Hint Unfold term_identity typ_identity.

Lemma wfterm_identity :
  wfterm nil term_identity typ_identity.
Proof.
unfold typ_identity. unfold term_identity. unfold_fzip.
simpl_close a1. simpl_close x1.
pick fresh b1 and apply wfterm_gen; auto; simpl_open.
pick fresh y1 and apply wfterm_abs; auto with fzip; simpl_open.
auto 7 with fzip.
Qed.

Definition projL_term :=
  Gen a1 (Gen a2 (Abs x1 (Prod (typ_var_f a1) (typ_var_f a2))
    (Fst (term_var_f x1)))).
Definition projL_typ :=
  Forall a1 (Forall a2 (Arrow (Prod (typ_var_f a1) (typ_var_f a2))
    (typ_var_f a1))).

Lemma wfterm_projL : wfterm nil projL_term projL_typ.
Proof.
unfold projL_term. unfold projL_typ.
unfold_fzip. simpl_close x1. simpl_close a2. simpl_close a1.
destruct (a2 == a1); try congruence.