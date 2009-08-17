Add LoadPath "../metatheory".
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metatheory.
Require Export LibLNgen.

Require Export F_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  typ_ind' H1 H2 H3 H4 H5.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  typ_rec' H1 H2 H3 H4 H5.

Scheme term_ind' := Induction for term Sort Prop.

Definition term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  term_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme term_rec' := Induction for term Sort Set.

Definition term_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  term_rec' H1 H2 H3 H4 H5 H6 H7.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_typ_wrt_typ_rec (n1 : nat) (a1 : typvar) (t1 : typ) {struct t1} : typ :=
  match t1 with
    | typ_var_f a2 => if (a1 == a2) then (typ_var_b n1) else (typ_var_f a2)
    | typ_var_b n2 => if (lt_ge_dec n2 n1) then (typ_var_b n2) else (typ_var_b (S n2))
    | typ_arrow t2 t3 => typ_arrow (close_typ_wrt_typ_rec n1 a1 t2) (close_typ_wrt_typ_rec n1 a1 t3)
    | typ_forall t2 => typ_forall (close_typ_wrt_typ_rec (S n1) a1 t2)
  end.

Definition close_typ_wrt_typ a1 t1 := close_typ_wrt_typ_rec 0 a1 t1.

Fixpoint close_term_wrt_term_rec (n1 : nat) (x1 : termvar) (e1 : term) {struct e1} : term :=
  match e1 with
    | term_var_f x2 => if (x1 == x2) then (term_var_b n1) else (term_var_f x2)
    | term_var_b n2 => if (lt_ge_dec n2 n1) then (term_var_b n2) else (term_var_b (S n2))
    | term_abs t1 e2 => term_abs t1 (close_term_wrt_term_rec (S n1) x1 e2)
    | term_app e2 e3 => term_app (close_term_wrt_term_rec n1 x1 e2) (close_term_wrt_term_rec n1 x1 e3)
    | term_gen e2 => term_gen (close_term_wrt_term_rec n1 x1 e2)
    | term_inst e2 t1 => term_inst (close_term_wrt_term_rec n1 x1 e2) t1
  end.

Fixpoint close_term_wrt_typ_rec (n1 : nat) (a1 : typvar) (e1 : term) {struct e1} : term :=
  match e1 with
    | term_var_f x1 => term_var_f x1
    | term_var_b n2 => term_var_b n2
    | term_abs t1 e2 => term_abs (close_typ_wrt_typ_rec n1 a1 t1) (close_term_wrt_typ_rec n1 a1 e2)
    | term_app e2 e3 => term_app (close_term_wrt_typ_rec n1 a1 e2) (close_term_wrt_typ_rec n1 a1 e3)
    | term_gen e2 => term_gen (close_term_wrt_typ_rec (S n1) a1 e2)
    | term_inst e2 t1 => term_inst (close_term_wrt_typ_rec n1 a1 e2) (close_typ_wrt_typ_rec n1 a1 t1)
  end.

Definition close_term_wrt_term x1 e1 := close_term_wrt_term_rec 0 x1 e1.

Definition close_term_wrt_typ a1 e1 := close_term_wrt_typ_rec 0 a1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (t1 : typ) {struct t1} : nat :=
  match t1 with
    | typ_var_f a1 => 1
    | typ_var_b n1 => 1
    | typ_arrow t2 t3 => 1 + (size_typ t2) + (size_typ t3)
    | typ_forall t2 => 1 + (size_typ t2)
  end.

Fixpoint size_term (e1 : term) {struct e1} : nat :=
  match e1 with
    | term_var_f x1 => 1
    | term_var_b n1 => 1
    | term_abs t1 e2 => 1 + (size_typ t1) + (size_term e2)
    | term_app e2 e3 => 1 + (size_term e2) + (size_term e3)
    | term_gen e2 => 1 + (size_term e2)
    | term_inst e2 t1 => 1 + (size_term e2) + (size_typ t1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_typ_var_f : forall n1 a1,
    degree_typ_wrt_typ n1 (typ_var_f a1)
  | degree_wrt_typ_typ_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (typ_var_b n2)
  | degree_wrt_typ_typ_arrow : forall n1 t1 t2,
    degree_typ_wrt_typ n1 t1 ->
    degree_typ_wrt_typ n1 t2 ->
    degree_typ_wrt_typ n1 (typ_arrow t1 t2)
  | degree_wrt_typ_typ_forall : forall n1 t1,
    degree_typ_wrt_typ (S n1) t1 ->
    degree_typ_wrt_typ n1 (typ_forall t1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Definition degree_typ_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  degree_typ_wrt_typ_ind' H1 H2 H3 H4 H5.

Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_term_wrt_term : nat -> term -> Prop :=
  | degree_wrt_term_term_var_f : forall n1 x1,
    degree_term_wrt_term n1 (term_var_f x1)
  | degree_wrt_term_term_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_term_wrt_term n1 (term_var_b n2)
  | degree_wrt_term_term_abs : forall n1 t1 e1,
    degree_term_wrt_term (S n1) e1 ->
    degree_term_wrt_term n1 (term_abs t1 e1)
  | degree_wrt_term_term_app : forall n1 e1 e2,
    degree_term_wrt_term n1 e1 ->
    degree_term_wrt_term n1 e2 ->
    degree_term_wrt_term n1 (term_app e1 e2)
  | degree_wrt_term_term_gen : forall n1 e1,
    degree_term_wrt_term n1 e1 ->
    degree_term_wrt_term n1 (term_gen e1)
  | degree_wrt_term_term_inst : forall n1 e1 t1,
    degree_term_wrt_term n1 e1 ->
    degree_term_wrt_term n1 (term_inst e1 t1).

Inductive degree_term_wrt_typ : nat -> term -> Prop :=
  | degree_wrt_typ_term_var_f : forall n1 x1,
    degree_term_wrt_typ n1 (term_var_f x1)
  | degree_wrt_typ_term_var_b : forall n1 n2,
    degree_term_wrt_typ n1 (term_var_b n2)
  | degree_wrt_typ_term_abs : forall n1 t1 e1,
    degree_typ_wrt_typ n1 t1 ->
    degree_term_wrt_typ n1 e1 ->
    degree_term_wrt_typ n1 (term_abs t1 e1)
  | degree_wrt_typ_term_app : forall n1 e1 e2,
    degree_term_wrt_typ n1 e1 ->
    degree_term_wrt_typ n1 e2 ->
    degree_term_wrt_typ n1 (term_app e1 e2)
  | degree_wrt_typ_term_gen : forall n1 e1,
    degree_term_wrt_typ (S n1) e1 ->
    degree_term_wrt_typ n1 (term_gen e1)
  | degree_wrt_typ_term_inst : forall n1 e1 t1,
    degree_term_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 t1 ->
    degree_term_wrt_typ n1 (term_inst e1 t1).

Scheme degree_term_wrt_term_ind' := Induction for degree_term_wrt_term Sort Prop.

Definition degree_term_wrt_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  degree_term_wrt_term_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme degree_term_wrt_typ_ind' := Induction for degree_term_wrt_typ Sort Prop.

Definition degree_term_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  degree_term_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7.

Hint Constructors degree_term_wrt_term : core lngen.

Hint Constructors degree_term_wrt_typ : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_typ_var_f : forall a1,
    lc_set_typ (typ_var_f a1)
  | lc_set_typ_arrow : forall t1 t2,
    lc_set_typ t1 ->
    lc_set_typ t2 ->
    lc_set_typ (typ_arrow t1 t2)
  | lc_set_typ_forall : forall t1,
    (forall a1 : typvar, lc_set_typ (open_typ_wrt_typ t1 (typ_var_f a1))) ->
    lc_set_typ (typ_forall t1).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Definition lc_typ_mutind :=
  fun H1 H2 H3 H4 =>
  lc_typ_ind' H1 H2 H3 H4.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Definition lc_set_typ_mutind :=
  fun H1 H2 H3 H4 =>
  lc_set_typ_ind' H1 H2 H3 H4.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Definition lc_set_typ_mutrec :=
  fun H1 H2 H3 H4 =>
  lc_set_typ_rec' H1 H2 H3 H4.

Hint Constructors lc_typ : core lngen.

Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_term : term -> Set :=
  | lc_set_term_var_f : forall x1,
    lc_set_term (term_var_f x1)
  | lc_set_term_abs : forall t1 e1,
    lc_set_typ t1 ->
    (forall x1 : termvar, lc_set_term (open_term_wrt_term e1 (term_var_f x1))) ->
    lc_set_term (term_abs t1 e1)
  | lc_set_term_app : forall e1 e2,
    lc_set_term e1 ->
    lc_set_term e2 ->
    lc_set_term (term_app e1 e2)
  | lc_set_term_gen : forall e1,
    (forall a1 : typvar, lc_set_term (open_term_wrt_typ e1 (typ_var_f a1))) ->
    lc_set_term (term_gen e1)
  | lc_set_term_inst : forall e1 t1,
    lc_set_term e1 ->
    lc_set_typ t1 ->
    lc_set_term (term_inst e1 t1).

Scheme lc_term_ind' := Induction for lc_term Sort Prop.

Definition lc_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_term_ind' H1 H2 H3 H4 H5 H6.

Scheme lc_set_term_ind' := Induction for lc_set_term Sort Prop.

Definition lc_set_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_set_term_ind' H1 H2 H3 H4 H5 H6.

Scheme lc_set_term_rec' := Induction for lc_set_term Sort Set.

Definition lc_set_term_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  lc_set_term_rec' H1 H2 H3 H4 H5 H6.

Hint Constructors lc_term : core lngen.

Hint Constructors lc_set_term : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ t1 := forall a1, lc_typ (open_typ_wrt_typ t1 (typ_var_f a1)).

Hint Unfold body_typ_wrt_typ.

Definition body_term_wrt_term e1 := forall x1, lc_term (open_term_wrt_term e1 (term_var_f x1)).

Definition body_term_wrt_typ e1 := forall a1, lc_term (open_term_wrt_typ e1 (typ_var_f a1)).

Hint Unfold body_term_wrt_term.

Hint Unfold body_term_wrt_typ.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall t1, 1 <= size_typ t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall t1, 1 <= size_typ t1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_term_min_mutual :
(forall e1, 1 <= size_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_term_min :
forall e1, 1 <= size_term e1.
Proof.
pose proof size_term_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall t1 a1 n1,
  size_typ (close_typ_wrt_typ_rec n1 a1 t1) = size_typ t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall t1 a1 n1,
  size_typ (close_typ_wrt_typ_rec n1 a1 t1) = size_typ t1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_term_close_term_wrt_term_rec_mutual :
(forall e1 x1 n1,
  size_term (close_term_wrt_term_rec n1 x1 e1) = size_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_close_term_wrt_term_rec :
forall e1 x1 n1,
  size_term (close_term_wrt_term_rec n1 x1 e1) = size_term e1.
Proof.
pose proof size_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_close_term_wrt_term_rec : lngen.
Hint Rewrite size_term_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_term_close_term_wrt_typ_rec_mutual :
(forall e1 a1 n1,
  size_term (close_term_wrt_typ_rec n1 a1 e1) = size_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_close_term_wrt_typ_rec :
forall e1 a1 n1,
  size_term (close_term_wrt_typ_rec n1 a1 e1) = size_term e1.
Proof.
pose proof size_term_close_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_close_term_wrt_typ_rec : lngen.
Hint Rewrite size_term_close_term_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall t1 a1,
  size_typ (close_typ_wrt_typ a1 t1) = size_typ t1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_term_close_term_wrt_term :
forall e1 x1,
  size_term (close_term_wrt_term x1 e1) = size_term e1.
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_close_term_wrt_term : lngen.
Hint Rewrite size_term_close_term_wrt_term using solve [auto] : lngen.

Lemma size_term_close_term_wrt_typ :
forall e1 a1,
  size_term (close_term_wrt_typ a1 e1) = size_term e1.
Proof.
unfold close_term_wrt_typ; default_simp.
Qed.

Hint Resolve size_term_close_term_wrt_typ : lngen.
Hint Rewrite size_term_close_term_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall t1 t2 n1,
  size_typ t1 <= size_typ (open_typ_wrt_typ_rec n1 t2 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall t1 t2 n1,
  size_typ t1 <= size_typ (open_typ_wrt_typ_rec n1 t2 t1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_mutual :
(forall e1 e2 n1,
  size_term e1 <= size_term (open_term_wrt_term_rec n1 e2 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec :
forall e1 e2 n1,
  size_term e1 <= size_term (open_term_wrt_term_rec n1 e2 e1).
Proof.
pose proof size_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_open_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_typ_rec_mutual :
(forall e1 t1 n1,
  size_term e1 <= size_term (open_term_wrt_typ_rec n1 t1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_typ_rec :
forall e1 t1 n1,
  size_term e1 <= size_term (open_term_wrt_typ_rec n1 t1 e1).
Proof.
pose proof size_term_open_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_open_term_wrt_typ_rec : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ :
forall t1 t2,
  size_typ t1 <= size_typ (open_typ_wrt_typ t1 t2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_term_open_term_wrt_term :
forall e1 e2,
  size_term e1 <= size_term (open_term_wrt_term e1 e2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_open_term_wrt_term : lngen.

Lemma size_term_open_term_wrt_typ :
forall e1 t1,
  size_term e1 <= size_term (open_term_wrt_typ e1 t1).
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve size_term_open_term_wrt_typ : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall t1 a1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f a1) t1) = size_typ t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall t1 a1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f a1) t1) = size_typ t1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_var_mutual :
(forall e1 x1 n1,
  size_term (open_term_wrt_term_rec n1 (term_var_f x1) e1) = size_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_var :
forall e1 x1 n1,
  size_term (open_term_wrt_term_rec n1 (term_var_f x1) e1) = size_term e1.
Proof.
pose proof size_term_open_term_wrt_term_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_open_term_wrt_term_rec_var : lngen.
Hint Rewrite size_term_open_term_wrt_term_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_typ_rec_var_mutual :
(forall e1 a1 n1,
  size_term (open_term_wrt_typ_rec n1 (typ_var_f a1) e1) = size_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_typ_rec_var :
forall e1 a1 n1,
  size_term (open_term_wrt_typ_rec n1 (typ_var_f a1) e1) = size_term e1.
Proof.
pose proof size_term_open_term_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_open_term_wrt_typ_rec_var : lngen.
Hint Rewrite size_term_open_term_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall t1 a1,
  size_typ (open_typ_wrt_typ t1 (typ_var_f a1)) = size_typ t1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_term_open_term_wrt_term_var :
forall e1 x1,
  size_term (open_term_wrt_term e1 (term_var_f x1)) = size_term e1.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_open_term_wrt_term_var : lngen.
Hint Rewrite size_term_open_term_wrt_term_var using solve [auto] : lngen.

Lemma size_term_open_term_wrt_typ_var :
forall e1 a1,
  size_term (open_term_wrt_typ e1 (typ_var_f a1)) = size_term e1.
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve size_term_open_term_wrt_typ_var : lngen.
Hint Rewrite size_term_open_term_wrt_typ_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 t1,
  degree_typ_wrt_typ n1 t1 ->
  degree_typ_wrt_typ (S n1) t1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 t1,
  degree_typ_wrt_typ n1 t1 ->
  degree_typ_wrt_typ (S n1) t1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_S_mutual :
(forall n1 e1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term (S n1) e1).
Proof.
apply_mutual_ind degree_term_wrt_term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_term_wrt_term_S :
forall n1 e1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term (S n1) e1.
Proof.
pose proof degree_term_wrt_term_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_S : lngen.

(* begin hide *)

Lemma degree_term_wrt_typ_S_mutual :
(forall n1 e1,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind degree_term_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_term_wrt_typ_S :
forall n1 e1,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ (S n1) e1.
Proof.
pose proof degree_term_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_typ_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 t1,
  degree_typ_wrt_typ O t1 ->
  degree_typ_wrt_typ n1 t1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_term_wrt_term_O :
forall n1 e1,
  degree_term_wrt_term O e1 ->
  degree_term_wrt_term n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_O : lngen.

Lemma degree_term_wrt_typ_O :
forall n1 e1,
  degree_term_wrt_typ O e1 ->
  degree_term_wrt_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_term_wrt_typ_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall t1 a1 n1,
  degree_typ_wrt_typ n1 t1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 a1 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall t1 a1 n1,
  degree_typ_wrt_typ n1 t1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 a1 t1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec_mutual :
(forall e1 x1 n1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec :
forall e1 x1 n1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 e1).
Proof.
pose proof degree_term_wrt_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_close_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_typ_rec_mutual :
(forall e1 a1 n1 n2,
  degree_term_wrt_term n2 e1 ->
  degree_term_wrt_term n2 (close_term_wrt_typ_rec n1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_typ_rec :
forall e1 a1 n1 n2,
  degree_term_wrt_term n2 e1 ->
  degree_term_wrt_term n2 (close_term_wrt_typ_rec n1 a1 e1).
Proof.
pose proof degree_term_wrt_term_close_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_close_term_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_close_term_wrt_term_rec_mutual :
(forall e1 x1 n1 n2,
  degree_term_wrt_typ n2 e1 ->
  degree_term_wrt_typ n2 (close_term_wrt_term_rec n1 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_close_term_wrt_term_rec :
forall e1 x1 n1 n2,
  degree_term_wrt_typ n2 e1 ->
  degree_term_wrt_typ n2 (close_term_wrt_term_rec n1 x1 e1).
Proof.
pose proof degree_term_wrt_typ_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_typ_close_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_close_term_wrt_typ_rec_mutual :
(forall e1 a1 n1,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ (S n1) (close_term_wrt_typ_rec n1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_close_term_wrt_typ_rec :
forall e1 a1 n1,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ (S n1) (close_term_wrt_typ_rec n1 a1 e1).
Proof.
pose proof degree_term_wrt_typ_close_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_typ_close_term_wrt_typ_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall t1 a1,
  degree_typ_wrt_typ 0 t1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ a1 t1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_term_wrt_term_close_term_wrt_term :
forall e1 x1,
  degree_term_wrt_term 0 e1 ->
  degree_term_wrt_term 1 (close_term_wrt_term x1 e1).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_close_term_wrt_term : lngen.

Lemma degree_term_wrt_term_close_term_wrt_typ :
forall e1 a1 n1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term n1 (close_term_wrt_typ a1 e1).
Proof.
unfold close_term_wrt_typ; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_close_term_wrt_typ : lngen.

Lemma degree_term_wrt_typ_close_term_wrt_term :
forall e1 x1 n1,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ n1 (close_term_wrt_term x1 e1).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve degree_term_wrt_typ_close_term_wrt_term : lngen.

Lemma degree_term_wrt_typ_close_term_wrt_typ :
forall e1 a1,
  degree_term_wrt_typ 0 e1 ->
  degree_term_wrt_typ 1 (close_term_wrt_typ a1 e1).
Proof.
unfold close_term_wrt_typ; default_simp.
Qed.

Hint Resolve degree_term_wrt_typ_close_term_wrt_typ : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall t1 a1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 a1 t1) ->
  degree_typ_wrt_typ n1 t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall t1 a1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 a1 t1) ->
  degree_typ_wrt_typ n1 t1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec_inv_mutual :
(forall e1 x1 n1,
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 e1) ->
  degree_term_wrt_term n1 e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec_inv :
forall e1 x1 n1,
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 e1) ->
  degree_term_wrt_term n1 e1.
Proof.
pose proof degree_term_wrt_term_close_term_wrt_term_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_term_close_term_wrt_term_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_typ_rec_inv_mutual :
(forall e1 a1 n1 n2,
  degree_term_wrt_term n2 (close_term_wrt_typ_rec n1 a1 e1) ->
  degree_term_wrt_term n2 e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_typ_rec_inv :
forall e1 a1 n1 n2,
  degree_term_wrt_term n2 (close_term_wrt_typ_rec n1 a1 e1) ->
  degree_term_wrt_term n2 e1.
Proof.
pose proof degree_term_wrt_term_close_term_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_term_close_term_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_close_term_wrt_term_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_term_wrt_typ n2 (close_term_wrt_term_rec n1 x1 e1) ->
  degree_term_wrt_typ n2 e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_close_term_wrt_term_rec_inv :
forall e1 x1 n1 n2,
  degree_term_wrt_typ n2 (close_term_wrt_term_rec n1 x1 e1) ->
  degree_term_wrt_typ n2 e1.
Proof.
pose proof degree_term_wrt_typ_close_term_wrt_term_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_typ_close_term_wrt_term_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_close_term_wrt_typ_rec_inv_mutual :
(forall e1 a1 n1,
  degree_term_wrt_typ (S n1) (close_term_wrt_typ_rec n1 a1 e1) ->
  degree_term_wrt_typ n1 e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_close_term_wrt_typ_rec_inv :
forall e1 a1 n1,
  degree_term_wrt_typ (S n1) (close_term_wrt_typ_rec n1 a1 e1) ->
  degree_term_wrt_typ n1 e1.
Proof.
pose proof degree_term_wrt_typ_close_term_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_typ_close_term_wrt_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall t1 a1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ a1 t1) ->
  degree_typ_wrt_typ 0 t1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_term_wrt_term_close_term_wrt_term_inv :
forall e1 x1,
  degree_term_wrt_term 1 (close_term_wrt_term x1 e1) ->
  degree_term_wrt_term 0 e1.
Proof.
unfold close_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_term_close_term_wrt_term_inv : lngen.

Lemma degree_term_wrt_term_close_term_wrt_typ_inv :
forall e1 a1 n1,
  degree_term_wrt_term n1 (close_term_wrt_typ a1 e1) ->
  degree_term_wrt_term n1 e1.
Proof.
unfold close_term_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_term_close_term_wrt_typ_inv : lngen.

Lemma degree_term_wrt_typ_close_term_wrt_term_inv :
forall e1 x1 n1,
  degree_term_wrt_typ n1 (close_term_wrt_term x1 e1) ->
  degree_term_wrt_typ n1 e1.
Proof.
unfold close_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_typ_close_term_wrt_term_inv : lngen.

Lemma degree_term_wrt_typ_close_term_wrt_typ_inv :
forall e1 a1,
  degree_term_wrt_typ 1 (close_term_wrt_typ a1 e1) ->
  degree_term_wrt_typ 0 e1.
Proof.
unfold close_term_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_typ_close_term_wrt_typ_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall t1 t2 n1,
  degree_typ_wrt_typ (S n1) t1 ->
  degree_typ_wrt_typ n1 t2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 t2 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall t1 t2 n1,
  degree_typ_wrt_typ (S n1) t1 ->
  degree_typ_wrt_typ n1 t2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 t2 t1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_mutual :
(forall e1 e2 n1,
  degree_term_wrt_term (S n1) e1 ->
  degree_term_wrt_term n1 e2 ->
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 e2 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec :
forall e1 e2 n1,
  degree_term_wrt_term (S n1) e1 ->
  degree_term_wrt_term n1 e2 ->
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 e2 e1).
Proof.
pose proof degree_term_wrt_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_open_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_typ_rec_mutual :
(forall e1 t1 n1 n2,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term n1 (open_term_wrt_typ_rec n2 t1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_typ_rec :
forall e1 t1 n1 n2,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term n1 (open_term_wrt_typ_rec n2 t1 e1).
Proof.
pose proof degree_term_wrt_term_open_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_open_term_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_open_term_wrt_term_rec_mutual :
(forall e1 e2 n1 n2,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ n1 e2 ->
  degree_term_wrt_typ n1 (open_term_wrt_term_rec n2 e2 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_open_term_wrt_term_rec :
forall e1 e2 n1 n2,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ n1 e2 ->
  degree_term_wrt_typ n1 (open_term_wrt_term_rec n2 e2 e1).
Proof.
pose proof degree_term_wrt_typ_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_typ_open_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_open_term_wrt_typ_rec_mutual :
(forall e1 t1 n1,
  degree_term_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 t1 ->
  degree_term_wrt_typ n1 (open_term_wrt_typ_rec n1 t1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_open_term_wrt_typ_rec :
forall e1 t1 n1,
  degree_term_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 t1 ->
  degree_term_wrt_typ n1 (open_term_wrt_typ_rec n1 t1 e1).
Proof.
pose proof degree_term_wrt_typ_open_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_typ_open_term_wrt_typ_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall t1 t2,
  degree_typ_wrt_typ 1 t1 ->
  degree_typ_wrt_typ 0 t2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ t1 t2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_term_wrt_term_open_term_wrt_term :
forall e1 e2,
  degree_term_wrt_term 1 e1 ->
  degree_term_wrt_term 0 e2 ->
  degree_term_wrt_term 0 (open_term_wrt_term e1 e2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_open_term_wrt_term : lngen.

Lemma degree_term_wrt_term_open_term_wrt_typ :
forall e1 t1 n1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term n1 (open_term_wrt_typ e1 t1).
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_open_term_wrt_typ : lngen.

Lemma degree_term_wrt_typ_open_term_wrt_term :
forall e1 e2 n1,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ n1 e2 ->
  degree_term_wrt_typ n1 (open_term_wrt_term e1 e2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve degree_term_wrt_typ_open_term_wrt_term : lngen.

Lemma degree_term_wrt_typ_open_term_wrt_typ :
forall e1 t1,
  degree_term_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 t1 ->
  degree_term_wrt_typ 0 (open_term_wrt_typ e1 t1).
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve degree_term_wrt_typ_open_term_wrt_typ : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall t1 t2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 t2 t1) ->
  degree_typ_wrt_typ (S n1) t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall t1 t2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 t2 t1) ->
  degree_typ_wrt_typ (S n1) t1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_inv_mutual :
(forall e1 e2 n1,
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 e2 e1) ->
  degree_term_wrt_term (S n1) e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_inv :
forall e1 e2 n1,
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 e2 e1) ->
  degree_term_wrt_term (S n1) e1.
Proof.
pose proof degree_term_wrt_term_open_term_wrt_term_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_term_open_term_wrt_term_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_typ_rec_inv_mutual :
(forall e1 t1 n1 n2,
  degree_term_wrt_term n1 (open_term_wrt_typ_rec n2 t1 e1) ->
  degree_term_wrt_term n1 e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_typ_rec_inv :
forall e1 t1 n1 n2,
  degree_term_wrt_term n1 (open_term_wrt_typ_rec n2 t1 e1) ->
  degree_term_wrt_term n1 e1.
Proof.
pose proof degree_term_wrt_term_open_term_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_term_open_term_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_open_term_wrt_term_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_term_wrt_typ n1 (open_term_wrt_term_rec n2 e2 e1) ->
  degree_term_wrt_typ n1 e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_open_term_wrt_term_rec_inv :
forall e1 e2 n1 n2,
  degree_term_wrt_typ n1 (open_term_wrt_term_rec n2 e2 e1) ->
  degree_term_wrt_typ n1 e1.
Proof.
pose proof degree_term_wrt_typ_open_term_wrt_term_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_typ_open_term_wrt_term_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_open_term_wrt_typ_rec_inv_mutual :
(forall e1 t1 n1,
  degree_term_wrt_typ n1 (open_term_wrt_typ_rec n1 t1 e1) ->
  degree_term_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_typ_open_term_wrt_typ_rec_inv :
forall e1 t1 n1,
  degree_term_wrt_typ n1 (open_term_wrt_typ_rec n1 t1 e1) ->
  degree_term_wrt_typ (S n1) e1.
Proof.
pose proof degree_term_wrt_typ_open_term_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_typ_open_term_wrt_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall t1 t2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ t1 t2) ->
  degree_typ_wrt_typ 1 t1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_term_wrt_term_open_term_wrt_term_inv :
forall e1 e2,
  degree_term_wrt_term 0 (open_term_wrt_term e1 e2) ->
  degree_term_wrt_term 1 e1.
Proof.
unfold open_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_term_open_term_wrt_term_inv : lngen.

Lemma degree_term_wrt_term_open_term_wrt_typ_inv :
forall e1 t1 n1,
  degree_term_wrt_term n1 (open_term_wrt_typ e1 t1) ->
  degree_term_wrt_term n1 e1.
Proof.
unfold open_term_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_term_open_term_wrt_typ_inv : lngen.

Lemma degree_term_wrt_typ_open_term_wrt_term_inv :
forall e1 e2 n1,
  degree_term_wrt_typ n1 (open_term_wrt_term e1 e2) ->
  degree_term_wrt_typ n1 e1.
Proof.
unfold open_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_typ_open_term_wrt_term_inv : lngen.

Lemma degree_term_wrt_typ_open_term_wrt_typ_inv :
forall e1 t1,
  degree_term_wrt_typ 0 (open_term_wrt_typ e1 t1) ->
  degree_term_wrt_typ 1 e1.
Proof.
unfold open_term_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_typ_open_term_wrt_typ_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall t1 t2 a1 n1,
  close_typ_wrt_typ_rec n1 a1 t1 = close_typ_wrt_typ_rec n1 a1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall t1 t2 a1 n1,
  close_typ_wrt_typ_rec n1 a1 t1 = close_typ_wrt_typ_rec n1 a1 t2 ->
  t1 = t2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_term_wrt_term_rec n1 x1 e1 = close_term_wrt_term_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind term_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_inj :
forall e1 e2 x1 n1,
  close_term_wrt_term_rec n1 x1 e1 = close_term_wrt_term_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_term_wrt_term_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_term_wrt_term_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_typ_rec_inj_mutual :
(forall e1 e2 a1 n1,
  close_term_wrt_typ_rec n1 a1 e1 = close_term_wrt_typ_rec n1 a1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind term_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_typ_rec_inj :
forall e1 e2 a1 n1,
  close_term_wrt_typ_rec n1 a1 e1 = close_term_wrt_typ_rec n1 a1 e2 ->
  e1 = e2.
Proof.
pose proof close_term_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_term_wrt_typ_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall t1 t2 a1,
  close_typ_wrt_typ a1 t1 = close_typ_wrt_typ a1 t2 ->
  t1 = t2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_term_wrt_term_inj :
forall e1 e2 x1,
  close_term_wrt_term x1 e1 = close_term_wrt_term x1 e2 ->
  e1 = e2.
Proof.
unfold close_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate close_term_wrt_term_inj : lngen.

Lemma close_term_wrt_typ_inj :
forall e1 e2 a1,
  close_term_wrt_typ a1 e1 = close_term_wrt_typ a1 e2 ->
  e1 = e2.
Proof.
unfold close_term_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_term_wrt_typ_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall t1 a1 n1,
  a1 `notin` ftv_typ t1 ->
  close_typ_wrt_typ_rec n1 a1 (open_typ_wrt_typ_rec n1 (typ_var_f a1) t1) = t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall t1 a1 n1,
  a1 `notin` ftv_typ t1 ->
  close_typ_wrt_typ_rec n1 a1 (open_typ_wrt_typ_rec n1 (typ_var_f a1) t1) = t1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_open_term_wrt_term_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_term e1 ->
  close_term_wrt_term_rec n1 x1 (open_term_wrt_term_rec n1 (term_var_f x1) e1) = e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_open_term_wrt_term_rec :
forall e1 x1 n1,
  x1 `notin` fv_term e1 ->
  close_term_wrt_term_rec n1 x1 (open_term_wrt_term_rec n1 (term_var_f x1) e1) = e1.
Proof.
pose proof close_term_wrt_term_rec_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_term_wrt_term_rec_open_term_wrt_term_rec : lngen.
Hint Rewrite close_term_wrt_term_rec_open_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_typ_rec_open_term_wrt_typ_rec_mutual :
(forall e1 a1 n1,
  a1 `notin` ftv_term e1 ->
  close_term_wrt_typ_rec n1 a1 (open_term_wrt_typ_rec n1 (typ_var_f a1) e1) = e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_typ_rec_open_term_wrt_typ_rec :
forall e1 a1 n1,
  a1 `notin` ftv_term e1 ->
  close_term_wrt_typ_rec n1 a1 (open_term_wrt_typ_rec n1 (typ_var_f a1) e1) = e1.
Proof.
pose proof close_term_wrt_typ_rec_open_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_term_wrt_typ_rec_open_term_wrt_typ_rec : lngen.
Hint Rewrite close_term_wrt_typ_rec_open_term_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall t1 a1,
  a1 `notin` ftv_typ t1 ->
  close_typ_wrt_typ a1 (open_typ_wrt_typ t1 (typ_var_f a1)) = t1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_term_wrt_term_open_term_wrt_term :
forall e1 x1,
  x1 `notin` fv_term e1 ->
  close_term_wrt_term x1 (open_term_wrt_term e1 (term_var_f x1)) = e1.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve close_term_wrt_term_open_term_wrt_term : lngen.
Hint Rewrite close_term_wrt_term_open_term_wrt_term using solve [auto] : lngen.

Lemma close_term_wrt_typ_open_term_wrt_typ :
forall e1 a1,
  a1 `notin` ftv_term e1 ->
  close_term_wrt_typ a1 (open_term_wrt_typ e1 (typ_var_f a1)) = e1.
Proof.
unfold close_term_wrt_typ; unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve close_term_wrt_typ_open_term_wrt_typ : lngen.
Hint Rewrite close_term_wrt_typ_open_term_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall t1 a1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f a1) (close_typ_wrt_typ_rec n1 a1 t1) = t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall t1 a1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f a1) (close_typ_wrt_typ_rec n1 a1 t1) = t1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_close_term_wrt_term_rec_mutual :
(forall e1 x1 n1,
  open_term_wrt_term_rec n1 (term_var_f x1) (close_term_wrt_term_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_close_term_wrt_term_rec :
forall e1 x1 n1,
  open_term_wrt_term_rec n1 (term_var_f x1) (close_term_wrt_term_rec n1 x1 e1) = e1.
Proof.
pose proof open_term_wrt_term_rec_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_term_wrt_term_rec_close_term_wrt_term_rec : lngen.
Hint Rewrite open_term_wrt_term_rec_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_typ_rec_close_term_wrt_typ_rec_mutual :
(forall e1 a1 n1,
  open_term_wrt_typ_rec n1 (typ_var_f a1) (close_term_wrt_typ_rec n1 a1 e1) = e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_typ_rec_close_term_wrt_typ_rec :
forall e1 a1 n1,
  open_term_wrt_typ_rec n1 (typ_var_f a1) (close_term_wrt_typ_rec n1 a1 e1) = e1.
Proof.
pose proof open_term_wrt_typ_rec_close_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_term_wrt_typ_rec_close_term_wrt_typ_rec : lngen.
Hint Rewrite open_term_wrt_typ_rec_close_term_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall t1 a1,
  open_typ_wrt_typ (close_typ_wrt_typ a1 t1) (typ_var_f a1) = t1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_term_wrt_term_close_term_wrt_term :
forall e1 x1,
  open_term_wrt_term (close_term_wrt_term x1 e1) (term_var_f x1) = e1.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve open_term_wrt_term_close_term_wrt_term : lngen.
Hint Rewrite open_term_wrt_term_close_term_wrt_term using solve [auto] : lngen.

Lemma open_term_wrt_typ_close_term_wrt_typ :
forall e1 a1,
  open_term_wrt_typ (close_term_wrt_typ a1 e1) (typ_var_f a1) = e1.
Proof.
unfold close_term_wrt_typ; unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve open_term_wrt_typ_close_term_wrt_typ : lngen.
Hint Rewrite open_term_wrt_typ_close_term_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall t2 t1 a1 n1,
  a1 `notin` ftv_typ t2 ->
  a1 `notin` ftv_typ t1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f a1) t2 = open_typ_wrt_typ_rec n1 (typ_var_f a1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall t2 t1 a1 n1,
  a1 `notin` ftv_typ t2 ->
  a1 `notin` ftv_typ t1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f a1) t2 = open_typ_wrt_typ_rec n1 (typ_var_f a1) t1 ->
  t2 = t1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_term e2 ->
  x1 `notin` fv_term e1 ->
  open_term_wrt_term_rec n1 (term_var_f x1) e2 = open_term_wrt_term_rec n1 (term_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind term_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_term e2 ->
  x1 `notin` fv_term e1 ->
  open_term_wrt_term_rec n1 (term_var_f x1) e2 = open_term_wrt_term_rec n1 (term_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_term_wrt_term_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_term_wrt_term_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_typ_rec_inj_mutual :
(forall e2 e1 a1 n1,
  a1 `notin` ftv_term e2 ->
  a1 `notin` ftv_term e1 ->
  open_term_wrt_typ_rec n1 (typ_var_f a1) e2 = open_term_wrt_typ_rec n1 (typ_var_f a1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind term_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_typ_rec_inj :
forall e2 e1 a1 n1,
  a1 `notin` ftv_term e2 ->
  a1 `notin` ftv_term e1 ->
  open_term_wrt_typ_rec n1 (typ_var_f a1) e2 = open_term_wrt_typ_rec n1 (typ_var_f a1) e1 ->
  e2 = e1.
Proof.
pose proof open_term_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_term_wrt_typ_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall t2 t1 a1,
  a1 `notin` ftv_typ t2 ->
  a1 `notin` ftv_typ t1 ->
  open_typ_wrt_typ t2 (typ_var_f a1) = open_typ_wrt_typ t1 (typ_var_f a1) ->
  t2 = t1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_term_wrt_term_inj :
forall e2 e1 x1,
  x1 `notin` fv_term e2 ->
  x1 `notin` fv_term e1 ->
  open_term_wrt_term e2 (term_var_f x1) = open_term_wrt_term e1 (term_var_f x1) ->
  e2 = e1.
Proof.
unfold open_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate open_term_wrt_term_inj : lngen.

Lemma open_term_wrt_typ_inj :
forall e2 e1 a1,
  a1 `notin` ftv_term e2 ->
  a1 `notin` ftv_term e1 ->
  open_term_wrt_typ e2 (typ_var_f a1) = open_term_wrt_typ e1 (typ_var_f a1) ->
  e2 = e1.
Proof.
unfold open_term_wrt_typ; eauto with lngen.
Qed.

Hint Immediate open_term_wrt_typ_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall t1,
  lc_typ t1 ->
  degree_typ_wrt_typ 0 t1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall t1,
  lc_typ t1 ->
  degree_typ_wrt_typ 0 t1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_of_lc_term_mutual :
(forall e1,
  lc_term e1 ->
  degree_term_wrt_term 0 e1).
Proof.
apply_mutual_ind lc_term_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_term_wrt_term_of_lc_term :
forall e1,
  lc_term e1 ->
  degree_term_wrt_term 0 e1.
Proof.
pose proof degree_term_wrt_term_of_lc_term_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_of_lc_term : lngen.

(* begin hide *)

Lemma degree_term_wrt_typ_of_lc_term_mutual :
(forall e1,
  lc_term e1 ->
  degree_term_wrt_typ 0 e1).
Proof.
apply_mutual_ind lc_term_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_term_wrt_typ_of_lc_term :
forall e1,
  lc_term e1 ->
  degree_term_wrt_typ 0 e1.
Proof.
pose proof degree_term_wrt_typ_of_lc_term_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_typ_of_lc_term : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall t1,
  size_typ t1 = i1 ->
  degree_typ_wrt_typ 0 t1 ->
  lc_typ t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_degree :
forall t1,
  degree_typ_wrt_typ 0 t1 ->
  lc_typ t1.
Proof.
intros t1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ t1));
intuition eauto.
Qed.

Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_term_of_degree_size_mutual :
forall i1,
(forall e1,
  size_term e1 = i1 ->
  degree_term_wrt_term 0 e1 ->
  degree_term_wrt_typ 0 e1 ->
  lc_term e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind term_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_term_of_degree :
forall e1,
  degree_term_wrt_term 0 e1 ->
  degree_term_wrt_typ 0 e1 ->
  lc_term e1.
Proof.
intros e1; intros;
pose proof (lc_term_of_degree_size_mutual (size_term e1));
intuition eauto.
Qed.

Hint Resolve lc_term_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac term_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_term_wrt_term_of_lc_term in J1;
              let J2 := fresh in pose proof H as J2; apply degree_term_wrt_typ_of_lc_term in J2; clear H
          end).

Lemma lc_typ_forall_exists :
forall a1 t1,
  lc_typ (open_typ_wrt_typ t1 (typ_var_f a1)) ->
  lc_typ (typ_forall t1).
Proof.
intros; typ_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_term_abs_exists :
forall x1 t1 e1,
  lc_typ t1 ->
  lc_term (open_term_wrt_term e1 (term_var_f x1)) ->
  lc_term (term_abs t1 e1).
Proof.
intros; term_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_term_gen_exists :
forall a1 e1,
  lc_term (open_term_wrt_typ e1 (typ_var_f a1)) ->
  lc_term (term_gen e1).
Proof.
intros; term_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_typ (typ_forall _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_typ_forall_exists a1).

Hint Extern 1 (lc_term (term_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_term_abs_exists x1).

Hint Extern 1 (lc_term (term_gen _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_term_gen_exists a1).

Lemma lc_body_typ_wrt_typ :
forall t1 t2,
  body_typ_wrt_typ t1 ->
  lc_typ t2 ->
  lc_typ (open_typ_wrt_typ t1 t2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
typ_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_term_wrt_term :
forall e1 e2,
  body_term_wrt_term e1 ->
  lc_term e2 ->
  lc_term (open_term_wrt_term e1 e2).
Proof.
unfold body_term_wrt_term;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
term_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_term_wrt_term : lngen.

Lemma lc_body_term_wrt_typ :
forall e1 t1,
  body_term_wrt_typ e1 ->
  lc_typ t1 ->
  lc_term (open_term_wrt_typ e1 t1).
Proof.
unfold body_term_wrt_typ;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
term_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_term_wrt_typ : lngen.

Lemma lc_body_typ_forall_1 :
forall t1,
  lc_typ (typ_forall t1) ->
  body_typ_wrt_typ t1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_typ_forall_1 : lngen.

Lemma lc_body_term_abs_2 :
forall t1 e1,
  lc_term (term_abs t1 e1) ->
  body_term_wrt_term e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_term_abs_2 : lngen.

Lemma lc_body_term_gen_1 :
forall e1,
  lc_term (term_gen e1) ->
  body_term_wrt_typ e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_term_gen_1 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall t1 (proof2 proof3 : lc_typ t1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall t1 (proof2 proof3 : lc_typ t1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_term_unique_mutual :
(forall e1 (proof2 proof3 : lc_term e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_term_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_term_unique :
forall e1 (proof2 proof3 : lc_term e1), proof2 = proof3.
Proof.
pose proof lc_term_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_term_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall t1, lc_set_typ t1 -> lc_typ t1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall t1, lc_set_typ t1 -> lc_typ t1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_term_of_lc_set_term_mutual :
(forall e1, lc_set_term e1 -> lc_term e1).
Proof.
apply_mutual_ind lc_set_term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_term_of_lc_set_term :
forall e1, lc_set_term e1 -> lc_term e1.
Proof.
pose proof lc_term_of_lc_set_term_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_term_of_lc_set_term : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall t1,
  size_typ t1 = i1 ->
  lc_typ t1 ->
  lc_set_typ t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ];
default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_typ_of_lc_typ :
forall t1,
  lc_typ t1 ->
  lc_set_typ t1.
Proof.
intros t1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ t1));
intuition eauto.
Qed.

Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_term_of_lc_term_size_mutual :
forall i1,
(forall e1,
  size_term e1 = i1 ->
  lc_term e1 ->
  lc_set_term e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind term_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_term_of_lc_term
 | apply lc_set_typ_of_lc_typ];
default_simp; eapply_first_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_term_of_lc_term :
forall e1,
  lc_term e1 ->
  lc_set_term e1.
Proof.
intros e1; intros;
pose proof (lc_set_term_of_lc_term_size_mutual (size_term e1));
intuition eauto.
Qed.

Hint Resolve lc_set_term_of_lc_term : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall t1 a1 n1,
  degree_typ_wrt_typ n1 t1 ->
  a1 `notin` ftv_typ t1 ->
  close_typ_wrt_typ_rec n1 a1 t1 = t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall t1 a1 n1,
  degree_typ_wrt_typ n1 t1 ->
  a1 `notin` ftv_typ t1 ->
  close_typ_wrt_typ_rec n1 a1 t1 = t1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_degree_term_wrt_term_mutual :
(forall e1 x1 n1,
  degree_term_wrt_term n1 e1 ->
  x1 `notin` fv_term e1 ->
  close_term_wrt_term_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_degree_term_wrt_term :
forall e1 x1 n1,
  degree_term_wrt_term n1 e1 ->
  x1 `notin` fv_term e1 ->
  close_term_wrt_term_rec n1 x1 e1 = e1.
Proof.
pose proof close_term_wrt_term_rec_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve close_term_wrt_term_rec_degree_term_wrt_term : lngen.
Hint Rewrite close_term_wrt_term_rec_degree_term_wrt_term using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_typ_rec_degree_term_wrt_typ_mutual :
(forall e1 a1 n1,
  degree_term_wrt_typ n1 e1 ->
  a1 `notin` ftv_term e1 ->
  close_term_wrt_typ_rec n1 a1 e1 = e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_typ_rec_degree_term_wrt_typ :
forall e1 a1 n1,
  degree_term_wrt_typ n1 e1 ->
  a1 `notin` ftv_term e1 ->
  close_term_wrt_typ_rec n1 a1 e1 = e1.
Proof.
pose proof close_term_wrt_typ_rec_degree_term_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_term_wrt_typ_rec_degree_term_wrt_typ : lngen.
Hint Rewrite close_term_wrt_typ_rec_degree_term_wrt_typ using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_lc_typ :
forall t1 a1,
  lc_typ t1 ->
  a1 `notin` ftv_typ t1 ->
  close_typ_wrt_typ a1 t1 = t1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_term_wrt_term_lc_term :
forall e1 x1,
  lc_term e1 ->
  x1 `notin` fv_term e1 ->
  close_term_wrt_term x1 e1 = e1.
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve close_term_wrt_term_lc_term : lngen.
Hint Rewrite close_term_wrt_term_lc_term using solve [auto] : lngen.

Lemma close_term_wrt_typ_lc_term :
forall e1 a1,
  lc_term e1 ->
  a1 `notin` ftv_term e1 ->
  close_term_wrt_typ a1 e1 = e1.
Proof.
unfold close_term_wrt_typ; default_simp.
Qed.

Hint Resolve close_term_wrt_typ_lc_term : lngen.
Hint Rewrite close_term_wrt_typ_lc_term using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall t2 t1 n1,
  degree_typ_wrt_typ n1 t2 ->
  open_typ_wrt_typ_rec n1 t1 t2 = t2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall t2 t1 n1,
  degree_typ_wrt_typ n1 t2 ->
  open_typ_wrt_typ_rec n1 t1 t2 = t2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_degree_term_wrt_term_mutual :
(forall e2 e1 n1,
  degree_term_wrt_term n1 e2 ->
  open_term_wrt_term_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_degree_term_wrt_term :
forall e2 e1 n1,
  degree_term_wrt_term n1 e2 ->
  open_term_wrt_term_rec n1 e1 e2 = e2.
Proof.
pose proof open_term_wrt_term_rec_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve open_term_wrt_term_rec_degree_term_wrt_term : lngen.
Hint Rewrite open_term_wrt_term_rec_degree_term_wrt_term using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_typ_rec_degree_term_wrt_typ_mutual :
(forall e1 t1 n1,
  degree_term_wrt_typ n1 e1 ->
  open_term_wrt_typ_rec n1 t1 e1 = e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_typ_rec_degree_term_wrt_typ :
forall e1 t1 n1,
  degree_term_wrt_typ n1 e1 ->
  open_term_wrt_typ_rec n1 t1 e1 = e1.
Proof.
pose proof open_term_wrt_typ_rec_degree_term_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_term_wrt_typ_rec_degree_term_wrt_typ : lngen.
Hint Rewrite open_term_wrt_typ_rec_degree_term_wrt_typ using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_lc_typ :
forall t2 t1,
  lc_typ t2 ->
  open_typ_wrt_typ t2 t1 = t2.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_term_wrt_term_lc_term :
forall e2 e1,
  lc_term e2 ->
  open_term_wrt_term e2 e1 = e2.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve open_term_wrt_term_lc_term : lngen.
Hint Rewrite open_term_wrt_term_lc_term using solve [auto] : lngen.

Lemma open_term_wrt_typ_lc_term :
forall e1 t1,
  lc_term e1 ->
  open_term_wrt_typ e1 t1 = e1.
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve open_term_wrt_typ_lc_term : lngen.
Hint Rewrite open_term_wrt_typ_lc_term using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftv_typ_close_typ_wrt_typ_rec_mutual :
(forall t1 a1 n1,
  ftv_typ (close_typ_wrt_typ_rec n1 a1 t1) [=] remove a1 (ftv_typ t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_typ_close_typ_wrt_typ_rec :
forall t1 a1 n1,
  ftv_typ (close_typ_wrt_typ_rec n1 a1 t1) [=] remove a1 (ftv_typ t1).
Proof.
pose proof ftv_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite ftv_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_term_close_term_wrt_term_rec_mutual :
(forall e1 x1 n1,
  fv_term (close_term_wrt_term_rec n1 x1 e1) [=] remove x1 (fv_term e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_close_term_wrt_term_rec :
forall e1 x1 n1,
  fv_term (close_term_wrt_term_rec n1 x1 e1) [=] remove x1 (fv_term e1).
Proof.
pose proof fv_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_close_term_wrt_term_rec : lngen.
Hint Rewrite fv_term_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_term_close_term_wrt_typ_rec_mutual :
(forall e1 a1 n1,
  fv_term (close_term_wrt_typ_rec n1 a1 e1) [=] fv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_close_term_wrt_typ_rec :
forall e1 a1 n1,
  fv_term (close_term_wrt_typ_rec n1 a1 e1) [=] fv_term e1.
Proof.
pose proof fv_term_close_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_close_term_wrt_typ_rec : lngen.
Hint Rewrite fv_term_close_term_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_term_close_term_wrt_term_rec_mutual :
(forall e1 x1 n1,
  ftv_term (close_term_wrt_term_rec n1 x1 e1) [=] ftv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_term_close_term_wrt_term_rec :
forall e1 x1 n1,
  ftv_term (close_term_wrt_term_rec n1 x1 e1) [=] ftv_term e1.
Proof.
pose proof ftv_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_close_term_wrt_term_rec : lngen.
Hint Rewrite ftv_term_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_term_close_term_wrt_typ_rec_mutual :
(forall e1 a1 n1,
  ftv_term (close_term_wrt_typ_rec n1 a1 e1) [=] remove a1 (ftv_term e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_term_close_term_wrt_typ_rec :
forall e1 a1 n1,
  ftv_term (close_term_wrt_typ_rec n1 a1 e1) [=] remove a1 (ftv_term e1).
Proof.
pose proof ftv_term_close_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_close_term_wrt_typ_rec : lngen.
Hint Rewrite ftv_term_close_term_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftv_typ_close_typ_wrt_typ :
forall t1 a1,
  ftv_typ (close_typ_wrt_typ a1 t1) [=] remove a1 (ftv_typ t1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve ftv_typ_close_typ_wrt_typ : lngen.
Hint Rewrite ftv_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma fv_term_close_term_wrt_term :
forall e1 x1,
  fv_term (close_term_wrt_term x1 e1) [=] remove x1 (fv_term e1).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_close_term_wrt_term : lngen.
Hint Rewrite fv_term_close_term_wrt_term using solve [auto] : lngen.

Lemma fv_term_close_term_wrt_typ :
forall e1 a1,
  fv_term (close_term_wrt_typ a1 e1) [=] fv_term e1.
Proof.
unfold close_term_wrt_typ; default_simp.
Qed.

Hint Resolve fv_term_close_term_wrt_typ : lngen.
Hint Rewrite fv_term_close_term_wrt_typ using solve [auto] : lngen.

Lemma ftv_term_close_term_wrt_term :
forall e1 x1,
  ftv_term (close_term_wrt_term x1 e1) [=] ftv_term e1.
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve ftv_term_close_term_wrt_term : lngen.
Hint Rewrite ftv_term_close_term_wrt_term using solve [auto] : lngen.

Lemma ftv_term_close_term_wrt_typ :
forall e1 a1,
  ftv_term (close_term_wrt_typ a1 e1) [=] remove a1 (ftv_term e1).
Proof.
unfold close_term_wrt_typ; default_simp.
Qed.

Hint Resolve ftv_term_close_term_wrt_typ : lngen.
Hint Rewrite ftv_term_close_term_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall t1 t2 n1,
  ftv_typ t1 [<=] ftv_typ (open_typ_wrt_typ_rec n1 t2 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_typ_open_typ_wrt_typ_rec_lower :
forall t1 t2 n1,
  ftv_typ t1 [<=] ftv_typ (open_typ_wrt_typ_rec n1 t2 t1).
Proof.
pose proof ftv_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_lower_mutual :
(forall e1 e2 n1,
  fv_term e1 [<=] fv_term (open_term_wrt_term_rec n1 e2 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_lower :
forall e1 e2 n1,
  fv_term e1 [<=] fv_term (open_term_wrt_term_rec n1 e2 e1).
Proof.
pose proof fv_term_open_term_wrt_term_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_open_term_wrt_term_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_typ_rec_lower_mutual :
(forall e1 t1 n1,
  fv_term e1 [<=] fv_term (open_term_wrt_typ_rec n1 t1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_typ_rec_lower :
forall e1 t1 n1,
  fv_term e1 [<=] fv_term (open_term_wrt_typ_rec n1 t1 e1).
Proof.
pose proof fv_term_open_term_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_open_term_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_term_open_term_wrt_term_rec_lower_mutual :
(forall e1 e2 n1,
  ftv_term e1 [<=] ftv_term (open_term_wrt_term_rec n1 e2 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_term_open_term_wrt_term_rec_lower :
forall e1 e2 n1,
  ftv_term e1 [<=] ftv_term (open_term_wrt_term_rec n1 e2 e1).
Proof.
pose proof ftv_term_open_term_wrt_term_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_open_term_wrt_term_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_term_open_term_wrt_typ_rec_lower_mutual :
(forall e1 t1 n1,
  ftv_term e1 [<=] ftv_term (open_term_wrt_typ_rec n1 t1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_term_open_term_wrt_typ_rec_lower :
forall e1 t1 n1,
  ftv_term e1 [<=] ftv_term (open_term_wrt_typ_rec n1 t1 e1).
Proof.
pose proof ftv_term_open_term_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_open_term_wrt_typ_rec_lower : lngen.

(* end hide *)

Lemma ftv_typ_open_typ_wrt_typ_lower :
forall t1 t2,
  ftv_typ t1 [<=] ftv_typ (open_typ_wrt_typ t1 t2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve ftv_typ_open_typ_wrt_typ_lower : lngen.

Lemma fv_term_open_term_wrt_term_lower :
forall e1 e2,
  fv_term e1 [<=] fv_term (open_term_wrt_term e1 e2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_open_term_wrt_term_lower : lngen.

Lemma fv_term_open_term_wrt_typ_lower :
forall e1 t1,
  fv_term e1 [<=] fv_term (open_term_wrt_typ e1 t1).
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve fv_term_open_term_wrt_typ_lower : lngen.

Lemma ftv_term_open_term_wrt_term_lower :
forall e1 e2,
  ftv_term e1 [<=] ftv_term (open_term_wrt_term e1 e2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve ftv_term_open_term_wrt_term_lower : lngen.

Lemma ftv_term_open_term_wrt_typ_lower :
forall e1 t1,
  ftv_term e1 [<=] ftv_term (open_term_wrt_typ e1 t1).
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve ftv_term_open_term_wrt_typ_lower : lngen.

(* begin hide *)

Lemma ftv_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall t1 t2 n1,
  ftv_typ (open_typ_wrt_typ_rec n1 t2 t1) [<=] ftv_typ t2 `union` ftv_typ t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_typ_open_typ_wrt_typ_rec_upper :
forall t1 t2 n1,
  ftv_typ (open_typ_wrt_typ_rec n1 t2 t1) [<=] ftv_typ t2 `union` ftv_typ t1.
Proof.
pose proof ftv_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_upper_mutual :
(forall e1 e2 n1,
  fv_term (open_term_wrt_term_rec n1 e2 e1) [<=] fv_term e2 `union` fv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_upper :
forall e1 e2 n1,
  fv_term (open_term_wrt_term_rec n1 e2 e1) [<=] fv_term e2 `union` fv_term e1.
Proof.
pose proof fv_term_open_term_wrt_term_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_open_term_wrt_term_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_typ_rec_upper_mutual :
(forall e1 t1 n1,
  fv_term (open_term_wrt_typ_rec n1 t1 e1) [<=] fv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_typ_rec_upper :
forall e1 t1 n1,
  fv_term (open_term_wrt_typ_rec n1 t1 e1) [<=] fv_term e1.
Proof.
pose proof fv_term_open_term_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_open_term_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_term_open_term_wrt_term_rec_upper_mutual :
(forall e1 e2 n1,
  ftv_term (open_term_wrt_term_rec n1 e2 e1) [<=] ftv_term e2 `union` ftv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_term_open_term_wrt_term_rec_upper :
forall e1 e2 n1,
  ftv_term (open_term_wrt_term_rec n1 e2 e1) [<=] ftv_term e2 `union` ftv_term e1.
Proof.
pose proof ftv_term_open_term_wrt_term_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_open_term_wrt_term_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_term_open_term_wrt_typ_rec_upper_mutual :
(forall e1 t1 n1,
  ftv_term (open_term_wrt_typ_rec n1 t1 e1) [<=] ftv_typ t1 `union` ftv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_term_open_term_wrt_typ_rec_upper :
forall e1 t1 n1,
  ftv_term (open_term_wrt_typ_rec n1 t1 e1) [<=] ftv_typ t1 `union` ftv_term e1.
Proof.
pose proof ftv_term_open_term_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_open_term_wrt_typ_rec_upper : lngen.

(* end hide *)

Lemma ftv_typ_open_typ_wrt_typ_upper :
forall t1 t2,
  ftv_typ (open_typ_wrt_typ t1 t2) [<=] ftv_typ t2 `union` ftv_typ t1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve ftv_typ_open_typ_wrt_typ_upper : lngen.

Lemma fv_term_open_term_wrt_term_upper :
forall e1 e2,
  fv_term (open_term_wrt_term e1 e2) [<=] fv_term e2 `union` fv_term e1.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_open_term_wrt_term_upper : lngen.

Lemma fv_term_open_term_wrt_typ_upper :
forall e1 t1,
  fv_term (open_term_wrt_typ e1 t1) [<=] fv_term e1.
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve fv_term_open_term_wrt_typ_upper : lngen.

Lemma ftv_term_open_term_wrt_term_upper :
forall e1 e2,
  ftv_term (open_term_wrt_term e1 e2) [<=] ftv_term e2 `union` ftv_term e1.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve ftv_term_open_term_wrt_term_upper : lngen.

Lemma ftv_term_open_term_wrt_typ_upper :
forall e1 t1,
  ftv_term (open_term_wrt_typ e1 t1) [<=] ftv_typ t1 `union` ftv_term e1.
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve ftv_term_open_term_wrt_typ_upper : lngen.

(* begin hide *)

Lemma ftv_typ_tsubst_typ_fresh_mutual :
(forall t1 t2 a1,
  a1 `notin` ftv_typ t1 ->
  ftv_typ (tsubst_typ t2 a1 t1) [=] ftv_typ t1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_typ_tsubst_typ_fresh :
forall t1 t2 a1,
  a1 `notin` ftv_typ t1 ->
  ftv_typ (tsubst_typ t2 a1 t1) [=] ftv_typ t1.
Proof.
pose proof ftv_typ_tsubst_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_typ_tsubst_typ_fresh : lngen.
Hint Rewrite ftv_typ_tsubst_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_term_subst_term_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_term e1 ->
  fv_term (subst_term e2 x1 e1) [=] fv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_fresh :
forall e1 e2 x1,
  x1 `notin` fv_term e1 ->
  fv_term (subst_term e2 x1 e1) [=] fv_term e1.
Proof.
pose proof fv_term_subst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_fresh : lngen.
Hint Rewrite fv_term_subst_term_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_term_subst_term_fresh_mutual :
(forall e1 t1 a1,
  fv_term (tsubst_term t1 a1 e1) [=] fv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_term_subst_term_fresh :
forall e1 t1 a1,
  fv_term (tsubst_term t1 a1 e1) [=] fv_term e1.
Proof.
pose proof ftv_term_subst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_subst_term_fresh : lngen.
Hint Rewrite ftv_term_subst_term_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_term_tsubst_term_fresh_mutual :
(forall e1 t1 a1,
  a1 `notin` ftv_term e1 ->
  ftv_term (tsubst_term t1 a1 e1) [=] ftv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_term_tsubst_term_fresh :
forall e1 t1 a1,
  a1 `notin` ftv_term e1 ->
  ftv_term (tsubst_term t1 a1 e1) [=] ftv_term e1.
Proof.
pose proof ftv_term_tsubst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_tsubst_term_fresh : lngen.
Hint Rewrite ftv_term_tsubst_term_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_typ_tsubst_typ_lower_mutual :
(forall t1 t2 a1,
  remove a1 (ftv_typ t1) [<=] ftv_typ (tsubst_typ t2 a1 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_typ_tsubst_typ_lower :
forall t1 t2 a1,
  remove a1 (ftv_typ t1) [<=] ftv_typ (tsubst_typ t2 a1 t1).
Proof.
pose proof ftv_typ_tsubst_typ_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_typ_tsubst_typ_lower : lngen.

(* begin hide *)

Lemma fv_term_subst_term_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_term e1) [<=] fv_term (subst_term e2 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_lower :
forall e1 e2 x1,
  remove x1 (fv_term e1) [<=] fv_term (subst_term e2 x1 e1).
Proof.
pose proof fv_term_subst_term_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_lower : lngen.

(* begin hide *)

Lemma fv_term_tsubst_term_lower_mutual :
(forall e1 t1 a1,
  fv_term e1 [<=] fv_term (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_tsubst_term_lower :
forall e1 t1 a1,
  fv_term e1 [<=] fv_term (tsubst_term t1 a1 e1).
Proof.
pose proof fv_term_tsubst_term_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_tsubst_term_lower : lngen.

(* begin hide *)

Lemma ftv_term_subst_term_lower_mutual :
(forall e1 e2 x1,
  ftv_term e1 [<=] ftv_term (subst_term e2 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_term_subst_term_lower :
forall e1 e2 x1,
  ftv_term e1 [<=] ftv_term (subst_term e2 x1 e1).
Proof.
pose proof ftv_term_subst_term_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_subst_term_lower : lngen.

(* begin hide *)

Lemma ftv_term_tsubst_term_lower_mutual :
(forall e1 t1 a1,
  remove a1 (ftv_term e1) [<=] ftv_term (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_term_tsubst_term_lower :
forall e1 t1 a1,
  remove a1 (ftv_term e1) [<=] ftv_term (tsubst_term t1 a1 e1).
Proof.
pose proof ftv_term_tsubst_term_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_tsubst_term_lower : lngen.

(* begin hide *)

Lemma ftv_typ_tsubst_typ_notin_mutual :
(forall t1 t2 a1 a2,
  a2 `notin` ftv_typ t1 ->
  a2 `notin` ftv_typ t2 ->
  a2 `notin` ftv_typ (tsubst_typ t2 a1 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_typ_tsubst_typ_notin :
forall t1 t2 a1 a2,
  a2 `notin` ftv_typ t1 ->
  a2 `notin` ftv_typ t2 ->
  a2 `notin` ftv_typ (tsubst_typ t2 a1 t1).
Proof.
pose proof ftv_typ_tsubst_typ_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_typ_tsubst_typ_notin : lngen.

(* begin hide *)

Lemma fv_term_subst_term_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_term e1 ->
  x2 `notin` fv_term e2 ->
  x2 `notin` fv_term (subst_term e2 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_term e1 ->
  x2 `notin` fv_term e2 ->
  x2 `notin` fv_term (subst_term e2 x1 e1).
Proof.
pose proof fv_term_subst_term_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_notin : lngen.

(* begin hide *)

Lemma fv_term_tsubst_term_notin_mutual :
(forall e1 t1 a1 x1,
  x1 `notin` fv_term e1 ->
  x1 `notin` fv_term (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_tsubst_term_notin :
forall e1 t1 a1 x1,
  x1 `notin` fv_term e1 ->
  x1 `notin` fv_term (tsubst_term t1 a1 e1).
Proof.
pose proof fv_term_tsubst_term_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_tsubst_term_notin : lngen.

(* begin hide *)

Lemma ftv_term_subst_term_notin_mutual :
(forall e1 e2 x1 a1,
  a1 `notin` ftv_term e1 ->
  a1 `notin` ftv_term e2 ->
  a1 `notin` ftv_term (subst_term e2 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_term_subst_term_notin :
forall e1 e2 x1 a1,
  a1 `notin` ftv_term e1 ->
  a1 `notin` ftv_term e2 ->
  a1 `notin` ftv_term (subst_term e2 x1 e1).
Proof.
pose proof ftv_term_subst_term_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_subst_term_notin : lngen.

(* begin hide *)

Lemma ftv_term_tsubst_term_notin_mutual :
(forall e1 t1 a1 a2,
  a2 `notin` ftv_term e1 ->
  a2 `notin` ftv_typ t1 ->
  a2 `notin` ftv_term (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_term_tsubst_term_notin :
forall e1 t1 a1 a2,
  a2 `notin` ftv_term e1 ->
  a2 `notin` ftv_typ t1 ->
  a2 `notin` ftv_term (tsubst_term t1 a1 e1).
Proof.
pose proof ftv_term_tsubst_term_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_tsubst_term_notin : lngen.

(* begin hide *)

Lemma ftv_typ_tsubst_typ_upper_mutual :
(forall t1 t2 a1,
  ftv_typ (tsubst_typ t2 a1 t1) [<=] ftv_typ t2 `union` remove a1 (ftv_typ t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_typ_tsubst_typ_upper :
forall t1 t2 a1,
  ftv_typ (tsubst_typ t2 a1 t1) [<=] ftv_typ t2 `union` remove a1 (ftv_typ t1).
Proof.
pose proof ftv_typ_tsubst_typ_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_typ_tsubst_typ_upper : lngen.

(* begin hide *)

Lemma fv_term_subst_term_upper_mutual :
(forall e1 e2 x1,
  fv_term (subst_term e2 x1 e1) [<=] fv_term e2 `union` remove x1 (fv_term e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_upper :
forall e1 e2 x1,
  fv_term (subst_term e2 x1 e1) [<=] fv_term e2 `union` remove x1 (fv_term e1).
Proof.
pose proof fv_term_subst_term_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_upper : lngen.

(* begin hide *)

Lemma fv_term_tsubst_term_upper_mutual :
(forall e1 t1 a1,
  fv_term (tsubst_term t1 a1 e1) [<=] fv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_tsubst_term_upper :
forall e1 t1 a1,
  fv_term (tsubst_term t1 a1 e1) [<=] fv_term e1.
Proof.
pose proof fv_term_tsubst_term_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_tsubst_term_upper : lngen.

(* begin hide *)

Lemma ftv_term_subst_term_upper_mutual :
(forall e1 e2 x1,
  ftv_term (subst_term e2 x1 e1) [<=] ftv_term e2 `union` ftv_term e1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_term_subst_term_upper :
forall e1 e2 x1,
  ftv_term (subst_term e2 x1 e1) [<=] ftv_term e2 `union` ftv_term e1.
Proof.
pose proof ftv_term_subst_term_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_subst_term_upper : lngen.

(* begin hide *)

Lemma ftv_term_tsubst_term_upper_mutual :
(forall e1 t1 a1,
  ftv_term (tsubst_term t1 a1 e1) [<=] ftv_typ t1 `union` remove a1 (ftv_term e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_term_tsubst_term_upper :
forall e1 t1 a1,
  ftv_term (tsubst_term t1 a1 e1) [<=] ftv_typ t1 `union` remove a1 (ftv_term e1).
Proof.
pose proof ftv_term_tsubst_term_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve ftv_term_tsubst_term_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma tsubst_typ_close_typ_wrt_typ_rec_mutual :
(forall t2 t1 a1 a2 n1,
  degree_typ_wrt_typ n1 t1 ->
  a1 <> a2 ->
  a2 `notin` ftv_typ t1 ->
  tsubst_typ t1 a1 (close_typ_wrt_typ_rec n1 a2 t2) = close_typ_wrt_typ_rec n1 a2 (tsubst_typ t1 a1 t2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_close_typ_wrt_typ_rec :
forall t2 t1 a1 a2 n1,
  degree_typ_wrt_typ n1 t1 ->
  a1 <> a2 ->
  a2 `notin` ftv_typ t1 ->
  tsubst_typ t1 a1 (close_typ_wrt_typ_rec n1 a2 t2) = close_typ_wrt_typ_rec n1 a2 (tsubst_typ t1 a1 t2).
Proof.
pose proof tsubst_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_term_wrt_term n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_term e1 ->
  subst_term e1 x1 (close_term_wrt_term_rec n1 x2 e2) = close_term_wrt_term_rec n1 x2 (subst_term e1 x1 e2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_close_term_wrt_term_rec :
forall e2 e1 x1 x2 n1,
  degree_term_wrt_term n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_term e1 ->
  subst_term e1 x1 (close_term_wrt_term_rec n1 x2 e2) = close_term_wrt_term_rec n1 x2 (subst_term e1 x1 e2).
Proof.
pose proof subst_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_close_term_wrt_term_rec : lngen.

(* begin hide *)

Lemma subst_term_close_term_wrt_typ_rec_mutual :
(forall e2 e1 a1 x1 n1,
  degree_term_wrt_typ n1 e1 ->
  x1 `notin` ftv_term e1 ->
  subst_term e1 a1 (close_term_wrt_typ_rec n1 x1 e2) = close_term_wrt_typ_rec n1 x1 (subst_term e1 a1 e2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_close_term_wrt_typ_rec :
forall e2 e1 a1 x1 n1,
  degree_term_wrt_typ n1 e1 ->
  x1 `notin` ftv_term e1 ->
  subst_term e1 a1 (close_term_wrt_typ_rec n1 x1 e2) = close_term_wrt_typ_rec n1 x1 (subst_term e1 a1 e2).
Proof.
pose proof subst_term_close_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_close_term_wrt_typ_rec : lngen.

(* begin hide *)

Lemma tsubst_term_close_term_wrt_term_rec_mutual :
(forall e1 t1 x1 a1 n1,
  tsubst_term t1 x1 (close_term_wrt_term_rec n1 a1 e1) = close_term_wrt_term_rec n1 a1 (tsubst_term t1 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_close_term_wrt_term_rec :
forall e1 t1 x1 a1 n1,
  tsubst_term t1 x1 (close_term_wrt_term_rec n1 a1 e1) = close_term_wrt_term_rec n1 a1 (tsubst_term t1 x1 e1).
Proof.
pose proof tsubst_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_close_term_wrt_term_rec : lngen.

(* begin hide *)

Lemma tsubst_term_close_term_wrt_typ_rec_mutual :
(forall e1 t1 a1 a2 n1,
  degree_typ_wrt_typ n1 t1 ->
  a1 <> a2 ->
  a2 `notin` ftv_typ t1 ->
  tsubst_term t1 a1 (close_term_wrt_typ_rec n1 a2 e1) = close_term_wrt_typ_rec n1 a2 (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_close_term_wrt_typ_rec :
forall e1 t1 a1 a2 n1,
  degree_typ_wrt_typ n1 t1 ->
  a1 <> a2 ->
  a2 `notin` ftv_typ t1 ->
  tsubst_term t1 a1 (close_term_wrt_typ_rec n1 a2 e1) = close_term_wrt_typ_rec n1 a2 (tsubst_term t1 a1 e1).
Proof.
pose proof tsubst_term_close_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_close_term_wrt_typ_rec : lngen.

Lemma tsubst_typ_close_typ_wrt_typ :
forall t2 t1 a1 a2,
  lc_typ t1 ->  a1 <> a2 ->
  a2 `notin` ftv_typ t1 ->
  tsubst_typ t1 a1 (close_typ_wrt_typ a2 t2) = close_typ_wrt_typ a2 (tsubst_typ t1 a1 t2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_typ_close_typ_wrt_typ : lngen.

Lemma subst_term_close_term_wrt_term :
forall e2 e1 x1 x2,
  lc_term e1 ->  x1 <> x2 ->
  x2 `notin` fv_term e1 ->
  subst_term e1 x1 (close_term_wrt_term x2 e2) = close_term_wrt_term x2 (subst_term e1 x1 e2).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_close_term_wrt_term : lngen.

Lemma subst_term_close_term_wrt_typ :
forall e2 e1 a1 x1,
  lc_term e1 ->  x1 `notin` ftv_term e1 ->
  subst_term e1 a1 (close_term_wrt_typ x1 e2) = close_term_wrt_typ x1 (subst_term e1 a1 e2).
Proof.
unfold close_term_wrt_typ; default_simp.
Qed.

Hint Resolve subst_term_close_term_wrt_typ : lngen.

Lemma tsubst_term_close_term_wrt_term :
forall e1 t1 x1 a1,
  lc_typ t1 ->  tsubst_term t1 x1 (close_term_wrt_term a1 e1) = close_term_wrt_term a1 (tsubst_term t1 x1 e1).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve tsubst_term_close_term_wrt_term : lngen.

Lemma tsubst_term_close_term_wrt_typ :
forall e1 t1 a1 a2,
  lc_typ t1 ->  a1 <> a2 ->
  a2 `notin` ftv_typ t1 ->
  tsubst_term t1 a1 (close_term_wrt_typ a2 e1) = close_term_wrt_typ a2 (tsubst_term t1 a1 e1).
Proof.
unfold close_term_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_term_close_term_wrt_typ : lngen.

(* begin hide *)

Lemma tsubst_typ_degree_typ_wrt_typ_mutual :
(forall t1 t2 a1 n1,
  degree_typ_wrt_typ n1 t1 ->
  degree_typ_wrt_typ n1 t2 ->
  degree_typ_wrt_typ n1 (tsubst_typ t2 a1 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_degree_typ_wrt_typ :
forall t1 t2 a1 n1,
  degree_typ_wrt_typ n1 t1 ->
  degree_typ_wrt_typ n1 t2 ->
  degree_typ_wrt_typ n1 (tsubst_typ t2 a1 t1).
Proof.
pose proof tsubst_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma subst_term_degree_term_wrt_term_mutual :
(forall e1 e2 x1 n1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term n1 e2 ->
  degree_term_wrt_term n1 (subst_term e2 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_degree_term_wrt_term :
forall e1 e2 x1 n1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term n1 e2 ->
  degree_term_wrt_term n1 (subst_term e2 x1 e1).
Proof.
pose proof subst_term_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_degree_term_wrt_term : lngen.

(* begin hide *)

Lemma subst_term_degree_term_wrt_typ_mutual :
(forall e1 e2 x1 n1,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ n1 e2 ->
  degree_term_wrt_typ n1 (subst_term e2 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_degree_term_wrt_typ :
forall e1 e2 x1 n1,
  degree_term_wrt_typ n1 e1 ->
  degree_term_wrt_typ n1 e2 ->
  degree_term_wrt_typ n1 (subst_term e2 x1 e1).
Proof.
pose proof subst_term_degree_term_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_degree_term_wrt_typ : lngen.

(* begin hide *)

Lemma tsubst_term_degree_term_wrt_term_mutual :
(forall e1 t1 a1 n1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term n1 (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_degree_term_wrt_term :
forall e1 t1 a1 n1,
  degree_term_wrt_term n1 e1 ->
  degree_term_wrt_term n1 (tsubst_term t1 a1 e1).
Proof.
pose proof tsubst_term_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_degree_term_wrt_term : lngen.

(* begin hide *)

Lemma tsubst_term_degree_term_wrt_typ_mutual :
(forall e1 t1 a1 n1,
  degree_term_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 t1 ->
  degree_term_wrt_typ n1 (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_degree_term_wrt_typ :
forall e1 t1 a1 n1,
  degree_term_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 t1 ->
  degree_term_wrt_typ n1 (tsubst_term t1 a1 e1).
Proof.
pose proof tsubst_term_degree_term_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_degree_term_wrt_typ : lngen.

(* begin hide *)

Lemma tsubst_typ_fresh_eq_mutual :
(forall t2 t1 a1,
  a1 `notin` ftv_typ t2 ->
  tsubst_typ t1 a1 t2 = t2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_fresh_eq :
forall t2 t1 a1,
  a1 `notin` ftv_typ t2 ->
  tsubst_typ t1 a1 t2 = t2.
Proof.
pose proof tsubst_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_fresh_eq : lngen.
Hint Rewrite tsubst_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_term_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_term e2 ->
  subst_term e1 x1 e2 = e2).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_term e2 ->
  subst_term e1 x1 e2 = e2.
Proof.
pose proof subst_term_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh_eq : lngen.
Hint Rewrite subst_term_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_term_fresh_eq_mutual :
(forall e1 t1 a1,
  a1 `notin` ftv_term e1 ->
  tsubst_term t1 a1 e1 = e1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_fresh_eq :
forall e1 t1 a1,
  a1 `notin` ftv_term e1 ->
  tsubst_term t1 a1 e1 = e1.
Proof.
pose proof tsubst_term_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_fresh_eq : lngen.
Hint Rewrite tsubst_term_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_typ_fresh_same_mutual :
(forall t2 t1 a1,
  a1 `notin` ftv_typ t1 ->
  a1 `notin` ftv_typ (tsubst_typ t1 a1 t2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_fresh_same :
forall t2 t1 a1,
  a1 `notin` ftv_typ t1 ->
  a1 `notin` ftv_typ (tsubst_typ t1 a1 t2).
Proof.
pose proof tsubst_typ_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_fresh_same : lngen.
Hint Rewrite tsubst_typ_fresh_same using solve [auto] : lngen.

(* begin hide *)

Lemma subst_term_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_term e1 ->
  x1 `notin` fv_term (subst_term e1 x1 e2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_term e1 ->
  x1 `notin` fv_term (subst_term e1 x1 e2).
Proof.
pose proof subst_term_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh_same : lngen.
Hint Rewrite subst_term_fresh_same using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_term_fresh_same_mutual :
(forall e1 t1 a1,
  a1 `notin` ftv_typ t1 ->
  a1 `notin` ftv_term (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_fresh_same :
forall e1 t1 a1,
  a1 `notin` ftv_typ t1 ->
  a1 `notin` ftv_term (tsubst_term t1 a1 e1).
Proof.
pose proof tsubst_term_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_fresh_same : lngen.
Hint Rewrite tsubst_term_fresh_same using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_typ_fresh_mutual :
(forall t2 t1 a1 a2,
  a1 `notin` ftv_typ t2 ->
  a1 `notin` ftv_typ t1 ->
  a1 `notin` ftv_typ (tsubst_typ t1 a2 t2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_fresh :
forall t2 t1 a1 a2,
  a1 `notin` ftv_typ t2 ->
  a1 `notin` ftv_typ t1 ->
  a1 `notin` ftv_typ (tsubst_typ t1 a2 t2).
Proof.
pose proof tsubst_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_fresh : lngen.
Hint Rewrite tsubst_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma subst_term_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_term e2 ->
  x1 `notin` fv_term e1 ->
  x1 `notin` fv_term (subst_term e1 x2 e2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_term e2 ->
  x1 `notin` fv_term e1 ->
  x1 `notin` fv_term (subst_term e1 x2 e2).
Proof.
pose proof subst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh : lngen.
Hint Rewrite subst_term_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_term_fresh_mutual :
(forall e1 t1 a1 a2,
  a1 `notin` ftv_term e1 ->
  a1 `notin` ftv_typ t1 ->
  a1 `notin` ftv_term (tsubst_term t1 a2 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_fresh :
forall e1 t1 a1 a2,
  a1 `notin` ftv_term e1 ->
  a1 `notin` ftv_typ t1 ->
  a1 `notin` ftv_term (tsubst_term t1 a2 e1).
Proof.
pose proof tsubst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_fresh : lngen.
Hint Rewrite tsubst_term_fresh using solve [auto] : lngen.

Lemma tsubst_typ_lc_typ :
forall t1 t2 a1,
  lc_typ t1 ->
  lc_typ t2 ->
  lc_typ (tsubst_typ t2 a1 t1).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_typ_lc_typ : lngen.

Lemma subst_term_lc_term :
forall e1 e2 x1,
  lc_term e1 ->
  lc_term e2 ->
  lc_term (subst_term e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_lc_term : lngen.

Lemma tsubst_term_lc_term :
forall e1 t1 a1,
  lc_term e1 ->
  lc_typ t1 ->
  lc_term (tsubst_term t1 a1 e1).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_term_lc_term : lngen.

(* begin hide *)

Lemma tsubst_typ_open_typ_wrt_typ_rec_mutual :
(forall t3 t1 t2 a1 n1,
  lc_typ t1 ->
  tsubst_typ t1 a1 (open_typ_wrt_typ_rec n1 t2 t3) = open_typ_wrt_typ_rec n1 (tsubst_typ t1 a1 t2) (tsubst_typ t1 a1 t3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_typ_open_typ_wrt_typ_rec :
forall t3 t1 t2 a1 n1,
  lc_typ t1 ->
  tsubst_typ t1 a1 (open_typ_wrt_typ_rec n1 t2 t3) = open_typ_wrt_typ_rec n1 (tsubst_typ t1 a1 t2) (tsubst_typ t1 a1 t3).
Proof.
pose proof tsubst_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_term_open_term_wrt_term_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_term e1 ->
  subst_term e1 x1 (open_term_wrt_term_rec n1 e2 e3) = open_term_wrt_term_rec n1 (subst_term e1 x1 e2) (subst_term e1 x1 e3)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_open_term_wrt_term_rec :
forall e3 e1 e2 x1 n1,
  lc_term e1 ->
  subst_term e1 x1 (open_term_wrt_term_rec n1 e2 e3) = open_term_wrt_term_rec n1 (subst_term e1 x1 e2) (subst_term e1 x1 e3).
Proof.
pose proof subst_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_open_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_term_open_term_wrt_typ_rec_mutual :
(forall e2 e1 t1 x1 n1,
  lc_term e1 ->
  subst_term e1 x1 (open_term_wrt_typ_rec n1 t1 e2) = open_term_wrt_typ_rec n1 t1 (subst_term e1 x1 e2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_open_term_wrt_typ_rec :
forall e2 e1 t1 x1 n1,
  lc_term e1 ->
  subst_term e1 x1 (open_term_wrt_typ_rec n1 t1 e2) = open_term_wrt_typ_rec n1 t1 (subst_term e1 x1 e2).
Proof.
pose proof subst_term_open_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_open_term_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_open_term_wrt_term_rec_mutual :
(forall e2 t1 e1 a1 n1,
  tsubst_term t1 a1 (open_term_wrt_term_rec n1 e1 e2) = open_term_wrt_term_rec n1 (tsubst_term t1 a1 e1) (tsubst_term t1 a1 e2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_open_term_wrt_term_rec :
forall e2 t1 e1 a1 n1,
  tsubst_term t1 a1 (open_term_wrt_term_rec n1 e1 e2) = open_term_wrt_term_rec n1 (tsubst_term t1 a1 e1) (tsubst_term t1 a1 e2).
Proof.
pose proof tsubst_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_open_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_open_term_wrt_typ_rec_mutual :
(forall e1 t1 t2 a1 n1,
  lc_typ t1 ->
  tsubst_term t1 a1 (open_term_wrt_typ_rec n1 t2 e1) = open_term_wrt_typ_rec n1 (tsubst_typ t1 a1 t2) (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_open_term_wrt_typ_rec :
forall e1 t1 t2 a1 n1,
  lc_typ t1 ->
  tsubst_term t1 a1 (open_term_wrt_typ_rec n1 t2 e1) = open_term_wrt_typ_rec n1 (tsubst_typ t1 a1 t2) (tsubst_term t1 a1 e1).
Proof.
pose proof tsubst_term_open_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_open_term_wrt_typ_rec : lngen.

(* end hide *)

Lemma tsubst_typ_open_typ_wrt_typ :
forall t3 t1 t2 a1,
  lc_typ t1 ->
  tsubst_typ t1 a1 (open_typ_wrt_typ t3 t2) = open_typ_wrt_typ (tsubst_typ t1 a1 t3) (tsubst_typ t1 a1 t2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_typ_open_typ_wrt_typ : lngen.

Lemma subst_term_open_term_wrt_term :
forall e3 e1 e2 x1,
  lc_term e1 ->
  subst_term e1 x1 (open_term_wrt_term e3 e2) = open_term_wrt_term (subst_term e1 x1 e3) (subst_term e1 x1 e2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_open_term_wrt_term : lngen.

Lemma subst_term_open_term_wrt_typ :
forall e2 e1 t1 x1,
  lc_term e1 ->
  subst_term e1 x1 (open_term_wrt_typ e2 t1) = open_term_wrt_typ (subst_term e1 x1 e2) t1.
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve subst_term_open_term_wrt_typ : lngen.

Lemma tsubst_term_open_term_wrt_term :
forall e2 t1 e1 a1,
  tsubst_term t1 a1 (open_term_wrt_term e2 e1) = open_term_wrt_term (tsubst_term t1 a1 e2) (tsubst_term t1 a1 e1).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve tsubst_term_open_term_wrt_term : lngen.

Lemma tsubst_term_open_term_wrt_typ :
forall e1 t1 t2 a1,
  lc_typ t1 ->
  tsubst_term t1 a1 (open_term_wrt_typ e1 t2) = open_term_wrt_typ (tsubst_term t1 a1 e1) (tsubst_typ t1 a1 t2).
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_term_open_term_wrt_typ : lngen.

Lemma tsubst_typ_open_typ_wrt_typ_var :
forall t2 t1 a1 a2,
  a1 <> a2 ->
  lc_typ t1 ->
  open_typ_wrt_typ (tsubst_typ t1 a1 t2) (typ_var_f a2) = tsubst_typ t1 a1 (open_typ_wrt_typ t2 (typ_var_f a2)).
Proof.
intros; rewrite tsubst_typ_open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_typ_open_typ_wrt_typ_var : lngen.

Lemma subst_term_open_term_wrt_term_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_term e1 ->
  open_term_wrt_term (subst_term e1 x1 e2) (term_var_f x2) = subst_term e1 x1 (open_term_wrt_term e2 (term_var_f x2)).
Proof.
intros; rewrite subst_term_open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_open_term_wrt_term_var : lngen.

Lemma subst_term_open_term_wrt_typ_var :
forall e2 e1 x1 a1,
  lc_term e1 ->
  open_term_wrt_typ (subst_term e1 x1 e2) (typ_var_f a1) = subst_term e1 x1 (open_term_wrt_typ e2 (typ_var_f a1)).
Proof.
intros; rewrite subst_term_open_term_wrt_typ; default_simp.
Qed.

Hint Resolve subst_term_open_term_wrt_typ_var : lngen.

Lemma tsubst_term_open_term_wrt_term_var :
forall e1 t1 a1 x1,
  open_term_wrt_term (tsubst_term t1 a1 e1) (term_var_f x1) = tsubst_term t1 a1 (open_term_wrt_term e1 (term_var_f x1)).
Proof.
intros; rewrite tsubst_term_open_term_wrt_term; default_simp.
Qed.

Hint Resolve tsubst_term_open_term_wrt_term_var : lngen.

Lemma tsubst_term_open_term_wrt_typ_var :
forall e1 t1 a1 a2,
  a1 <> a2 ->
  lc_typ t1 ->
  open_term_wrt_typ (tsubst_term t1 a1 e1) (typ_var_f a2) = tsubst_term t1 a1 (open_term_wrt_typ e1 (typ_var_f a2)).
Proof.
intros; rewrite tsubst_term_open_term_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_term_open_term_wrt_typ_var : lngen.

(* begin hide *)

Lemma tsubst_typ_spec_rec_mutual :
(forall t1 t2 a1 n1,
  tsubst_typ t2 a1 t1 = open_typ_wrt_typ_rec n1 t2 (close_typ_wrt_typ_rec n1 a1 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_typ_spec_rec :
forall t1 t2 a1 n1,
  tsubst_typ t2 a1 t1 = open_typ_wrt_typ_rec n1 t2 (close_typ_wrt_typ_rec n1 a1 t1).
Proof.
pose proof tsubst_typ_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_term_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_term e2 x1 e1 = open_term_wrt_term_rec n1 e2 (close_term_wrt_term_rec n1 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_spec_rec :
forall e1 e2 x1 n1,
  subst_term e2 x1 e1 = open_term_wrt_term_rec n1 e2 (close_term_wrt_term_rec n1 x1 e1).
Proof.
pose proof subst_term_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_spec_rec_mutual :
(forall e1 t1 a1 n1,
  tsubst_term t1 a1 e1 = open_term_wrt_typ_rec n1 t1 (close_term_wrt_typ_rec n1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_spec_rec :
forall e1 t1 a1 n1,
  tsubst_term t1 a1 e1 = open_term_wrt_typ_rec n1 t1 (close_term_wrt_typ_rec n1 a1 e1).
Proof.
pose proof tsubst_term_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_spec_rec : lngen.

(* end hide *)

Lemma tsubst_typ_spec :
forall t1 t2 a1,
  tsubst_typ t2 a1 t1 = open_typ_wrt_typ (close_typ_wrt_typ a1 t1) t2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_typ_spec : lngen.

Lemma subst_term_spec :
forall e1 e2 x1,
  subst_term e2 x1 e1 = open_term_wrt_term (close_term_wrt_term x1 e1) e2.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_spec : lngen.

Lemma tsubst_term_spec :
forall e1 t1 a1,
  tsubst_term t1 a1 e1 = open_term_wrt_typ (close_term_wrt_typ a1 e1) t1.
Proof.
unfold close_term_wrt_typ; unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_term_spec : lngen.

(* begin hide *)

Lemma tsubst_typ_tsubst_typ_mutual :
(forall t1 t2 t3 a2 a1,
  a2 `notin` ftv_typ t2 ->
  a2 <> a1 ->
  tsubst_typ t2 a1 (tsubst_typ t3 a2 t1) = tsubst_typ (tsubst_typ t2 a1 t3) a2 (tsubst_typ t2 a1 t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_tsubst_typ :
forall t1 t2 t3 a2 a1,
  a2 `notin` ftv_typ t2 ->
  a2 <> a1 ->
  tsubst_typ t2 a1 (tsubst_typ t3 a2 t1) = tsubst_typ (tsubst_typ t2 a1 t3) a2 (tsubst_typ t2 a1 t1).
Proof.
pose proof tsubst_typ_tsubst_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_tsubst_typ : lngen.

(* begin hide *)

Lemma subst_term_subst_term_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_term e2 ->
  x2 <> x1 ->
  subst_term e2 x1 (subst_term e3 x2 e1) = subst_term (subst_term e2 x1 e3) x2 (subst_term e2 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_subst_term :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_term e2 ->
  x2 <> x1 ->
  subst_term e2 x1 (subst_term e3 x2 e1) = subst_term (subst_term e2 x1 e3) x2 (subst_term e2 x1 e1).
Proof.
pose proof subst_term_subst_term_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_subst_term : lngen.

(* begin hide *)

Lemma subst_term_tsubst_term_mutual :
(forall e1 e2 t1 a1 x1,
  a1 `notin` ftv_term e2 ->
  subst_term e2 x1 (tsubst_term t1 a1 e1) = tsubst_term t1 a1 (subst_term e2 x1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_tsubst_term :
forall e1 e2 t1 a1 x1,
  a1 `notin` ftv_term e2 ->
  subst_term e2 x1 (tsubst_term t1 a1 e1) = tsubst_term t1 a1 (subst_term e2 x1 e1).
Proof.
pose proof subst_term_tsubst_term_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_tsubst_term : lngen.

(* begin hide *)

Lemma tsubst_term_subst_term_mutual :
(forall e1 t1 e2 x1 a1,
  tsubst_term t1 a1 (subst_term e2 x1 e1) = subst_term (tsubst_term t1 a1 e2) x1 (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_subst_term :
forall e1 t1 e2 x1 a1,
  tsubst_term t1 a1 (subst_term e2 x1 e1) = subst_term (tsubst_term t1 a1 e2) x1 (tsubst_term t1 a1 e1).
Proof.
pose proof tsubst_term_subst_term_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_subst_term : lngen.

(* begin hide *)

Lemma tsubst_term_tsubst_term_mutual :
(forall e1 t1 t2 a2 a1,
  a2 `notin` ftv_typ t1 ->
  a2 <> a1 ->
  tsubst_term t1 a1 (tsubst_term t2 a2 e1) = tsubst_term (tsubst_typ t1 a1 t2) a2 (tsubst_term t1 a1 e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_tsubst_term :
forall e1 t1 t2 a2 a1,
  a2 `notin` ftv_typ t1 ->
  a2 <> a1 ->
  tsubst_term t1 a1 (tsubst_term t2 a2 e1) = tsubst_term (tsubst_typ t1 a1 t2) a2 (tsubst_term t1 a1 e1).
Proof.
pose proof tsubst_term_tsubst_term_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_tsubst_term : lngen.

(* begin hide *)

Lemma tsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall t2 t1 a1 a2 n1,
  a2 `notin` ftv_typ t2 ->
  a2 `notin` ftv_typ t1 ->
  a2 <> a1 ->
  degree_typ_wrt_typ n1 t1 ->
  tsubst_typ t1 a1 t2 = close_typ_wrt_typ_rec n1 a2 (tsubst_typ t1 a1 (open_typ_wrt_typ_rec n1 (typ_var_f a2) t2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall t2 t1 a1 a2 n1,
  a2 `notin` ftv_typ t2 ->
  a2 `notin` ftv_typ t1 ->
  a2 <> a1 ->
  degree_typ_wrt_typ n1 t1 ->
  tsubst_typ t1 a1 t2 = close_typ_wrt_typ_rec n1 a2 (tsubst_typ t1 a1 (open_typ_wrt_typ_rec n1 (typ_var_f a2) t2)).
Proof.
pose proof tsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_term e2 ->
  x2 `notin` fv_term e1 ->
  x2 <> x1 ->
  degree_term_wrt_term n1 e1 ->
  subst_term e1 x1 e2 = close_term_wrt_term_rec n1 x2 (subst_term e1 x1 (open_term_wrt_term_rec n1 (term_var_f x2) e2))).
Proof.
apply_mutual_ind term_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_term e2 ->
  x2 `notin` fv_term e1 ->
  x2 <> x1 ->
  degree_term_wrt_term n1 e1 ->
  subst_term e1 x1 e2 = close_term_wrt_term_rec n1 x2 (subst_term e1 x1 (open_term_wrt_term_rec n1 (term_var_f x2) e2)).
Proof.
pose proof subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_term_close_term_wrt_typ_rec_open_term_wrt_typ_rec_mutual :
(forall e2 e1 x1 a1 n1,
  a1 `notin` ftv_term e2 ->
  a1 `notin` ftv_term e1 ->
  degree_term_wrt_typ n1 e1 ->
  subst_term e1 x1 e2 = close_term_wrt_typ_rec n1 a1 (subst_term e1 x1 (open_term_wrt_typ_rec n1 (typ_var_f a1) e2))).
Proof.
apply_mutual_ind term_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_close_term_wrt_typ_rec_open_term_wrt_typ_rec :
forall e2 e1 x1 a1 n1,
  a1 `notin` ftv_term e2 ->
  a1 `notin` ftv_term e1 ->
  degree_term_wrt_typ n1 e1 ->
  subst_term e1 x1 e2 = close_term_wrt_typ_rec n1 a1 (subst_term e1 x1 (open_term_wrt_typ_rec n1 (typ_var_f a1) e2)).
Proof.
pose proof subst_term_close_term_wrt_typ_rec_open_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_close_term_wrt_typ_rec_open_term_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_close_term_wrt_term_rec_open_term_wrt_term_rec_mutual :
(forall e1 t1 a1 x1 n1,
  x1 `notin` fv_term e1 ->
  tsubst_term t1 a1 e1 = close_term_wrt_term_rec n1 x1 (tsubst_term t1 a1 (open_term_wrt_term_rec n1 (term_var_f x1) e1))).
Proof.
apply_mutual_ind term_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_close_term_wrt_term_rec_open_term_wrt_term_rec :
forall e1 t1 a1 x1 n1,
  x1 `notin` fv_term e1 ->
  tsubst_term t1 a1 e1 = close_term_wrt_term_rec n1 x1 (tsubst_term t1 a1 (open_term_wrt_term_rec n1 (term_var_f x1) e1)).
Proof.
pose proof tsubst_term_close_term_wrt_term_rec_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_close_term_wrt_term_rec_open_term_wrt_term_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_close_term_wrt_typ_rec_open_term_wrt_typ_rec_mutual :
(forall e1 t1 a1 a2 n1,
  a2 `notin` ftv_term e1 ->
  a2 `notin` ftv_typ t1 ->
  a2 <> a1 ->
  degree_typ_wrt_typ n1 t1 ->
  tsubst_term t1 a1 e1 = close_term_wrt_typ_rec n1 a2 (tsubst_term t1 a1 (open_term_wrt_typ_rec n1 (typ_var_f a2) e1))).
Proof.
apply_mutual_ind term_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_term_close_term_wrt_typ_rec_open_term_wrt_typ_rec :
forall e1 t1 a1 a2 n1,
  a2 `notin` ftv_term e1 ->
  a2 `notin` ftv_typ t1 ->
  a2 <> a1 ->
  degree_typ_wrt_typ n1 t1 ->
  tsubst_term t1 a1 e1 = close_term_wrt_typ_rec n1 a2 (tsubst_term t1 a1 (open_term_wrt_typ_rec n1 (typ_var_f a2) e1)).
Proof.
pose proof tsubst_term_close_term_wrt_typ_rec_open_term_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_close_term_wrt_typ_rec_open_term_wrt_typ_rec : lngen.

(* end hide *)

Lemma tsubst_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall t2 t1 a1 a2,
  a2 `notin` ftv_typ t2 ->
  a2 `notin` ftv_typ t1 ->
  a2 <> a1 ->
  lc_typ t1 ->
  tsubst_typ t1 a1 t2 = close_typ_wrt_typ a2 (tsubst_typ t1 a1 (open_typ_wrt_typ t2 (typ_var_f a2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma subst_term_close_term_wrt_term_open_term_wrt_term :
forall e2 e1 x1 x2,
  x2 `notin` fv_term e2 ->
  x2 `notin` fv_term e1 ->
  x2 <> x1 ->
  lc_term e1 ->
  subst_term e1 x1 e2 = close_term_wrt_term x2 (subst_term e1 x1 (open_term_wrt_term e2 (term_var_f x2))).
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_close_term_wrt_term_open_term_wrt_term : lngen.

Lemma subst_term_close_term_wrt_typ_open_term_wrt_typ :
forall e2 e1 x1 a1,
  a1 `notin` ftv_term e2 ->
  a1 `notin` ftv_term e1 ->
  lc_term e1 ->
  subst_term e1 x1 e2 = close_term_wrt_typ a1 (subst_term e1 x1 (open_term_wrt_typ e2 (typ_var_f a1))).
Proof.
unfold close_term_wrt_typ; unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve subst_term_close_term_wrt_typ_open_term_wrt_typ : lngen.

Lemma tsubst_term_close_term_wrt_term_open_term_wrt_term :
forall e1 t1 a1 x1,
  x1 `notin` fv_term e1 ->
  lc_typ t1 ->
  tsubst_term t1 a1 e1 = close_term_wrt_term x1 (tsubst_term t1 a1 (open_term_wrt_term e1 (term_var_f x1))).
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve tsubst_term_close_term_wrt_term_open_term_wrt_term : lngen.

Lemma tsubst_term_close_term_wrt_typ_open_term_wrt_typ :
forall e1 t1 a1 a2,
  a2 `notin` ftv_term e1 ->
  a2 `notin` ftv_typ t1 ->
  a2 <> a1 ->
  lc_typ t1 ->
  tsubst_term t1 a1 e1 = close_term_wrt_typ a2 (tsubst_term t1 a1 (open_term_wrt_typ e1 (typ_var_f a2))).
Proof.
unfold close_term_wrt_typ; unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_term_close_term_wrt_typ_open_term_wrt_typ : lngen.

Lemma tsubst_typ_typ_forall :
forall a2 t2 t1 a1,
  lc_typ t1 ->
  a2 `notin` ftv_typ t1 `union` ftv_typ t2 `union` singleton a1 ->
  tsubst_typ t1 a1 (typ_forall t2) = typ_forall (close_typ_wrt_typ a2 (tsubst_typ t1 a1 (open_typ_wrt_typ t2 (typ_var_f a2)))).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_typ_typ_forall : lngen.

Lemma subst_term_term_abs :
forall x2 t1 e2 e1 x1,
  lc_term e1 ->
  x2 `notin` fv_term e1 `union` fv_term e2 `union` singleton x1 ->
  subst_term e1 x1 (term_abs t1 e2) = term_abs (t1) (close_term_wrt_term x2 (subst_term e1 x1 (open_term_wrt_term e2 (term_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_term_abs : lngen.

Lemma subst_term_term_gen :
forall a1 e2 e1 x1,
  lc_term e1 ->
  a1 `notin` ftv_term e1 `union` ftv_term e2 ->
  subst_term e1 x1 (term_gen e2) = term_gen (close_term_wrt_typ a1 (subst_term e1 x1 (open_term_wrt_typ e2 (typ_var_f a1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_term_gen : lngen.

Lemma tsubst_term_term_abs :
forall x1 t2 e1 t1 a1,
  lc_typ t1 ->
  x1 `notin` fv_term e1 ->
  tsubst_term t1 a1 (term_abs t2 e1) = term_abs (tsubst_typ t1 a1 t2) (close_term_wrt_term x1 (tsubst_term t1 a1 (open_term_wrt_term e1 (term_var_f x1)))).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_term_term_abs : lngen.

Lemma tsubst_term_term_gen :
forall a2 e1 t1 a1,
  lc_typ t1 ->
  a2 `notin` ftv_typ t1 `union` ftv_term e1 `union` singleton a1 ->
  tsubst_term t1 a1 (term_gen e1) = term_gen (close_term_wrt_typ a2 (tsubst_term t1 a1 (open_term_wrt_typ e1 (typ_var_f a2)))).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_term_term_gen : lngen.

(* begin hide *)

Lemma tsubst_typ_intro_rec_mutual :
(forall t1 a1 t2 n1,
  a1 `notin` ftv_typ t1 ->
  open_typ_wrt_typ_rec n1 t2 t1 = tsubst_typ t2 a1 (open_typ_wrt_typ_rec n1 (typ_var_f a1) t1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_intro_rec :
forall t1 a1 t2 n1,
  a1 `notin` ftv_typ t1 ->
  open_typ_wrt_typ_rec n1 t2 t1 = tsubst_typ t2 a1 (open_typ_wrt_typ_rec n1 (typ_var_f a1) t1).
Proof.
pose proof tsubst_typ_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_intro_rec : lngen.
Hint Rewrite tsubst_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_term_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_term e1 ->
  open_term_wrt_term_rec n1 e2 e1 = subst_term e2 x1 (open_term_wrt_term_rec n1 (term_var_f x1) e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_term e1 ->
  open_term_wrt_term_rec n1 e2 e1 = subst_term e2 x1 (open_term_wrt_term_rec n1 (term_var_f x1) e1).
Proof.
pose proof subst_term_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_intro_rec : lngen.
Hint Rewrite subst_term_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_term_intro_rec_mutual :
(forall e1 a1 t1 n1,
  a1 `notin` ftv_term e1 ->
  open_term_wrt_typ_rec n1 t1 e1 = tsubst_term t1 a1 (open_term_wrt_typ_rec n1 (typ_var_f a1) e1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_term_intro_rec :
forall e1 a1 t1 n1,
  a1 `notin` ftv_term e1 ->
  open_term_wrt_typ_rec n1 t1 e1 = tsubst_term t1 a1 (open_term_wrt_typ_rec n1 (typ_var_f a1) e1).
Proof.
pose proof tsubst_term_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_term_intro_rec : lngen.
Hint Rewrite tsubst_term_intro_rec using solve [auto] : lngen.

Lemma tsubst_typ_intro :
forall a1 t1 t2,
  a1 `notin` ftv_typ t1 ->
  open_typ_wrt_typ t1 t2 = tsubst_typ t2 a1 (open_typ_wrt_typ t1 (typ_var_f a1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_typ_intro : lngen.

Lemma subst_term_intro :
forall x1 e1 e2,
  x1 `notin` fv_term e1 ->
  open_term_wrt_term e1 e2 = subst_term e2 x1 (open_term_wrt_term e1 (term_var_f x1)).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_intro : lngen.

Lemma tsubst_term_intro :
forall a1 e1 t1,
  a1 `notin` ftv_term e1 ->
  open_term_wrt_typ e1 t1 = tsubst_term t1 a1 (open_term_wrt_typ e1 (typ_var_f a1)).
Proof.
unfold open_term_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_term_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto := auto; tauto.
Ltac default_autorewrite := fail.
