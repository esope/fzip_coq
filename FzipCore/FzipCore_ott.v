(* generated by Ott 0.10.17 ***locally nameless*** from: FzipCore.ott *)

Require Import Metatheory.

Inductive tag {A : Type} : Type :=
  | T : A -> tag
  | U : tag
  | E : tag
  | Eq : A -> tag.

Definition pure {A: Type} (G: list (atom * @tag A)) := forall a, ~ binds a E G.
Hint Unfold pure.


(** syntax *)
Definition termvar := var.
Definition typvar := var.

Inductive typ : Set := 
 | typ_var_b : nat -> typ
 | typ_var_f : typvar -> typ
 | typ_arrow : typ -> typ -> typ
 | typ_prod : typ -> typ -> typ
 | typ_forall : typ -> typ
 | typ_exists : typ -> typ.

Inductive term : Set := 
 | term_var_b : nat -> term
 | term_var_f : termvar -> term
 | term_abs : typ -> term -> term
 | term_app : term -> term -> term
 | term_let : term -> term -> term
 | term_pair : term -> term -> term
 | term_fst : term -> term
 | term_snd : term -> term
 | term_gen : term -> term
 | term_inst : term -> typ -> term
 | term_exists : term -> term
 | term_open : typ -> term -> term
 | term_nu : term -> term
 | term_sigma : typ -> typ -> term -> term
 | term_coerce : term -> typ -> term.

Definition typing_env : Set := list (atom * @tag typ).

(* EXPERIMENTAL *)

(** opening up abstractions *)
Fixpoint open_typ_wrt_typ_rec (k:nat) (t_5:typ) (t__6:typ) {struct t__6}: typ :=
  match t__6 with
  | (typ_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => typ_var_b nat
        | inleft (right _) => t_5
        | inright _ => typ_var_b (nat - 1)
      end
  | (typ_var_f a) => typ_var_f a
  | (typ_arrow t1 t2) => typ_arrow (open_typ_wrt_typ_rec k t_5 t1) (open_typ_wrt_typ_rec k t_5 t2)
  | (typ_prod t1 t2) => typ_prod (open_typ_wrt_typ_rec k t_5 t1) (open_typ_wrt_typ_rec k t_5 t2)
  | (typ_forall t) => typ_forall (open_typ_wrt_typ_rec (S k) t_5 t)
  | (typ_exists t) => typ_exists (open_typ_wrt_typ_rec (S k) t_5 t)
end.

Fixpoint open_term_wrt_term_rec (k:nat) (e_5:term) (e__6:term) {struct e__6}: term :=
  match e__6 with
  | (term_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => term_var_b nat
        | inleft (right _) => e_5
        | inright _ => term_var_b (nat - 1)
      end
  | (term_var_f x) => term_var_f x
  | (term_abs t e) => term_abs t (open_term_wrt_term_rec (S k) e_5 e)
  | (term_app e1 e2) => term_app (open_term_wrt_term_rec k e_5 e1) (open_term_wrt_term_rec k e_5 e2)
  | (term_let e1 e2) => term_let (open_term_wrt_term_rec k e_5 e1) (open_term_wrt_term_rec (S k) e_5 e2)
  | (term_pair e1 e2) => term_pair (open_term_wrt_term_rec k e_5 e1) (open_term_wrt_term_rec k e_5 e2)
  | (term_fst e) => term_fst (open_term_wrt_term_rec k e_5 e)
  | (term_snd e) => term_snd (open_term_wrt_term_rec k e_5 e)
  | (term_gen e) => term_gen (open_term_wrt_term_rec k e_5 e)
  | (term_inst e t) => term_inst (open_term_wrt_term_rec k e_5 e) t
  | (term_exists e) => term_exists (open_term_wrt_term_rec k e_5 e)
  | (term_open t e) => term_open t (open_term_wrt_term_rec k e_5 e)
  | (term_nu e) => term_nu (open_term_wrt_term_rec k e_5 e)
  | (term_sigma t1 t2 e) => term_sigma t1 t2 (open_term_wrt_term_rec k e_5 e)
  | (term_coerce e t) => term_coerce (open_term_wrt_term_rec k e_5 e) t
end.

Fixpoint open_term_wrt_typ_rec (k:nat) (t_5:typ) (e_5:term) {struct e_5}: term :=
  match e_5 with
  | (term_var_b nat) => term_var_b nat
  | (term_var_f x) => term_var_f x
  | (term_abs t e) => term_abs (open_typ_wrt_typ_rec k t_5 t) (open_term_wrt_typ_rec k t_5 e)
  | (term_app e1 e2) => term_app (open_term_wrt_typ_rec k t_5 e1) (open_term_wrt_typ_rec k t_5 e2)
  | (term_let e1 e2) => term_let (open_term_wrt_typ_rec k t_5 e1) (open_term_wrt_typ_rec k t_5 e2)
  | (term_pair e1 e2) => term_pair (open_term_wrt_typ_rec k t_5 e1) (open_term_wrt_typ_rec k t_5 e2)
  | (term_fst e) => term_fst (open_term_wrt_typ_rec k t_5 e)
  | (term_snd e) => term_snd (open_term_wrt_typ_rec k t_5 e)
  | (term_gen e) => term_gen (open_term_wrt_typ_rec (S k) t_5 e)
  | (term_inst e t) => term_inst (open_term_wrt_typ_rec k t_5 e) (open_typ_wrt_typ_rec k t_5 t)
  | (term_exists e) => term_exists (open_term_wrt_typ_rec (S k) t_5 e)
  | (term_open t e) => term_open (open_typ_wrt_typ_rec k t_5 t) (open_term_wrt_typ_rec k t_5 e)
  | (term_nu e) => term_nu (open_term_wrt_typ_rec (S k) t_5 e)
  | (term_sigma t1 t2 e) => term_sigma (open_typ_wrt_typ_rec k t_5 t1) (open_typ_wrt_typ_rec k t_5 t2) (open_term_wrt_typ_rec (S k) t_5 e)
  | (term_coerce e t) => term_coerce (open_term_wrt_typ_rec k t_5 e) (open_typ_wrt_typ_rec k t_5 t)
end.

Definition open_typ_wrt_typ t_5 t__6 := open_typ_wrt_typ_rec 0 t__6 t_5.

Definition open_term_wrt_term e_5 e__6 := open_term_wrt_term_rec 0 e__6 e_5.

Definition open_term_wrt_typ t_5 e_5 := open_term_wrt_typ_rec 0 e_5 t_5.


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_typ *)
Inductive lc_typ : typ -> Prop :=    (* defn lc_typ *)
 | lc_typ_var_f : forall (a:typvar),
     (lc_typ (typ_var_f a))
 | lc_typ_arrow : forall (t1 t2:typ),
     (lc_typ t1) ->
     (lc_typ t2) ->
     (lc_typ (typ_arrow t1 t2))
 | lc_typ_prod : forall (t1 t2:typ),
     (lc_typ t1) ->
     (lc_typ t2) ->
     (lc_typ (typ_prod t1 t2))
 | lc_typ_forall : forall (t:typ),
      ( forall a , lc_typ  ( open_typ_wrt_typ t (typ_var_f a) )  )  ->
     (lc_typ (typ_forall t))
 | lc_typ_exists : forall (t:typ),
      ( forall a , lc_typ  ( open_typ_wrt_typ t (typ_var_f a) )  )  ->
     (lc_typ (typ_exists t)).

(* defns LC_term *)
Inductive lc_term : term -> Prop :=    (* defn lc_term *)
 | lc_term_var_f : forall (x:termvar),
     (lc_term (term_var_f x))
 | lc_term_abs : forall (t:typ) (e:term),
     (lc_typ t) ->
      ( forall x , lc_term  ( open_term_wrt_term e (term_var_f x) )  )  ->
     (lc_term (term_abs t e))
 | lc_term_app : forall (e1 e2:term),
     (lc_term e1) ->
     (lc_term e2) ->
     (lc_term (term_app e1 e2))
 | lc_term_let : forall (e1 e2:term),
     (lc_term e1) ->
      ( forall x , lc_term  ( open_term_wrt_term e2 (term_var_f x) )  )  ->
     (lc_term (term_let e1 e2))
 | lc_term_pair : forall (e1 e2:term),
     (lc_term e1) ->
     (lc_term e2) ->
     (lc_term (term_pair e1 e2))
 | lc_term_fst : forall (e:term),
     (lc_term e) ->
     (lc_term (term_fst e))
 | lc_term_snd : forall (e:term),
     (lc_term e) ->
     (lc_term (term_snd e))
 | lc_term_gen : forall (e:term),
      ( forall a , lc_term  ( open_term_wrt_typ e (typ_var_f a) )  )  ->
     (lc_term (term_gen e))
 | lc_term_inst : forall (e:term) (t:typ),
     (lc_term e) ->
     (lc_typ t) ->
     (lc_term (term_inst e t))
 | lc_term_exists : forall (e:term),
      ( forall a , lc_term  ( open_term_wrt_typ e (typ_var_f a) )  )  ->
     (lc_term (term_exists e))
 | lc_term_open : forall (t:typ) (e:term),
     (lc_typ t) ->
     (lc_term e) ->
     (lc_term (term_open t e))
 | lc_term_nu : forall (e:term),
      ( forall a , lc_term  ( open_term_wrt_typ e (typ_var_f a) )  )  ->
     (lc_term (term_nu e))
 | lc_term_sigma : forall (t1 t2:typ) (e:term),
     (lc_typ t1) ->
     (lc_typ t2) ->
      ( forall a , lc_term  ( open_term_wrt_typ e (typ_var_f a) )  )  ->
     (lc_term (term_sigma t1 t2 e))
 | lc_term_coerce : forall (e:term) (t:typ),
     (lc_term e) ->
     (lc_typ t) ->
     (lc_term (term_coerce e t)).

(** free variables *)
Fixpoint ftv_typ (t_5:typ) : vars :=
  match t_5 with
  | (typ_var_b nat) => {}
  | (typ_var_f a) => {{a}}
  | (typ_arrow t1 t2) => (ftv_typ t1) \u (ftv_typ t2)
  | (typ_prod t1 t2) => (ftv_typ t1) \u (ftv_typ t2)
  | (typ_forall t) => (ftv_typ t)
  | (typ_exists t) => (ftv_typ t)
end.

Fixpoint fv_term (e_5:term) : vars :=
  match e_5 with
  | (term_var_b nat) => {}
  | (term_var_f x) => {{x}}
  | (term_abs t e) => (fv_term e)
  | (term_app e1 e2) => (fv_term e1) \u (fv_term e2)
  | (term_let e1 e2) => (fv_term e1) \u (fv_term e2)
  | (term_pair e1 e2) => (fv_term e1) \u (fv_term e2)
  | (term_fst e) => (fv_term e)
  | (term_snd e) => (fv_term e)
  | (term_gen e) => (fv_term e)
  | (term_inst e t) => (fv_term e)
  | (term_exists e) => (fv_term e)
  | (term_open t e) => (fv_term e)
  | (term_nu e) => (fv_term e)
  | (term_sigma t1 t2 e) => (fv_term e)
  | (term_coerce e t) => (fv_term e)
end.

Fixpoint ftv_term (e_5:term) : vars :=
  match e_5 with
  | (term_var_b nat) => {}
  | (term_var_f x) => {}
  | (term_abs t e) => (ftv_typ t) \u (ftv_term e)
  | (term_app e1 e2) => (ftv_term e1) \u (ftv_term e2)
  | (term_let e1 e2) => (ftv_term e1) \u (ftv_term e2)
  | (term_pair e1 e2) => (ftv_term e1) \u (ftv_term e2)
  | (term_fst e) => (ftv_term e)
  | (term_snd e) => (ftv_term e)
  | (term_gen e) => (ftv_term e)
  | (term_inst e t) => (ftv_term e) \u (ftv_typ t)
  | (term_exists e) => (ftv_term e)
  | (term_open t e) => (ftv_typ t) \u (ftv_term e)
  | (term_nu e) => (ftv_term e)
  | (term_sigma t1 t2 e) => (ftv_typ t1) \u (ftv_typ t2) \u (ftv_term e)
  | (term_coerce e t) => (ftv_term e) \u (ftv_typ t)
end.


(** substitutions *)
Fixpoint tsubst_typ (t_5:typ) (a5:typvar) (t__6:typ) {struct t__6} : typ :=
  match t__6 with
  | (typ_var_b nat) => typ_var_b nat
  | (typ_var_f a) => (if eq_var a a5 then t_5 else (typ_var_f a))
  | (typ_arrow t1 t2) => typ_arrow (tsubst_typ t_5 a5 t1) (tsubst_typ t_5 a5 t2)
  | (typ_prod t1 t2) => typ_prod (tsubst_typ t_5 a5 t1) (tsubst_typ t_5 a5 t2)
  | (typ_forall t) => typ_forall (tsubst_typ t_5 a5 t)
  | (typ_exists t) => typ_exists (tsubst_typ t_5 a5 t)
end.

Fixpoint subst_term (e_5:term) (x5:termvar) (e__6:term) {struct e__6} : term :=
  match e__6 with
  | (term_var_b nat) => term_var_b nat
  | (term_var_f x) => (if eq_var x x5 then e_5 else (term_var_f x))
  | (term_abs t e) => term_abs t (subst_term e_5 x5 e)
  | (term_app e1 e2) => term_app (subst_term e_5 x5 e1) (subst_term e_5 x5 e2)
  | (term_let e1 e2) => term_let (subst_term e_5 x5 e1) (subst_term e_5 x5 e2)
  | (term_pair e1 e2) => term_pair (subst_term e_5 x5 e1) (subst_term e_5 x5 e2)
  | (term_fst e) => term_fst (subst_term e_5 x5 e)
  | (term_snd e) => term_snd (subst_term e_5 x5 e)
  | (term_gen e) => term_gen (subst_term e_5 x5 e)
  | (term_inst e t) => term_inst (subst_term e_5 x5 e) t
  | (term_exists e) => term_exists (subst_term e_5 x5 e)
  | (term_open t e) => term_open t (subst_term e_5 x5 e)
  | (term_nu e) => term_nu (subst_term e_5 x5 e)
  | (term_sigma t1 t2 e) => term_sigma t1 t2 (subst_term e_5 x5 e)
  | (term_coerce e t) => term_coerce (subst_term e_5 x5 e) t
end.

Fixpoint tsubst_term (t_5:typ) (a5:typvar) (e_5:term) {struct e_5} : term :=
  match e_5 with
  | (term_var_b nat) => term_var_b nat
  | (term_var_f x) => term_var_f x
  | (term_abs t e) => term_abs (tsubst_typ t_5 a5 t) (tsubst_term t_5 a5 e)
  | (term_app e1 e2) => term_app (tsubst_term t_5 a5 e1) (tsubst_term t_5 a5 e2)
  | (term_let e1 e2) => term_let (tsubst_term t_5 a5 e1) (tsubst_term t_5 a5 e2)
  | (term_pair e1 e2) => term_pair (tsubst_term t_5 a5 e1) (tsubst_term t_5 a5 e2)
  | (term_fst e) => term_fst (tsubst_term t_5 a5 e)
  | (term_snd e) => term_snd (tsubst_term t_5 a5 e)
  | (term_gen e) => term_gen (tsubst_term t_5 a5 e)
  | (term_inst e t) => term_inst (tsubst_term t_5 a5 e) (tsubst_typ t_5 a5 t)
  | (term_exists e) => term_exists (tsubst_term t_5 a5 e)
  | (term_open t e) => term_open (tsubst_typ t_5 a5 t) (tsubst_term t_5 a5 e)
  | (term_nu e) => term_nu (tsubst_term t_5 a5 e)
  | (term_sigma t1 t2 e) => term_sigma (tsubst_typ t_5 a5 t1) (tsubst_typ t_5 a5 t2) (tsubst_term t_5 a5 e)
  | (term_coerce e t) => term_coerce (tsubst_term t_5 a5 e) (tsubst_typ t_5 a5 t)
end.


(** definitions *)

(* defns Jval *)
Inductive val : term -> Prop :=    (* defn val *)
 | val_abs : forall (t:typ) (e:term),
     lc_typ t ->
     lc_term (term_abs t e) ->
     val (term_abs t e)
 | val_gen : forall (e:term),
     lc_term (term_gen e) ->
     val (term_gen e)
 | val_pair : forall (e1 e2:term),
     val e1 ->
     val e2 ->
     val (term_pair e1 e2)
 | val_coerce : forall (e:term) (t:typ),
     lc_typ t ->
     val e ->
      (forall e' t, ( e ) <> term_coerce e' t)  ->
     val (term_coerce e t)
 | val_exists : forall (L:vars) (t':typ) (e e':term),
     e = term_exists (term_sigma (typ_var_b 0) t' e') ->
     (forall b, b \notin L -> lc_typ (open_typ_wrt_typ t' (typ_var_f b))) ->
     (forall b a, b \notin L -> a \notin L \u {{ b }} ->
         forall e1 e2 t1,
           term_sigma (typ_var_f b) t1 e1 =
           open_term_wrt_typ (term_sigma (typ_var_b 0) t' e') (typ_var_f b) ->
           e2 = open_term_wrt_typ e1 (typ_var_f a) ->
           val e2) ->
     val e

with result : term -> Prop :=    (* defn result *)
 | result_val : forall (e:term),
     val e ->
     result e
 | result_sigma : forall (L:vars) (b:typvar) (t:typ) (e:term),
     lc_typ t ->
      ( forall a , a \notin  L  -> result  ( open_term_wrt_typ e (typ_var_f a) )  )  ->
     result (term_sigma (typ_var_f b) t e).

(* defns Jzip *)
Inductive zip : typing_env -> typing_env -> typing_env -> Prop :=    (* defn zip *)
 | zip_empty : 
     zip  nil   nil   nil 
 | zip_TT : forall (G1:typing_env) (x:termvar) (t:typ) (G2 G:typing_env),
     lc_typ t ->
      x  `notin` dom  G1  ->
      x  `notin` dom  G2  ->
     zip G1 G2 G ->
     zip  ( x ~(T  t ) ++  G1 )   ( x ~(T  t ) ++  G2 )   ( x ~(T  t ) ++  G ) 
 | zip_UU : forall (G1:typing_env) (a:typvar) (G2 G:typing_env),
      a  `notin` dom  G1  ->
      a  `notin` dom  G2  ->
     zip G1 G2 G ->
     zip  ( a ~U ++  G1 )   ( a ~U ++  G2 )   ( a ~U ++  G ) 
 | zip_EU : forall (G1:typing_env) (a:typvar) (G2 G:typing_env),
      a  `notin` dom  G1  ->
      a  `notin` dom  G2  ->
     zip G1 G2 G ->
     zip  ( a ~E ++  G1 )   ( a ~U ++  G2 )   ( a ~E ++  G ) 
 | zip_E : forall (G1 G2:typing_env) (a:typvar) (G:typing_env),
      a  `notin` dom  G1  ->
      a  `notin` dom  G2  ->
     zip G1 G2 G ->
     zip G1  ( a ~E ++  G2 )   ( a ~E ++  G ) 
 | zip_EqEq : forall (G1:typing_env) (a:typvar) (t:typ) (G2 G:typing_env),
     lc_typ t ->
      a  `notin` dom  G1  ->
      a  `notin` dom  G2  ->
     zip G1 G2 G ->
     zip  ( a ~(Eq  t ) ++  G1 )   ( a ~(Eq  t ) ++  G2 )   ( a ~(Eq  t ) ++  G ) .

(* defns Jwf_env_typ *)
Inductive wfenv : typing_env -> Prop :=    (* defn wfenv *)
 | wfenv_empty : 
     wfenv  nil 
 | wfenv_cons_T : forall (G:typing_env) (x:termvar) (t:typ),
      x  `notin` dom  G  ->
     wftyp G t ->
     wfenv  ( x ~(T  t ) ++  G ) 
 | wfenv_cons_U : forall (G:typing_env) (a:typvar),
      a  `notin` dom  G  ->
     wfenv G ->
     wfenv  ( a ~U ++  G ) 
 | wfenv_cons_E : forall (G:typing_env) (a:typvar),
      a  `notin` dom  G  ->
     wfenv G ->
     wfenv  ( a ~E ++  G ) 
 | wfenv_cons_Eq : forall (G:typing_env) (a:typvar) (t:typ),
      a  `notin` dom  G  ->
     wftyp G t ->
     wfenv  ( a ~(Eq  t ) ++  G ) 
with wftyp : typing_env -> typ -> Prop :=    (* defn wftyp *)
 | wftyp_var : forall (G:typing_env) (a:typvar),
      (binds ( a ) U ( G ) \/ binds ( a ) E ( G ) \/ exists t, binds ( a ) (Eq t) ( G ))  ->
     wfenv G ->
     wftyp G (typ_var_f a)
 | wftyp_arrow : forall (G:typing_env) (t1 t2:typ),
     wftyp G t1 ->
     wftyp G t2 ->
     wftyp G (typ_arrow t1 t2)
 | wftyp_pair : forall (G:typing_env) (t1 t2:typ),
     wftyp G t1 ->
     wftyp G t2 ->
     wftyp G (typ_prod t1 t2)
 | wftyp_forall : forall (L:vars) (G:typing_env) (t:typ),
      ( forall a , a \notin  L  -> wftyp  ( a ~U ++  G )   ( open_typ_wrt_typ t (typ_var_f a) )  )  ->
     wftyp G (typ_forall t)
 | wftyp_exists : forall (L:vars) (G:typing_env) (t:typ),
      ( forall a , a \notin  L  -> wftyp  ( a ~U ++  G )   ( open_typ_wrt_typ t (typ_var_f a) )  )  ->
     wftyp G (typ_exists t).

(* defns Jwftypeq *)
Inductive wftypeq : typing_env -> typ -> typ -> Prop :=    (* defn wftypeq *)
 | wftypeq_var : forall (G:typing_env) (a:typvar),
      (binds ( a ) U ( G ) \/ binds ( a ) E ( G ) \/ exists t, binds ( a ) (Eq t) ( G ))  ->
     wfenv G ->
     wftypeq G (typ_var_f a) (typ_var_f a)
 | wftypeq_eq : forall (G:typing_env) (a:typvar) (t:typ),
      binds ( a ) (Eq ( t )) ( G )  ->
     wfenv G ->
     wftypeq G (typ_var_f a) t
 | wftypeq_arrow : forall (G:typing_env) (t1 t2 t1' t2':typ),
     wftypeq G t1 t1' ->
     wftypeq G t2 t2' ->
     wftypeq G (typ_arrow t1 t2) (typ_arrow t1' t2')
 | wftypeq_prod : forall (G:typing_env) (t1 t2 t1' t2':typ),
     wftypeq G t1 t1' ->
     wftypeq G t2 t2' ->
     wftypeq G (typ_prod t1 t2) (typ_prod t1' t2')
 | wftypeq_forall : forall (L:vars) (G:typing_env) (t1 t2:typ),
      ( forall a , a \notin  L  -> wftypeq  ( a ~U ++  G )   ( open_typ_wrt_typ t1 (typ_var_f a) )   ( open_typ_wrt_typ t2 (typ_var_f a) )  )  ->
     wftypeq G (typ_forall t1) (typ_forall t2)
 | wftypeq_exists : forall (L:vars) (G:typing_env) (t1 t2:typ),
      ( forall a , a \notin  L  -> wftypeq  ( a ~U ++  G )   ( open_typ_wrt_typ t1 (typ_var_f a) )   ( open_typ_wrt_typ t2 (typ_var_f a) )  )  ->
     wftypeq G (typ_exists t1) (typ_exists t2)
 | wftypeq_sym : forall (G:typing_env) (t1 t2:typ),
     wftypeq G t2 t1 ->
     wftypeq G t1 t2
 | wftypeq_trans : forall (G:typing_env) (t1 t3 t2:typ),
     wftypeq G t1 t2 ->
     wftypeq G t2 t3 ->
     wftypeq G t1 t3.

(* defns Jwfterm *)
Inductive wfterm : typing_env -> term -> typ -> Prop :=    (* defn wfterm *)
 | wfterm_val : forall (G:typing_env) (x:termvar) (t:typ),
      (pure ( G ))  ->
     wfenv G ->
      binds ( x ) (T ( t )) ( G )  ->
     wfterm G (term_var_f x) t
 | wfterm_app : forall (G:typing_env) (e1 e2:term) (t1:typ) (G1 G2:typing_env) (t2:typ),
     zip G1 G2 G ->
     wfterm G1 e1 (typ_arrow t2 t1) ->
     wfterm G2 e2 t2 ->
     wfterm G (term_app e1 e2) t1
 | wfterm_abs : forall (L:vars) (G:typing_env) (t1:typ) (e:term) (t2:typ),
      (pure ( G ))  ->
      ( forall x , x \notin  L  -> wfterm  ( x ~(T  t1 ) ++  G )   ( open_term_wrt_term e (term_var_f x) )  t2 )  ->
     wfterm G (term_abs t1 e) (typ_arrow t1 t2)
 | wfterm_let : forall (L:vars) (G:typing_env) (e1 e2:term) (t2:typ) (G1 G2:typing_env) (t1:typ),
     zip G1 G2 G ->
     wfterm G1 e1 t1 ->
      ( forall x , x \notin  L  -> wfterm  ( x ~(T  t1 ) ++  G2 )   ( open_term_wrt_term e2 (term_var_f x) )  t2 )  ->
     wfterm G (term_let e1 e2) t2
 | wfterm_pair : forall (G:typing_env) (e1 e2:term) (t1 t2:typ) (G1 G2:typing_env),
     zip G1 G2 G ->
     wfterm G1 e1 t1 ->
     wfterm G2 e2 t2 ->
     wfterm G (term_pair e1 e2) (typ_prod t1 t2)
 | wfterm_fst : forall (G:typing_env) (e:term) (t1 t2:typ),
     wfterm G e (typ_prod t1 t2) ->
     wfterm G (term_fst e) t1
 | wfterm_snd : forall (G:typing_env) (e:term) (t2 t1:typ),
     wfterm G e (typ_prod t1 t2) ->
     wfterm G (term_snd e) t2
 | wfterm_inst : forall (G:typing_env) (e:term) (t t':typ),
     wftyp G t ->
     wfterm G e (typ_forall t') ->
     wfterm G (term_inst e t)  (open_typ_wrt_typ  t'   t ) 
 | wfterm_gen : forall (L:vars) (G:typing_env) (e:term) (t:typ),
      (pure ( G ))  ->
      ( forall a , a \notin  L  -> wfterm  ( a ~U ++  G )   ( open_term_wrt_typ e (typ_var_f a) )   ( open_typ_wrt_typ t (typ_var_f a) )  )  ->
     wfterm G (term_gen e) (typ_forall t)
 | wfterm_exists : forall (L:vars) (G:typing_env) (e:term) (t:typ),
      ( forall a , a \notin  L  -> wfterm  ( a ~E ++  G )   ( open_term_wrt_typ e (typ_var_f a) )   ( open_typ_wrt_typ t (typ_var_f a) )  )  ->
     wfterm G (term_exists e) (typ_exists t)
 | wfterm_open : forall (G1:typing_env) (b:typvar) (G2:typing_env) (e:term) (t:typ),
      b  `notin` dom   (  (( G2 ) ++ ( G1 ))  )   ->
     wfterm  (( G2 ) ++ ( G1 ))  e (typ_exists t) ->
     wfterm  (( G2 ) ++ (  (  ( b ~E ++  G1 )  )  ))  (term_open (typ_var_f b) e)  (open_typ_wrt_typ  t   (typ_var_f b) ) 
 | wfterm_nu : forall (L:vars) (G:typing_env) (e:term) (t:typ),
      ( forall a , a \notin  L  -> wfterm  ( a ~E ++  G )   ( open_term_wrt_typ e (typ_var_f a) )  t )  ->
     wfterm G (term_nu e) t
 | wfterm_sigma : forall (L:vars) (G1:typing_env) (b:typvar) (G2:typing_env) (t':typ) (e:term) (t:typ),
      b  `notin` dom   (  (( G2 ) ++ ( G1 ))  )   ->
      ( forall a , a \notin  L  -> wfterm  ( a ~(Eq  t' ) ++   (  (( G2 ) ++ ( G1 ))  )  )   ( open_term_wrt_typ e (typ_var_f a) )   (tsubst_typ (typ_var_f a) b  t) )  ->
     wfterm  (( G2 ) ++ (  (  ( b ~E ++  G1 )  )  ))  (term_sigma (typ_var_f b) t' e) t
 | wfterm_coerce : forall (G:typing_env) (e:term) (t t':typ),
     wftypeq G t' t ->
     wfterm G e t' ->
     wfterm G (term_coerce e t) t.

(* defns Jred0 *)
Inductive red0 : term -> term -> Prop :=    (* defn red0 *)
 | red0_beta_v_red : forall (t:typ) (e1 e2:term),
     lc_typ t ->
     lc_term (term_abs t e1) ->
     val e2 ->
     red0 (term_app  ( (term_abs t e1) )  e2) (term_let e2 e1)
 | red0_beta_v_let : forall (e1 e2:term),
     lc_term (term_let e1 e2) ->
     val e1 ->
     red0 (term_let e1 e2)  (open_term_wrt_term  e2   e1 ) 
 | red0_pi_fst : forall (e1 e2:term),
     val (term_pair e1 e2) ->
     red0 (term_fst (term_pair e1 e2)) e1
 | red0_pi_snd : forall (e1 e2:term),
     val (term_pair e1 e2) ->
     red0 (term_snd (term_pair e1 e2)) e2
 | red0_beta_t : forall (e:term) (t:typ),
     lc_term (term_gen e) ->
     lc_typ t ->
     red0 (term_inst  ( (term_gen e) )  t)  (open_term_wrt_typ   e    t ) 
 | red0_open_exists : forall (L:vars) (b:typvar) (e:term),
      ( forall a , a \notin  L  -> result  ( open_term_wrt_typ e (typ_var_f a) )  )  ->
     red0 (term_open (typ_var_f b) (term_exists e))  (open_term_wrt_typ   e    (typ_var_f b) ) 
 | red0_nu_sigma : forall (L:vars) (t:typ) (e e':term),
   ( forall b , b \notin  L  ->  lc_typ (  ( open_typ_wrt_typ t (typ_var_f b) )  )  )  ->
   ( forall b , b \notin  L  ->  b  `notin` ftv_typ (  ( open_typ_wrt_typ t (typ_var_f b) )  )  )  ->
   ( forall b , b \notin  L  ->  b  `notin` ftv_term (  ( open_term_wrt_typ e (typ_var_f b) )  )  )  ->
   ( forall b a, b \notin  L -> a \notin   L  \u {{ b }}  ->
     forall t1 e1 e2,
       open_term_wrt_typ (term_sigma (typ_var_b 0) t e) (typ_var_f b)
       = term_sigma (typ_var_f b) t1 e1 ->
       open_term_wrt_typ e1 (typ_var_f a) = e2 ->
       result e2 ) ->
   ( forall b a, b \notin L -> a \notin L \u {{ b }} ->
     forall e1 e2,
       open_term_wrt_typ (term_sigma (typ_var_b 0) t e) (typ_var_f b)
       = term_sigma (typ_var_f b) (open_typ_wrt_typ t (typ_var_f b)) e1 ->
       open_term_wrt_typ e1 (typ_var_f a) = e2 ->
       e' = tsubst_term (open_typ_wrt_typ t (typ_var_f b)) a e2) ->
   red0 (term_nu (term_sigma (typ_var_b 0) t e)) e'
 | red0_coerce_app : forall (t2':typ) (e1:term) (t2 t1:typ) (e2:term),
     lc_typ t2 ->
     lc_term (term_abs t2' e1) ->
     lc_typ t2' ->
     lc_typ t1 ->
     val e2 ->
     red0 (term_app (term_coerce (term_abs t2' e1) (typ_arrow t2 t1)) e2) (term_coerce (term_app  ( (term_abs t2' e1) )  (term_coerce e2 t2')) t1)
 | red0_coerce_fst : forall (e1 e2:term) (t1 t2:typ),
     lc_typ t2 ->
     lc_typ t1 ->
     val (term_pair e1 e2) ->
     red0 (term_fst (term_coerce (term_pair e1 e2) (typ_prod t1 t2))) (term_coerce (term_fst (term_pair e1 e2)) t1)
 | red0_coerce_snd : forall (e1 e2:term) (t1 t2:typ),
     lc_typ t1 ->
     lc_typ t2 ->
     val (term_pair e1 e2) ->
     red0 (term_snd (term_coerce (term_pair e1 e2) (typ_prod t1 t2))) (term_coerce (term_snd (term_pair e1 e2)) t2)
 | red0_coerce_inst : forall (e:term) (t1 t2:typ),
     lc_typ (typ_forall t1) ->
     lc_term (term_gen e) ->
     lc_typ t2 ->
     red0 (term_inst (term_coerce (term_gen e) (typ_forall t1)) t2) (term_coerce (term_inst  ( (term_gen e) )  t2)  (open_typ_wrt_typ  t1   t2 ) )
 | red0_coerce_open : forall (b:typvar) (e:term) (t:typ),
     lc_typ (typ_exists t) ->
     val (term_exists e) ->
     red0 (term_open (typ_var_f b) (term_coerce (term_exists e) (typ_exists t))) (term_coerce (term_open (typ_var_f b) (term_exists e))  (open_typ_wrt_typ  t   (typ_var_f b) ) )
 | red0_coerce_coerce : forall (e:term) (t1 t2:typ),
     lc_typ t2 ->
     val (term_coerce e t1) ->
     red0 (term_coerce (term_coerce e t1) t2) (term_coerce e t2)
 | red0_sigma_appL : forall (L:vars) (b:typvar) (t:typ) (e1 e2 e2':term),
     result (term_sigma (typ_var_f b) t e1) ->
     result e2 ->
     (forall a , a \notin  L -> open_term_wrt_typ e2' (typ_var_f a) = tsubst_term (typ_var_f a) b e2) ->
     red0 (term_app (term_sigma (typ_var_f b) t e1) e2) (term_sigma (typ_var_f b) t  (term_app e1  e2'))
 | red0_sigma_appR : forall (L:vars) (e1 e1':term) (b:typvar) (t:typ) (e2:term),
     val e1 ->
     result (term_sigma (typ_var_f b) t e2) ->
     (forall a , a \notin  L  -> open_term_wrt_typ e1' (typ_var_f a) = tsubst_term (typ_var_f a) b e1) ->
      red0 (term_app e1 (term_sigma (typ_var_f b) t e2)) (term_sigma (typ_var_f b) t (term_app e1' e2))

 | red0_sigma_pairL : forall (L:vars) (b:typvar) (t:typ) (e1 e2 e2':term),
     result (term_sigma (typ_var_f b) t e1) ->
     result e2 ->
     (forall a , a \notin  L -> open_term_wrt_typ e2' (typ_var_f a) = tsubst_term (typ_var_f a) b e2) ->
     red0 (term_pair (term_sigma (typ_var_f b) t e1) e2) (term_sigma (typ_var_f b) t  (term_pair e1  e2'))
 | red0_sigma_pairR : forall (L:vars) (e1 e1':term) (b:typvar) (t:typ) (e2:term),
     val e1 ->
     result (term_sigma (typ_var_f b) t e2) ->
     (forall a , a \notin  L  -> open_term_wrt_typ e1' (typ_var_f a) = tsubst_term (typ_var_f a) b e1) ->
      red0 (term_pair e1 (term_sigma (typ_var_f b) t e2)) (term_sigma (typ_var_f b) t (term_pair e1' e2))
 | red0_sigma_fst : forall (b:typvar) (t:typ) (e:term),
     result (term_sigma (typ_var_f b) t e) ->
     red0 (term_fst (term_sigma (typ_var_f b) t e)) (term_sigma (typ_var_f b) t (term_fst e))
 | red0_sigma_snd : forall (b:typvar) (t:typ) (e:term),
     result (term_sigma (typ_var_f b) t e) ->
     red0 (term_snd (term_sigma (typ_var_f b) t e)) (term_sigma (typ_var_f b) t (term_snd e))
 | red0_sigma_inst : forall (L:vars) (b:typvar) (t:typ) (e:term) (t' t'':typ),
     lc_typ t' ->
     result (term_sigma (typ_var_f b) t e) ->
     (forall a , a \notin  L  -> open_typ_wrt_typ t'' (typ_var_f a) = tsubst_typ (typ_var_f a) b t') ->
     red0 (term_inst (term_sigma (typ_var_f b) t e) t')
     (term_sigma (typ_var_f b) t  (term_inst e t''))
 | red0_sigma_open : forall (c b:typvar) (t:typ) (e:term),
     result (term_sigma (typ_var_f b) t e) ->
     red0 (term_open (typ_var_f c) (term_sigma (typ_var_f b) t e)) (term_sigma (typ_var_f b) t (term_open (typ_var_f c) e))
 | red0_sigma_sigma : forall (L:vars) (b1:typvar) (t1 t1':typ) (b2:typvar) (t2:typ) (e e':term),
     lc_term (term_sigma (typ_var_f b1) t1 (term_sigma (typ_var_f b2) t2 e)) ->
      ( forall a1 , a1 \notin  L  ->  ( forall a2 , a2 \notin   L  \u {{ a1 }}  -> result  (open_term_wrt_typ_rec 0 (typ_var_f a1) (open_term_wrt_typ_rec 1 (typ_var_f a2) e) )  )  )  ->
      ( forall a2, a2 \notin L -> t1 = open_typ_wrt_typ t1' (typ_var_f a2) ) ->
      ( forall a1 a2, a1 \notin L -> a2 \notin L \u {{ a1 }} ->
        open_term_wrt_typ_rec 0 (typ_var_f a2) (open_term_wrt_typ_rec 1 (typ_var_f a1) e)
        = open_term_wrt_typ_rec 0 (typ_var_f a1) (open_term_wrt_typ_rec 1 (typ_var_f a2) e') ) ->
      red0 (term_sigma (typ_var_f b1) t1 (term_sigma (typ_var_f b2) t2 e)) (term_sigma (typ_var_f b2) (open_typ_wrt_typ t2 t1) (term_sigma (typ_var_f b1) t1' e')) .

(* defns Jred1 *)
Inductive red1 : term -> term -> Prop :=    (* defn red1 *)
 | red1_empty : forall (e e':term),
     red0 e e' ->
     red1 e e'
 | red1_let : forall (e1 e2 e1':term),
     lc_term (term_let e1 e2) ->
     red1 e1 e1' ->
     red1 (term_let e1 e2) (term_let e1' e2)
 | red1_appL : forall (e1 e2 e1':term),
     lc_term e2 ->
     red1 e1 e1' ->
     red1 (term_app e1 e2) (term_app e1' e2)
 | red1_appR : forall (e1 e2 e2':term),
     lc_term e1 ->
     red1 e2 e2' ->
     red1 (term_app e1 e2) (term_app e1 e2')
 | red1_pairL : forall (e1 e2 e1':term),
     lc_term e2 ->
     red1 e1 e1' ->
     red1 (term_pair e1 e2) (term_pair e1' e2)
 | red1_pairR : forall (e1 e2 e2':term),
     lc_term e1 ->
     red1 e2 e2' ->
     red1 (term_pair e1 e2) (term_pair e1 e2')
 | red1_fst : forall (e e':term),
     red1 e e' ->
     red1 (term_fst e) (term_fst e')
 | red1_snd : forall (e e':term),
     red1 e e' ->
     red1 (term_snd e) (term_snd e')
 | red1_inst : forall (e:term) (t:typ) (e':term),
     lc_typ t ->
     red1 e e' ->
     red1 (term_inst e t) (term_inst e' t)
 | red1_exists : forall (L:vars) (e e':term),
      ( forall a , a \notin  L  -> red1  ( open_term_wrt_typ e (typ_var_f a) )   ( open_term_wrt_typ e' (typ_var_f a) )  )  ->
     red1 (term_exists e) (term_exists e')
 | red1_open : forall (b:typvar) (e e':term),
     red1 e e' ->
     red1 (term_open (typ_var_f b) e) (term_open (typ_var_f b) e')
 | red1_nu : forall (L:vars) (e e':term),
      ( forall a , a \notin  L  -> red1  ( open_term_wrt_typ e (typ_var_f a) )   ( open_term_wrt_typ e' (typ_var_f a) )  )  ->
     red1 (term_nu e) (term_nu e')
 | red1_sigma : forall (L:vars) (b:typvar) (t:typ) (e e':term),
     lc_typ t ->
      ( forall a , a \notin  L  -> red1  ( open_term_wrt_typ e (typ_var_f a) )   ( open_term_wrt_typ e' (typ_var_f a) )  )  ->
     red1 (term_sigma (typ_var_f b) t e) (term_sigma (typ_var_f b) t e')
 | red1_coerce : forall (e:term) (t:typ) (e':term),
     lc_typ t ->
     red1 e e' ->
     red1 (term_coerce e t) (term_coerce e' t).

(** infrastructure *)

(* additional definitions *)


(* instanciation of tactics *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let D1 := gather_atoms_with (fun x => fv_term x) in
  let D2 := gather_atoms_with (fun x => ftv_typ x) in
  let D3 := gather_atoms_with (fun x => ftv_term x) in
  constr:(A \u B \u D1 \u D2 \u D3).

Hint Constructors val result zip wfenv wftyp wftypeq wfterm red0 red1 lc_typ lc_term.




