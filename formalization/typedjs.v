Add LoadPath "metatheory".
Require Import Metatheory.
Require Import Dataflow.

Inductive typ : Set :=
  | typ_int  : typ
  | typ_str : typ
  | typ_bool : typ
  | typ_arrow : typ -> typ -> typ
  | typ_union : typ -> typ -> typ.

Axiom typ_union_symm : forall t1 t2, typ_union t1 t2 = typ_union t2 t1.

Inductive string : Set :=
  string_const : string.

Inductive const : Set :=
  | const_int : nat -> const
  | const_bool : bool -> const
  | const_str : string -> const.

Inductive exp : Set :=
  | bvar : nat  -> exp    (* bound variables *)
  | fvar : RTS -> atom -> exp   (* free  variables *)
  | abs  : typ -> exp  -> exp (* type of the binding instance *)
  | app  : exp  -> exp -> exp
  | e_const : const -> exp
  | cond : exp -> exp -> exp -> exp.

Inductive static : rts.t -> typ -> typ -> Prop :=
  | ast_integer : forall r, rts.In rt_number r -> 
      static r typ_int typ_int
  | ast_string : forall r, rts.In rt_string r ->
      static r typ_str typ_str
  | ast_boolean : forall r, rts.In rt_boolean r ->
      static r typ_bool typ_bool
  | ast_arrow : forall r t1 t2, rts.In rt_function r ->
      static r (typ_arrow t1 t2) (typ_arrow t1 t2)
  | ast_union: forall r t1 t2 t1' t2',
      static r t1 t1' ->
      static r t2 t2' -> 
      static r (typ_union t1 t2) (typ_union t1' t2')
  | ast_unionL : forall r t1 t2 t1',
      static r t1 t1' ->
      static r (typ_union t1 t2) t1'
  | ast_unionR : forall r t1 t2 t2',
      static r t2 t2' ->
      static r (typ_union t1 t2) t2'.

Fixpoint runtime (t : typ) { struct t } : rts.t:=
  match t with
  | typ_int =>  rts.singleton rt_number
  | typ_str => rts.singleton rt_string
  | typ_bool => rts.singleton rt_boolean
  | typ_arrow _ _ => rts.singleton rt_function
  | typ_union t1 t2 => rts.union (runtime t1) (runtime t2)
  end.

Inductive subtype : typ -> typ -> Prop :=
  | subtype_refl : forall (t : typ), 
      subtype t t
  | subtype_trans : forall (s t u : typ), 
      subtype s u ->
      subtype u t -> 
      subtype s t
  | subtype_arrow : forall (s1 s2 t1 t2 : typ),
      subtype t1 s1 ->
      subtype s2 t2 -> 
      subtype (typ_arrow s1 s2) (typ_arrow t1 t2)
  | subtype_unionL : forall (s1 s2 t1 t2 : typ),
      subtype s1 t1 ->
      subtype s2 t2 ->
      subtype (typ_union s1 s2) (typ_union t1 t2)
  | subtype_unionRL : forall (s t1 t2 : typ),
      subtype s t1 -> 
      subtype s (typ_union t1 t2)
  | subtype_unionRR : forall (s t1 t2 : typ),
      subtype s t2 -> 
      subtype s (typ_union t1 t2).


Inductive typing_const : const -> typ -> Prop :=
  | typing_int : forall n, typing_const (const_int n) typ_int
  | typing_bool : forall b, typing_const (const_bool b) typ_bool
  | typing_str : forall s, typing_const (const_str s) typ_str.

Inductive runtime_type_const : const -> RT -> Prop :=
  | runtime_type_const_int : forall n, runtime_type_const (const_int n) rt_number
  | runtime_type_const_bool : forall b, runtime_type_const (const_bool b) rt_boolean
  | runtime_type_const_str : forall s, runtime_type_const (const_str s) rt_string.

Inductive runtime_type : exp -> RT -> Prop :=
  | typeof_const : forall c rt,
      runtime_type_const c rt ->
      runtime_type (e_const c) rt
  | typeof_abs : forall t e, runtime_type (abs t e) rt_function.

Inductive subst : atom -> exp -> exp -> exp -> Prop :=
  | subst_bvar : forall z u (i : nat), subst z u (bvar i) (bvar i)
  | subst_fvar_noop : forall z u r (x : atom),
      x <> z -> subst z u (fvar r x) (fvar r x)
  | subst_fvar : forall (z : atom) r rt (u : exp), 
      runtime_type u rt ->
      rts.In rt r ->
      subst z u (fvar r z) u
  | subst_abs : forall z u t e1 e1',
      subst z u e1 e1' ->
      subst z u (abs t e1) (abs t e1')
  | subst_app : forall z u e1 e2 e1' e2',
      subst z u e1 e1' ->
      subst z u e2 e2' ->
      subst z u (app e1 e2) (app e1' e2')
  | subst_const : forall z u (c : const),
      subst z u (e_const c) (e_const c)
  | subst_cond : forall z u (e1 e2 e3 e1' e2' e3' : exp),
      subst z u e1 e1' ->
      subst z u e2 e2' ->
      subst z u e3 e3' ->
      subst z u (cond e1 e2 e3) (cond e1' e2' e3').

Fixpoint open_rec (k : nat) (u : exp) (e : exp) {struct e} : exp :=
  match e with
    | bvar i => if k === i then u else (bvar i)
    | fvar r x => fvar r x
    | abs t e1 => abs t (open_rec (S k) u e1)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
    | e_const c => e_const c
    | cond e1 e2 e3 => cond (open_rec k u e1) 
                            (open_rec k u e2)
                            (open_rec k u e3)
  end.

Definition open e u := open_rec 0 u e.

Notation env := (list (atom * typ)).

Inductive lc : exp -> Prop :=
  | lc_var : forall r x,
      lc (fvar r x)
  | lc_abs : forall L e T,
      (forall x:atom, x `notin` L -> lc (open e (fvar (runtime T) x))) ->
      lc (abs T e)
  | lc_app : forall e1 e2,
      lc e1 ->
      lc e2 ->
      lc (app e1 e2)
  | lc_e_const : forall c,
      lc (e_const c)
  | lc_cond : forall e1 e2 e3,
      lc e1 -> lc e2 -> lc e3 -> lc (cond e1 e2 e3).

Inductive value : exp -> Prop :=
  | value_abs : forall t e,
      lc (abs t e) ->
      value (abs t e)
  | value_const : forall c,
      value (e_const c).

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E (x : atom) r S T,
      ok E ->
      binds x T E ->
      static r T S ->
      typing E (fvar r x) S
  | typing_abs : forall L E e T1 T2,
      (forall x : atom, x `notin` L ->
        typing ((x, T1) :: E) (open e (fvar (runtime T1) x)) T2) ->
      typing E (abs T1 e) (typ_arrow T1 T2)
  | typing_app : forall E e1 e2 T1 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (app e1 e2) T2
  | typing_e_const : forall E c T,
      typing_const c T ->
      typing E (e_const c) T
  | typing_cond : forall E e1 e2 e3 T,
      typing E e1 typ_bool ->
      typing E e2 T ->
      typing E e3 T ->
      typing E (cond e1 e2 e3) T
  | typing_sub : forall E e S T,
      subtype S T ->
      typing E e S ->
      typing E e T.

Inductive typing_soundness : env -> exp -> typ -> Prop :=
  | typing_static : forall E e T,
      typing E e T -> 
      typing_soundness E e T
  | typing_runtime : forall E e rt r S T,
      value e ->
      typing E e S ->
      runtime_type e rt ->
      rts.In rt r ->
      static r S T ->
      typing_soundness E e T.

Inductive eval : exp -> exp -> Prop :=
  | eval_beta : forall t e1 e2,
      lc (abs t e1) ->
      value e2 ->
      eval (app (abs t e1) e2) (open e1 e2)
  | eval_app_1 : forall e1 e1' e2,
      lc e2 ->
      eval e1 e1' ->
      eval (app e1 e2) (app e1' e2)
  | eval_app_2 : forall e1 e2 e2',
      value e1 ->
      eval e2 e2' ->
      eval (app e1 e2) (app e1 e2')
  | cxt_cond : forall e1 e2 e3 e1',
      eval e1 e1' ->
      lc e2 ->
      lc e3 ->
      eval (cond e1 e2 e3) (cond e1' e2 e3)
  | eval_cond_true : forall e2 e3,
      lc e2 ->
      lc e3 ->
      eval (cond (e_const (const_bool true)) e2 e3) e2
  | eval_cond_false : forall e2 e3,
      lc e2 ->
      lc e3 ->
      eval (cond (e_const (const_bool false)) e2 e3) e3.

Hint Constructors typing typing_const subst lc value eval runtime_type
  runtime_type_const typing_soundness.

Fixpoint fv (e : exp) {struct e} : atoms :=
  match e with
    | bvar i => {}
    | fvar r x => singleton x
    | abs t e1 => fv e1
    | app e1 e2 => (fv e1) `union` (fv e2)
    | e_const c => {}
    | cond e1 e2 e3 => (fv e1) `union` (fv e2) `union` (fv e3)
  end.

(*****************************************************************************
 * Tactics                                                                   *
 *****************************************************************************)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv x) in
  constr:(A `union` B `union` C `union` D).

(** We can use [gather_atoms] to define a variant of the [(pick fresh
    x for L)] tactic, which we call [(pick fresh x)].  The tactic
    chooses an atom fresh for "everything" in the context. *)

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in
  (pick fresh x for L).

(** We can also use [gather_atoms] to define a tactic for applying a
    rule that is defined using cofinite quantification.  The tactic
    [(pick fresh x and apply H)] applies a rule [H], just as the
    [apply] tactic would.  However, the tactic also picks a
    sufficiently fresh name [x] to use.

    Note: We define this tactic in terms of another tactic, [(pick
    fresh x excluding L and apply H)], which is defined and documented
    in [Metatheory.v]. *)

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.

(*****************************************************************************
 * Lemmas                                                                    *
 *****************************************************************************)

Lemma subtype_coherence: forall S T,
  subtype S T ->
  rts.Subset (runtime S) (runtime T).
Proof.
  intros S T H.
  induction H; subst.
  (* reflexivity *)
  simpl. apply rts_props.subset_equal. reflexivity.
  (* transitivity *)
  eapply rts_props.subset_trans.
    apply IHsubtype1. apply IHsubtype2.
  (* functions *)
  simpl. apply rts_props.subset_equal. reflexivity.
  (* unionL *)
  simpl. 
  assert (rts.Subset (runtime s1) (rts.union (runtime t1) (runtime t2))).
    eapply rts_props.subset_trans. apply IHsubtype1.
    apply rts_props.union_subset_1.
  assert (rts.Subset (runtime s2) (rts.union (runtime t1) (runtime t2))).
    eapply rts_props.subset_trans. apply IHsubtype2.
    apply rts_props.union_subset_2.
  apply rts_props.union_subset_3.
    exact H1. exact H2.
  (* unionRL *)
  simpl.
  eapply rts_props.subset_trans.
    apply IHsubtype.
  apply rts_props.union_subset_1.
  (* unionRR *)
  simpl.
  eapply rts_props.subset_trans.
    apply IHsubtype.
  apply rts_props.union_subset_2.
Qed.

Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  open_rec j v e = open_rec i u (open_rec j v e) ->
  e = open_rec i u e.
Proof with eauto*.
  induction e; intros j v i u Neq H; simpl in *;
      try solve [inversion H; f_equal; eauto].
  Case "bvar".
    destruct (j === n)...
    destruct (i === n)...
Qed.

Lemma open_rec_lc : forall k u e,
  lc e ->
  e = open_rec k u e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_fvar".
    simpl. auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
    unfold open in *.
    pick fresh x for L.
    apply open_rec_lc_core with (i := S k) (j := 0) (u := u) (v := fvar (runtime T) x). auto. auto.
  Case "lc_app".
    intro k. simpl. f_equal. auto. auto.
  (* e_const *)
  auto.
  (* cond *)
  intros. simpl. f_equal; auto.
Qed.

Lemma subst_open_rec : forall e1 e2 e1' e2' u x k,
  lc u ->
  subst x u e1 e1' ->
  subst x u e2 e2' ->
  subst x u (open_rec k e2 e1) (open_rec k e2' e1').
Proof.
  induction e1; intros.
  (* bvar *)
  inversion H0. subst.
  simpl.
  destruct (k === n); auto.
  (* fvar *)
  inversion H0. subst. simpl. exact H0. simpl. subst.
  assert (e1' = open_rec k e2' e1'). apply open_rec_lc. exact H.
  rewrite <- H2. exact H0.
  (* abs *)
  inversion H0. simpl. auto.
  inversion H0. subst.  simpl in *. auto.
  (* const *)
  inversion H0. subst. auto.
  (* cond *)
  inversion H0. subst. simpl. auto.
Qed.

Lemma typing_regular_lc : forall E e T,
  typing E e T -> lc e.
Proof.
  intros E e T H. induction H; eauto.
Qed.


Lemma subst_open_var : forall (x y : atom) u r e e1,
  y <> x ->
  lc u ->
  subst x u e e1 ->
  subst x u (open e (fvar r y)) (open e1 (fvar r y)).
Proof.
  intros x y u r e e1 e2 Neq Hrt.
  unfold open in *.
  apply subst_open_rec.
    exact Neq.
    exact Hrt.
    auto.
Qed.

Lemma subst_lc : forall (x : atom) u e e',
  lc e ->
  lc u ->
  subst x u e e' ->
  lc e'.
Proof.
  intros x u e e' He Hu Hsubst.
  generalize dependent e'.
  induction He; intros; inversion Hsubst; subst.
  destruct (x0 == x). auto. auto. auto.
  (* abs *)
  pick fresh y and apply lc_abs.
  assert (subst x u (open e (fvar (runtime T) y)) (open e1' (fvar (runtime T) y))).
    eapply subst_open_var; auto.
  apply H0 with (x0 := y). fsetdec. exact H1.
  (* app, cond, const *)
  auto. auto. auto.
Qed.

Lemma subst_fresh : forall (x : atom) e u,
  x `notin` fv e -> subst x u e e.
Proof.
  intros x e u.
  intros H.
  induction e.
    apply subst_bvar.
    apply subst_fvar_noop.
      unfold not.
      intros.
      unfold fv in H.
      assert (x `notin` singleton a -> False). fsetdec.
      apply H1. exact H.
    apply subst_abs.
      apply IHe.
      fsetdec.
    simpl in H.
    apply subst_app.
      apply IHe1. fsetdec.
      apply IHe2. fsetdec.
    apply subst_const.
    apply subst_cond; simpl in H; auto.
Qed. 

Lemma subst_intro : forall (x : atom) u e r rt,
  value u ->
  runtime_type u rt ->
  rts.In rt r ->
  x `notin` (fv e) ->
  lc u ->
  subst x u (open e (fvar r x)) (open e u).
Proof.
  intros x u e r rt Value Hruntime Hconsistent H J.
  unfold open.
  apply subst_open_rec.
    exact J. apply subst_fresh. exact H.
    eauto.
Qed.

Lemma single_runtime_type : forall val r1 r2,
  runtime_type val r1 ->
  runtime_type val r2 ->
  r1 = r2.
Proof.
  intros val r1 r2 Hrt1 Hrt2.
  inversion Hrt1; inversion Hrt2; subst.
  inversion H; inversion H2; subst; (reflexivity || inversion H3).
  inversion H2.
  inversion H2.
  reflexivity.
Qed.

Lemma static_sub : forall R S T,
  static R S T ->
  subtype T S.
Proof.
  intros R S T Hstatic. 
  induction Hstatic; try (apply subtype_refl).
  (* ast_union *)
  apply subtype_trans with (u := typ_union t1' t2').
  apply subtype_refl.
  apply subtype_unionL.
  apply IHHstatic1.
  apply IHHstatic2.
  (* ast_unionL *)
  apply subtype_unionRL. exact IHHstatic.
  (* ast_unionR *)
  apply subtype_unionRR. exact IHHstatic.
Qed.

(************
* Weakening *
************)

Lemma typing_static_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  ok (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G Eq Ok; subst; try eauto.
  (* typing_abs *)
  pick fresh x and apply typing_abs.
  rewrite <- cons_concat_assoc.
  apply H0.
  auto.
  rewrite cons_concat_assoc. reflexivity.
  rewrite cons_concat_assoc. apply ok_cons.
  apply Ok.
  auto.
Qed.

Lemma typing_weakening_strengthened :  forall E F G e T,
  typing_soundness (G ++ E) e T ->
  ok (G ++ F ++ E) ->
  typing_soundness (G ++ F ++ E) e T.
Proof.
  intros E F G e T H Ok.
  inversion H; subst.
  (* static typing *)
  apply typing_static.
  apply typing_static_weakening. exact H0. exact Ok.
  (* runtime typing *)
  eapply typing_runtime.
  exact H0.
  apply typing_static_weakening. apply H1. exact Ok.
  apply H2.
  apply H3.
  exact H4.
Qed.

Lemma typing_weakening : forall E F e T,
    typing_soundness E e T ->
    ok (F ++ E) ->
    typing_soundness (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite <- (nil_concat _ (F ++ E)).
  apply typing_weakening_strengthened; auto.
Qed.

(********************************************************************)
(* Coherence                                                        *)
(********************************************************************)

Lemma const_coherence : forall c rt T,
  typing_const c T ->
  runtime_type_const c rt ->
  rts.In rt (runtime T).
Proof.
  intros c rt T HypT HypRT.
  inversion HypT; subst; inversion HypRT; subst; simpl; fsetdec.
Qed.

Lemma static_coherence : forall E val rt T,
  value val ->
  typing E val T ->
  runtime_type val rt ->
  rts.In rt (runtime T).
Proof.
  intros E val rt T Hvalue Htyping Hrt.
  induction Htyping; inversion Hvalue.
  (* functions *)
  inversion Hrt.
  simpl.
  rewrite -> RTSFacts.singleton_iff.
  reflexivity.
  (* flat values *)
  subst.
  inversion Hrt.
  eapply const_coherence. apply H. apply H1.
  (* subtypes of functions *)
  inversion Hrt; subst. inversion H3. (* contradiction *)  
  assert (rts.Subset (runtime S) (runtime T)).
    apply subtype_coherence. exact H.
  assert (rts.In rt_function (runtime S)).
    apply IHHtyping in Hvalue. exact Hvalue.
    exact Hrt.
  eapply rts_props.in_subset. apply H3. exact H1.
  (* subtypes of flat values *) 
  subst.
  assert (rts.Subset (runtime S) (runtime T)).
    apply subtype_coherence. exact H.
  assert (rts.In rt (runtime S)).
    apply IHHtyping in Hvalue. exact Hvalue.
    exact Hrt.
  eapply rts_props.in_subset. apply H1. exact H0.
Qed.

Theorem coherence : forall E val rt T,
  value val ->
  typing_soundness E val T ->
  runtime_type val rt ->
  rts.In rt (runtime T).
Proof.
  intros E val rt T Hvalue Htyping Hrt.
  inversion Htyping; subst.
  eapply static_coherence; eauto.
  (* runtime typing *)
  assert (subtype T S). eapply static_sub. apply H3.
  assert (rts.Subset (runtime T) (runtime S)).
    eapply subtype_coherence. exact H4.
  assert (rt0 = rt); subst. eapply single_runtime_type; eauto.
  apply static_coherence with (rt := rt) (T := S) (E := E) in H.
    exact H.



  apply static_sub in H3.
  apply subtype_coherence in H3.
  apply static_coherence with (rt := rt0) in H0.
    eapply rts_props.in_subset. apply H0.  
  Check runtime_static_coherence.
  eapply runtime_static_coherence; eauto.
  eapply runtime_static_coherence; eauto.
Qed.

(***************
* Substitution *
***************)

  

Lemma typing_subst_strengthened : forall E F e e' u S T z,
  value u ->
  typing_soundness (F ++ (z, S) :: E) e T ->
  typing_soundness E u S ->
  subst z u e e' ->
  typing_soundness (F ++ E) e' T.
Proof.
  intros F E e e' u S T z Value.
  remember (E ++ (z, S) :: F) as G. 
  intros Hyp0 Hyp1.
  generalize dependent E.
  generalize dependent F.
  generalize dependent e'.
  inversion Hyp0; subst.
  induction H.
  (* var *)
  intros.
  subst.
  (* we know typing (E0 ++ (z, S) :: F) (fvar r x) S0 *)
  destruct (x == z).
    subst.
    assert (T = S). eapply binds_mid_eq_cons. apply H0. apply H.
    subst.
    inversion H2. subst. contradiction H8. reflexivity.
    subst. apply typing_weakening.
    Focus 2. eapply ok_remove_mid_cons. apply H.
    eapply typing_runtime.
      exact
  
    assert (typing F e' S).
      inversion Hyp1; subst. exact H3.
      assert (rt = rt0); subst. 
        eapply single_runtime_type; eauto.
      

      
   
      exact Value.
      apply Hyp1.
      apply H4.
      apply H7.
      apply H1.
    (* x <> z *)
    inversion H2; subst.
      eapply typing_var.
      eapply ok_remove_mid_cons. apply H.
      eapply binds_remove_mid_cons. apply H0.
      exact H8.
      exact H1.
      contradiction n. reflexivity.
  (* abs *)
  intros. inversion H1. subst.
  pick fresh x and apply typing_abs.
  assert (typing ((x, T1) :: E0 ++ (z, S) :: F) (open e (fvar (runtime T1) x)) T2) as HypPre.
    apply H.
    fsetdec.
  assert (subst z u (open e (fvar (runtime T1) x)) (open e1' (fvar (runtime T1) x))) as HypSubst.
    apply subst_open_var. fsetdec. eapply typing_regular_lc. apply Hyp1. apply H7.
  assert (x `notin` L). fsetdec.
  apply H0 with (e' := open e1' (fvar (runtime T1) x)) (E := (x, T1) :: E0)
                (F0 := F) (x := x); auto.
  (* app *)
  intros. inversion H. subst. eapply typing_app; auto.
  (* const *) 
  intros. inversion H0. subst. eapply typing_e_const; auto.
  (* cond *)
  intros. inversion H. subst. eapply typing_cond; auto.
  (* subtyping *)
  intros. eapply typing_sub. apply H. apply IHHyp0; auto.
  (* runtime-typing *)
  intros. subst.
  inversion H3; subst; inversion H. (* dismiss non-values *)
  subst.
  eapply typing_runtime.
    apply value_abs; auto. apply typing_regular_lc in Hyp1.
    apply subst_lc with (u := u) (e' := abs t e1') (e := abs t e1) (x := z); auto.
    apply IHHyp0; auto.
    apply typeof_abs.
    inversion H0. subst. apply H1.
    apply H2.
  eapply typing_runtime; auto. apply H0. apply H1. apply H2.
Qed.

Lemma typing_subst : forall E e e' u S T z,
  value u ->
  typing ((z, S) :: E) e T ->
  typing E u S ->
  subst z u e e' ->
  typing E e' T.
Proof.
  intros E e e' u S T z Value HypInd HypS HypSubst.
  assert (nil ++ E = E) as HypNilConcat. apply nil_concat.
  rewrite <- HypNilConcat.
  apply typing_subst_strengthened with (S := S) (u := u) (z := z) (e := e). 
    simpl. exact Value. exact HypInd. exact HypS. exact HypSubst.
Qed.



(*************************************************************************)
(** * Preservation *)
(*************************************************************************)


Hint Constructors runtime_type.

Lemma singleton_subset_neq : forall x y,
  x <> y ->
  ~ rts.Subset (rts.singleton x) (rts.singleton y).
Proof.
  unfold not. 
  intros.
  assert (rts.In x (rts.singleton x)). fsetdec.
  assert (rts.In x (rts.singleton y)).
    apply rts_props.in_subset with (s1 := rts.singleton x); auto.
  assert (y = x).
     rewrite <- RTSFacts.singleton_iff. exact H2.
  contradiction H.
    rewrite <- H3. reflexivity.
Qed.





Lemma typing_const_inv : forall E c S,
  typing E (e_const c) S ->
  exists T, typing_const c T /\ subtype T S.
Proof.
  intros E c S Htyping.
  remember (e_const c) as const.
  induction Htyping; inversion Heqconst0; subst.
Focus 3.
  assert (typing E (e_const c) T) as HtypingT. eapply typing_runtime; eauto.
  apply IHHtyping in H3.
  destruct H3 as [T' [Htyping' Hsub]].
  exists T'. split. exact Htyping'.
  apply static_coherence in H2.
    inversion HtypingT; subst.
    assert (T = T').
      inversion Htyping'; inversion H5; subst; 
      (reflexivity || inversion H5 || inversion Htyping').
    rewrite -> H3.
    apply subtype_refl.
    (* subtyping *)
    
    eapply subtype_trans.
      apply Hsub.
    Admitted.
(*
      reflexivity. inversion H5.
         
    Focus 3. auto.
  
  eapply subtype_trans. apply Hsub.



  (* typing_const *)
  exists T. split.
  exact H.
  intros.
    induction T'. 
  

apply subtype_refl.
  (* typing_sub *)
  apply IHHtyping in H0.
  destruct H0 as [T' [Htyping' Hsub]].
  exists T'. split. exact Htyping'.
  eapply subtype_trans. apply Hsub. apply H.
  (* typing_runtime *)
  assert (typing E (e_const c) T) as HtypingT. eapply typing_runtime; eauto.
  apply IHHtyping in H3.
  destruct H3 as [T' [Htyping' Hsub]].
  exists T'. split. exact Htyping'.
  apply static_coherence in H2.
  
  eapply subtype_trans. apply Hsub.
  
*)
Lemma typing_inv_abs : forall E T1 e T,
  typing E (abs T1 e) T ->
  exists T2, typing E (abs T1 e) (typ_arrow T1 T2) /\ 
             subtype (typ_arrow T1 T2) T.
Proof.
  intros E T1 e T Htyping.
  remember (abs T1 e) as exp.
  induction Htyping; intros; inversion Heqexp0. (* dismiss non-abstractions *)
  (* typing_abs *)
  subst. clear Heqexp0.
  pick fresh x.
  assert (typing ((x, T1) :: E) (open e (fvar (runtime T1) x)) T2).
    apply H. fsetdec.
  exists T2.
  split.
  apply typing_abs with (L := L).
  apply H.
  apply subtype_refl.
  (* typing_sub *)
  subst.
  apply IHHtyping in H0. 
  destruct H0 as [T2 [Htyping' Hsub']].
  exists T2.
  split.
  exact Htyping'.
  eapply subtype_trans. apply Hsub'. exact H.
  (* typing_runtime *)
  subst. 
  apply IHHtyping in H3.
  destruct H3 as [T2 [Htyping' Hsub']].
  exists T2.
  split.
  exact Htyping'.
  (* subtyping for typing_runtime *)
  inversion H0; subst.
Admitted.


Lemma runtime_static_coherence: forall E val rt T,
  value val ->
  runtime_type val rt ->
  typing E val T ->
  rts.In rt (runtime T).
Proof.
  intros E val rt T Hvalue Hrt Htyping.
  induction Htyping; subst; intros.
  (* contradiction *)
  inversion Hrt. 
  (* abstractions *)
  simpl.
  inversion Hrt.
  rewrite -> RTSFacts.singleton_iff.
  reflexivity.
  (* contradiction *)
  inversion Hvalue.
  (* constants *)
  eapply const_coherence. apply H. inversion Hrt. apply H1.
  (* contradiction *)
  inversion Hvalue.
  (* subtyping *)
  assert (rts.In rt (runtime S)) as Hsub. apply IHHtyping; auto.
  assert (rts.Subset (runtime S) (runtime T)) as Hsubset.
    apply subtype_coherence. exact H.
  eapply rts_props.in_subset. apply Hsub. exact Hsubset.
  (* runtime typing *)
  assert (typing E e T). eapply typing_runtime; eauto.
  destruct e; inversion Hvalue; subst.
    (* abstractions *)
    assert (rt = rt_function); subst. inversion Hrt. reflexivity.
    apply typing_inv_abs in H3.
    destruct H3 as [T2 [HtypingT2 Hsub]].
    apply subtype_coherence in Hsub.
    simpl in Hsub.
    assert (rts.In rt_function (rts.singleton rt_function)) as Hsingleton.
      rewrite -> RTSFacts.singleton_iff. reflexivity.
    eapply rts_props.in_subset.
      apply Hsingleton. exact Hsub.
    (* flat values *)
    inversion H3; subst.
      (* typing_e_const *)
      inversion Hrt; subst. eapply const_coherence. apply H6. exact H5.
      (* subtyping *)
      apply IHHtyping in Hvalue.
      apply static_coherence in H2.
      eapply rts_props.in_subset. apply Hvalue.
    subst.
Admitted.
  


Lemma preservation : forall E e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J.
  (* fvar *)
  inversion J.
  (* abs *)
  inversion J.
  (* app *)
  inversion J; subst.
  inversion H; subst.
  assert (exists rt, runtime_type e2 rt).
    destruct e2; inversion H5.
    exists rt_function. apply typeof_abs.
    subst. destruct c; eauto.
  destruct H1 as [rt H1].
  pick fresh x0.
  assert (subst x0 e2 (open e0 (fvar (runtime T1) x0)) (open e0 e2)) as HypIntro.
    eapply subst_intro. 
      exact H5. apply H1.
      eapply coherence. apply H5. apply H0. exact H1. 
      fsetdec.
      eapply typing_regular_lc. apply H0.
  eapply typing_subst.
    apply H5.
    apply H4. 
      assert (x0 `notin` L). fsetdec. apply H2.
    apply H0.
    exact HypIntro.
  (* application with subtyping *)
  assert (typing E (abs t e0) (typ_arrow T1 T2)) as HypTArr.
    apply typing_sub with (S := S). exact H1. exact H2.
  
    



  Focus 3.
  (* application where e1 is reduced *)
  assert (typing E e1' (typ_arrow T1 T2)) as HypPresv.
    apply IHtyping1. exact H5.
  apply typing_app with (T1 := T1). exact HypPresv. exact H0.
  (* application where e2 is reduced *)
  Focus 3.
  assert (typing E e2' T1) as HypPresv.
    apply IHtyping2. exact H5.
  apply typing_app with (T1 := T1). exact H. exact HypPresv.

  (* const *)
  Focus  3.
  inversion J.
  (* cond *)
  Focus 3.
  inversion J; subst; auto.
  (* subtyping *)
  Focus 3.
  eapply typing_sub. apply H. apply IHtyping. exact J.
  (* runtime typing *)
  Focus 3.
  inversion H; subst; inversion J.
Qed.

Lemma progress : forall e T,
  typing nil e T ->
  value e \/ exists e', eval e e'.
Proof.
  intros e T H.

  (* It will be useful to have a "non-destructed" form of the given
     typing derivation, since [induction] takes apart the derivation
     it is called on. *)
  assert (typing nil e T); auto.

  (* [remember nil as E] fails here because [nil] takes an implicit
     argument that Coq is unable to infer.  By prefixing [nil] with
     [@], we can supply the argument to nil explicitly. *)
  remember (@nil (atom * typ)) as E.

  induction H; subst.

  Case "typing_var".
    inversion H1.
  Case "typing_abs".
    left.
    apply value_abs.
    eapply typing_regular_lc; eauto.
  Case "typing_app".
    right.
    destruct IHtyping1 as [V1 | [e1' Eval1]]; auto.
    destruct IHtyping2 as [V2 | [e2' Eval2]]; auto.
    inversion V1; subst. exists (open e e2); auto.
    inversion H. inversion H4.
    exists (app e1 e2'); auto.
    exists (app e1' e2).
    apply eval_app_1. 
    eapply typing_regular_lc; eauto.
    assumption.
  (* const *)
  left.
  apply value_const.
  (* cond *)
  right.
  inversion H0. subst.
  apply IHtyping1 in H.
  apply IHtyping2 in H1.
  apply IHtyping3 in H2.
  destruct H.
  Focus 2.
  destruct H as [e1' H].
  exists (cond e1' e2 e3).
  apply cxt_cond; (auto || eapply typing_regular_lc; eauto).
  destruct e1; inversion H.
  inversion H7. (* dismiss abs *)
  subst. destruct c; inversion H7; inversion H5. (* dismiss non-bools *)
  subst. destruct b.
  exists e2. apply eval_cond_true; (auto || eapply typing_regular_lc; eauto).
  exists e3. apply eval_cond_false; (auto || eapply typing_regular_lc; eauto).
  reflexivity. reflexivity. reflexivity.
Qed.

