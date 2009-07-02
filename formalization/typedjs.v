Add LoadPath "metatheory".
Require Import Metatheory.
Require Import Dataflow.

Inductive typ : Set :=
  | typ_int  : typ
  | typ_str : typ
  | typ_bool : typ
  | typ_arrow : typ -> typ -> typ
  | typ_union : typ -> typ -> typ.

Inductive base_typ : typ -> Prop :=
  | base_typ_int : base_typ typ_int
  | base_typ_bool : base_typ typ_bool
  | base_typ_str : base_typ typ_str.

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

Fixpoint runtime (t : typ) { struct t } : RTS :=
  match t with
  | typ_int =>  rts.singleton rt_number
  | typ_str => rts.singleton rt_string
  | typ_bool => rts.singleton rt_boolean
  | typ_arrow _ _ => rts.singleton rt_function
  | typ_union t1 t2 => rts.union (runtime t1) (runtime t2)
  end.

Inductive static : rts.t -> typ -> typ -> Prop :=
  | ast_integer : static (rts.singleton rt_number) typ_int typ_int
  | ast_string : static (rts.singleton rt_string) typ_str typ_str
  | ast_boolean : static (rts.singleton rt_boolean) typ_bool typ_bool
  | ast_arrow : forall t1 t2,
      static (rts.singleton rt_function) (typ_arrow t1 t2) (typ_arrow t1 t2)
  | ast_union: forall r t1 t2 t1' t2',
      rts.Subset r (runtime t1) ->
      rts.Subset r (runtime t2) ->
      static (rts.inter (runtime t1) r) t1 t1' ->
      static (rts.inter (runtime t2) r) t2 t2' -> 
      static r (typ_union t1 t2) (typ_union t1' t2')
  | ast_unionL : forall r t1 t2 t1',
      rts.Subset r (runtime t1) ->
      static r t1 t1' ->
      static r (typ_union t1 t2) t1'
  | ast_unionR : forall r t1 t2 t2',
      rts.Subset r (runtime t2) ->
      static r t2 t2' ->
      static r (typ_union t1 t2) t2'.

Lemma static_runtime : forall R S T,
  static R S T ->
  rts.Subset R (runtime T).
Proof.
  intros R S T Hstatic.
  induction Hstatic; simpl; rtsdec.
Qed.

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
      typing E e T
  | typing_runtime : forall E e rt r S T,
      value e ->
      typing E e S ->
      runtime_type e rt ->
      rts.In rt r ->
      static r S T ->
      typing E e T.

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
  runtime_type_const.

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


Lemma runtime_sub: forall S T,
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

Lemma single_runtime_type : forall val rt1 rt2,
  value val ->
  runtime_type val rt1 ->
  runtime_type val rt2 ->
  rt1 = rt2.
Proof.
  intros val rt1 rt2 Hvalue Hrt1 Hrt2.
  destruct val; inversion Hvalue.
  inversion Hrt1. inversion Hrt2. reflexivity.
  destruct c; inversion Hrt1; inversion Hrt2;
  subst; inversion H1; inversion H4; reflexivity.
Qed.

(*****************************************************************************)
(* Weakening                                                                 *)
(*****************************************************************************)

Lemma typing_weakening_strengthened :  forall E F G e T,
  typing (G ++ E) e T ->
  ok (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G Eq Ok; subst; eauto.
  pick fresh x and apply typing_abs.
  rewrite <- cons_concat_assoc.
  apply H0.
  auto.
  rewrite cons_concat_assoc. reflexivity.
  rewrite cons_concat_assoc. apply ok_cons.
  apply Ok.
  auto.
Qed.

Lemma typing_weakening : forall E F e T,
    typing E e T ->
    ok (F ++ E) ->
    typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite <- (nil_concat _ (F ++ E)).
  apply typing_weakening_strengthened; auto.
Qed.

(*****************************************************************************)
(* Substitution                                                              *)
(*****************************************************************************)


Lemma typing_subst_strengthened : forall E F e e' u S T z,
  value u ->
  typing (F ++ (z, S) :: E) e T ->
  typing E u S ->
  subst z u e e' ->
  typing (F ++ E) e' T.
Proof.
  intros F E e e' u S T z Value.
  remember (E ++ (z, S) :: F) as G. 
  intros Hyp0 Hyp1.
  generalize dependent E.
  generalize dependent F.
  generalize dependent e'.
  induction Hyp0.
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
    eapply typing_runtime.
      exact Value.
      apply Hyp1.
      apply H4.
      apply H7.
      apply H1.
    eapply ok_remove_mid_cons. apply H.
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

(*****************************************************************************)
(* Inversion Lemmas                                                          *)
(*****************************************************************************)

Lemma subtype_inv_arrow : forall U V1 V2,
     subtype U (typ_arrow V1 V2)
  -> exists U1, exists U2, 
       (U=(typ_arrow U1 U2)) /\ (subtype V1 U1) /\ (subtype U2 V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember (typ_arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; inversion HeqV.
  exists V1. exists V2.
  split. reflexivity. split. apply subtype_refl. apply subtype_refl.
  (* transitivity *)
  apply IHHs2 in HeqV.
  destruct HeqV as [U1 [U2 HeqV]].
  destruct HeqV as [Hu [Hsub1 Hsub2]].
  apply IHHs1 in Hu.
  destruct Hu as [U3 [U4 Hu]].
  destruct Hu as [Hs [Hsub3 Hsub]].
  exists U3. exists U4.
  split. exact Hs.
  split. eapply subtype_trans. apply Hsub1. exact Hsub3.
         eapply subtype_trans. apply Hsub. exact Hsub2.
  (* arrow subtyping *)  
  exists s1. exists s2.
  subst...
Qed.

Lemma subtype_inv_int : forall T,
  subtype T typ_int ->
  T = typ_int.
Proof.
  intros T Hsub.
  remember typ_int as U.
  rewrite -> HeqU.
  assert (subtype T typ_int) as HsubOrig. subst. exact Hsub.
  generalize dependent HsubOrig.
  generalize dependent HeqU.
  induction Hsub; intros; try (inversion HeqU).
  subst. reflexivity.
  (* subtyping *)
  apply IHHsub1. apply IHHsub2. exact HeqU.
  subst. exact Hsub2. exact HsubOrig.
Qed.

Lemma subtype_inv_bool : forall T,
  subtype T typ_bool ->
  T = typ_bool.
Proof.
  intros T Hsub.
  remember typ_bool as U.
  rewrite -> HeqU.
  assert (subtype T typ_bool) as HsubOrig. subst. exact Hsub.
  generalize dependent HsubOrig.
  generalize dependent HeqU.
  induction Hsub; intros; try (inversion HeqU).
  subst. reflexivity.
  (* subtyping *)
  apply IHHsub1. apply IHHsub2. exact HeqU.
  subst. exact Hsub2. exact HsubOrig.
Qed.

Lemma typing_inv_cond : forall E e1 e2 e3 T,
  typing E (cond e1 e2 e3) T ->
  typing E e1 typ_bool /\
  typing E e2 T /\
  typing E e3 T.
Proof.
  intros.
  remember (cond e1 e2 e3) as Hexpr.
  induction H; inversion HeqHexpr.
  subst. auto.
  subst. apply IHtyping in H1.
  destruct H1 as [He1 [He2 He3]].
  split. exact He1.
  split. eapply typing_sub. apply H. exact He2.
         eapply typing_sub. apply H. exact He3.
  subst. inversion H.
Qed.

Lemma typing_inv_abs : forall E e S1 T1' T2',
  typing E (abs S1 e) (typ_arrow T1' T2') ->
  exists T1, exists T2, (exists L, forall x, x `notin` L -> 
            (typing ((x, S1) :: E) (open e (fvar (runtime S1) x)) T2)) /\
             subtype (typ_arrow T1 T2) (typ_arrow T1' T2') /\
             subtype T1 S1.
Proof with eauto.
  intros E e S1 T1' T2' Htyping.
  remember (abs S1 e) as expr.
  induction Htyping; inversion Heqexpr.
  (* typing_abs *)
  subst.
  exists S1.
  exists T2.
  split.
  pick fresh x'.
  remember (L `union` dom E `union` fv e) as L0.
  exists L0.
  intros x Hfree.
  apply H.
  fsetdec.
  split. apply subtype_refl. apply subtype_refl.
  (* typing_sub *)
  subst.
  apply IHHtyping in H0.
  destruct H0 as [T1 [T2 [[L Htyping0] H0]]].
  exists T1. exists T2.
  split. exists L. intros.
  apply Htyping0. fsetdec.
  destruct H0.
  split. eapply subtype_trans... exact H1.
  (* typing_runtime *)
  subst.
  inversion H0; subst.
  apply IHHtyping in H3. clear IHHtyping.
  destruct H3 as [T1 [T2 [[L Htyping0] [Hsub0 Hsub1]]]].
  exists T1. exists T2.
  split...
  split.
Focus 2. exact Hsub1.
  (* Here, we have to prove that T1 -> T2 <: T.
   * We know T1 -> T2 <: S and that T = static(R, S).
   * Since T1 -> T2 <: S, S "contains" the arrow type T1 -> T2.
   * By the static_sub lemma, T <: S.  Intituively, we know that T is
   * an arrow type and that it is the most general arrow type contained
   * in S--runtime type tests are first-order.  Therefore, T1 -> T2 <: T.
   *)
Admitted.

(*****************************************************************************)
(* Preservation                                                              *)
(*****************************************************************************)

Hint Constructors runtime_type.

Lemma const_coherence : forall c rt T,
  typing_const c T ->
  runtime_type_const c rt ->
  rts.In rt (runtime T).
Proof.
  intros c rt T HypT HypRT.
  inversion HypT; subst; inversion HypRT; subst; simpl; fsetdec.
Qed.


Lemma coherence : forall E val rt T,
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
  rewrite -> rts_facts.singleton_iff.
  reflexivity.
  (* flat values *)
  subst.
  inversion Hrt.
  eapply const_coherence. apply H. apply H1.
  (* subtypes of functions *)
  inversion Hrt; subst.  
    inversion H3. (* contradiction *)
  assert (rts.In rt_function (runtime S)).
    apply IHHtyping. exact Hvalue. trivial.
  assert (rts.Subset (runtime S) (runtime T)).
    apply runtime_sub. exact H.
  eapply rts_props.in_subset.
    apply H1. exact H3.
  (* subtypes of flat values *) 
  subst.
  assert (rts.Subset (runtime S) (runtime T)).
    apply runtime_sub. exact H.
  assert (rts.In rt (runtime S)).
    apply IHHtyping. exact Hvalue. exact Hrt.
  eapply rts_props.in_subset.
    apply H1. exact H0.
  (* runtime typing for functions *)
  assert (rt0 = rt); subst. eapply single_runtime_type; eauto.
  clear H0 H.
  apply static_runtime in H2.
  rtsdec.
  (* runtime typing for constants *)
  assert (rt0 = rt); subst. eapply single_runtime_type; eauto.
  apply static_runtime in H2.
  rtsdec.
Qed.

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
  inversion J; subst. (* consider applicable evaluation rules *)
  (* beta reduction *)
  apply typing_inv_abs in H. clear IHtyping1 IHtyping2.
  destruct H as [T3 [T4 [[L Htyping] [Hsub HsubArg]]]].
  apply subtype_inv_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub0 Hsub1]]]].
  inversion Heq; subst; clear Heq.
  assert (exists rt, runtime_type e2 rt) as H1.
    destruct e2; inversion H5.
    exists rt_function. apply typeof_abs.
    subst. destruct c; eauto.
  destruct H1 as [rt H1].
  pick fresh x0.
  assert (typing E e2 t) as H0'.
    eapply typing_sub.
    assert (subtype T1 t).
      eapply subtype_trans. apply Hsub0. exact HsubArg.
    apply H.
    exact H0.
  assert (subst x0 e2 (open e0 (fvar (runtime t) x0)) (open e0 e2)) as HypIntro.
    eapply subst_intro. 
     exact H5. 
     apply H1.
     eapply coherence.
     apply H5.
     apply H0'.
     exact H1.
     fsetdec.
     eapply typing_regular_lc. apply H0'.
  assert (typing ((x0, t) :: E) (open e0 (fvar (runtime t) x0)) U2) as H.
    apply Htyping. fsetdec.
  eapply typing_subst.
    apply H5.
    eapply typing_sub.
    apply Hsub1.
    apply H.
    exact H0'.
    exact HypIntro.
  (* application where e1 is reduced *)
  assert (typing E e1' (typ_arrow T1 T2)) as HypPresv.
    apply IHtyping1. exact H5.
  apply typing_app with (T1 := T1). exact HypPresv. exact H0.
  (* application where e2 is reduced *)
  assert (typing E e2' T1) as HypPresv.
    apply IHtyping2. exact H5.
  apply typing_app with (T1 := T1). exact H. exact HypPresv.
  (* const *)
  inversion J.
  (* cond *)
  inversion J; subst; auto.
  (* subtyping *)
  eapply typing_sub. apply H. apply IHtyping. exact J.
  (* runtime typing *)
  inversion H; subst; inversion J.
Qed.

Lemma canonical_abs : forall e T1 T2,
  value e ->
  typing nil e (typ_arrow T1 T2) ->
  exists S1, exists e', e = abs S1 e'.
Proof.
  intros e T1 T2 Hvalue Htyping.
  remember (@nil (atom * typ)) as E.
  remember (typ_arrow T1 T2) as T.
  generalize dependent T1.
  generalize dependent T2.
  induction Htyping; inversion Hvalue.
  (* arrows *)
  intros. exists T1. exists e. reflexivity.
  (* const *)
  intros. subst. inversion H.
  (* subtyping *)
  intros. exists t. exists e0. reflexivity.
  (* const-subtyping *)
  intros. subst.
  apply subtype_inv_arrow in H.
  destruct H as [U1 [U2 [Hsub0 [Hsub1 Hsub2]]]].
  apply IHHtyping with (T1 := U1) (T2 := U2) in Hvalue.
  destruct Hvalue as [S1 [e' Hvalue]].
  inversion Hvalue.
  reflexivity.
  exact Hsub0.
  (* runtime-typing of abstractions *)
  intros. subst. exists t. exists e0. reflexivity.
  (* runtime-typing of constants *)
  intros. subst.
  assert (rts.Subset r (rts.singleton rt_function)) as Hrt0.
    apply static_runtime in H2. exact H2.
  assert (rts.In rt (rts.singleton rt_function)) as Hrt1. 
    eapply rts_props.in_subset. apply H1. exact Hrt0.
  inversion H0; subst.
  inversion H4; subst; rewrite rts_facts.singleton_iff in Hrt1; 
    inversion Hrt1.
Qed.

Lemma canonical_bool : forall val,
  value val ->
  typing nil val typ_bool ->
  val = e_const (const_bool true) \/ val = e_const (const_bool false).
Proof with subst.
  intros val Hvalue Htyping.
  remember typ_bool as T.
  induction Htyping; inversion Hvalue.
  inversion HeqT.
  inversion H; subst; inversion H2.
  destruct b. left. reflexivity. right. reflexivity.
  subst.
  apply subtype_inv_bool in H...
  apply IHHtyping in Hvalue.
  destruct Hvalue; inversion H.
  reflexivity.
  subst.
  apply subtype_inv_bool in H...
  apply IHHtyping in Hvalue.
  destruct Hvalue. left. exact H. right. exact H.
  reflexivity.
  (* runtime-typing of functions *)
  subst.
  assert (rts.Subset r (rts.singleton rt_boolean)) as Hrt0.
    apply static_runtime in H2. exact H2.
  assert (rts.In rt (rts.singleton rt_boolean)) as Hrt1. 
    eapply rts_props.in_subset. apply H1. exact Hrt0.
  inversion H0; subst.
  rewrite rts_facts.singleton_iff in Hrt1.
  inversion Hrt1.
  (* runtime-typing of constants *)
  subst.
  assert (rts.Subset r (rts.singleton rt_boolean)) as Hrt0.
    apply static_runtime in H2. exact H2.
  assert (rts.In rt (rts.singleton rt_boolean)) as Hrt1. 
    eapply rts_props.in_subset. apply H1. exact Hrt0.
  inversion H0; subst.
  inversion H4; subst.
  rewrite rts_facts.singleton_iff in Hrt1; inversion Hrt1.
  destruct b. left. reflexivity. right. reflexivity.
  rewrite rts_facts.singleton_iff in Hrt1; inversion Hrt1.
Qed.

Lemma progress : forall e T,
  typing nil e T ->
  value e \/ exists e', eval e e'.
Proof with eauto.
  intros e T H.
  assert (typing nil e T); auto.
  remember (@nil (atom * typ)) as E.
  induction H; subst.
  (* typing_var *)
  inversion H1.
  (* typing_abs *)
  left.
  apply value_abs.
  eapply typing_regular_lc...
  (* typing_app *)
  right.
  destruct IHtyping1 as [V1 | [e1' Eval1]]; auto.
  destruct IHtyping2 as [V2 | [e2' Eval2]]; auto.
  assert (exists S1, exists e', e1 = abs S1 e').
    eapply canonical_abs...
  destruct H2 as [S1 [e' Heq]].
  subst.
  exists (open e' e2).
    apply eval_beta.
    eapply typing_regular_lc...
    exact V2.
  exists (app e1 e2')...
  exists (app e1' e2).
    apply eval_app_1. 
    eapply typing_regular_lc; eauto.
    assumption.
  (* const *)
  left.
  apply value_const.
  (* cond *)
  right.
  apply typing_inv_cond in H0.
  destruct H0 as [Hcond [Htrue Hfalse]].
  apply IHtyping1 in H.
  destruct H.
  (* e1 is a value *)
  apply canonical_bool in Hcond.
  destruct Hcond; subst.
  exists e2. apply eval_cond_true; eapply typing_regular_lc...
  exists e3. apply eval_cond_false; eapply typing_regular_lc...
  exact H.
  destruct H as [e' H].
  exists (cond e' e2 e3).
  apply cxt_cond. exact H. 
  eapply typing_regular_lc...
  eapply typing_regular_lc...
  reflexivity.
  (* subtyping *)
  apply IHtyping in H1. exact H1. reflexivity.
  (* runtime typing *)
  apply IHtyping in H1. exact H1. reflexivity.
Qed.
