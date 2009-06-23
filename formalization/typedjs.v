Add LoadPath "metatheory".
Require Import Metatheory.
Require Import Dataflow.

Inductive typ : Set :=
  | typ_base  : typ
  | typ_arrow : typ -> typ -> typ.

Inductive exp : Set :=
  | bvar : nat  -> exp    (* bound variables *)
  | fvar : atom -> exp   (* free  variables *)
  | abs  : typ -> exp  -> exp (* type of the binding instance *)
  | app  : exp  -> exp -> exp.

Inductive subst : atom -> exp -> exp -> exp -> Prop :=
  | subst_bvar : forall z u (i : nat), subst z u (bvar i) (bvar i)
  | subst_fvar_noop : forall z u (x : atom),
      x <> z -> subst z u (fvar x) (fvar x)
  | subst_fvar : forall (z : atom) (u : exp), subst z u (fvar z) u
  | subst_abs : forall z u t e1 e1',
      subst z u e1 e1' ->
      subst z u (abs t e1) (abs t e1')
  | subst_app : forall z u e1 e2 e1' e2',
      subst z u e1 e1' ->
      subst z u e2 e2' ->
      subst z u (app e1 e2) (app e1' e2').

Hint Constructors subst.

Fixpoint open_rec (k : nat) (u : exp) (e : exp) {struct e} : exp :=
  match e with
    | bvar i => if k === i then u else (bvar i)
    | fvar x => fvar x
    | abs t e1 => abs t (open_rec (S k) u e1)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
  end.

Definition open e u := open_rec 0 u e.

Notation env := (list (atom * typ)).

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E (x : atom) T,
      ok E ->
      binds x T E ->
      typing E (fvar x) T
  | typing_abs : forall L E e T1 T2,
      (forall x : atom, x `notin` L ->
        typing ((x, T1) :: E) (open e (fvar x)) T2) ->
      typing E (abs T1 e) (typ_arrow T1 T2)
  | typing_app : forall E e1 e2 T1 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (app e1 e2) T2.

Hint Constructors typing.

Inductive lc : exp -> Prop :=
  | lc_var : forall x,
      lc (fvar x)
  | lc_abs : forall L e t,
      (forall x:atom, x `notin` L -> lc (open e (fvar x))) ->
      lc (abs t e)
  | lc_app : forall e1 e2,
      lc e1 ->
      lc e2 ->
      lc (app e1 e2).

Hint Constructors lc.

Inductive value : exp -> Prop :=
  | value_abs : forall t e,
      lc (abs t e) ->
      value (abs t e).

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
      eval (app e1 e2) (app e1 e2').

Hint Constructors value eval.

Fixpoint fv (e : exp) {struct e} : atoms :=
  match e with
    | bvar i => {}
    | fvar x => singleton x
    | abs t e1 => fv e1
    | app e1 e2 => (fv e1) `union` (fv e2)
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
    apply open_rec_lc_core with (i := S k) (j := 0) (u := u) (v := fvar x). auto. auto.
  Case "lc_app".
    intro k. simpl. f_equal. auto. auto.
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
Qed.

Lemma subst_open_var : forall (x y : atom) u e e1,
  y <> x ->
  lc u ->
  subst x u e e1 ->
  subst x u (open e (fvar y)) (open e1 (fvar y)).
Proof.
  intros x y u e e1 e2 Neq H.
  unfold open in *.
  apply subst_open_rec.
    exact Neq.
    exact H.
    auto.
Qed.

Lemma typing_weakening_strengthened :  forall E F G e T,
  typing (G ++ E) e T ->
  ok (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G Eq Ok; subst.
  Case "typing_var".
    apply typing_var.
      apply Ok.
      apply binds_weaken. apply H0. apply Ok.
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    rewrite <- cons_concat_assoc.
    apply H0.
      auto.
      rewrite cons_concat_assoc. reflexivity.
      rewrite cons_concat_assoc. apply ok_cons.
        apply Ok.
        auto.
  Case "typing_app".
    eapply typing_app.
      eapply IHtyping1. reflexivity. apply Ok.
      eapply IHtyping2. reflexivity. apply Ok.
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

Lemma typing_regular_lc : forall E e T,
  typing E e T -> lc e.
Proof.
  intros E e T H. induction H; eauto.
Qed.

Lemma typing_subst_strengthened : forall E F e e' u S T z,
  typing (F ++ (z, S) :: E) e T ->
  typing E u S ->
  subst z u e e' ->
  typing (F ++ E) e' T.
Proof.
  intros F E e e' u S T z.
  remember (E ++ (z, S) :: F) as G. 
  intros Hyp0 Hyp1.
  Check subst_ind.
  generalize dependent E.
  generalize dependent F.
  generalize dependent e'.
  induction Hyp0.
  (* var *)
  intros.
  subst.
  destruct (x == z).
    assert (T = S). subst. eapply binds_mid_eq_cons. apply H0. apply H.
    subst.
    inversion H1. 
      unfold not in H5. contradiction H5. reflexivity.
      subst. apply typing_weakening. exact Hyp1.
      eapply ok_remove_mid_cons. apply H.
    (* x <> z *)
    inversion H1; subst.
    apply typing_var.
    eapply ok_remove_mid_cons. apply H.
    eapply binds_remove_mid_cons. apply H0.
    exact H5.
    contradiction n. reflexivity.
  (* abs *)
  intros.
  inversion H1. subst.
  pick fresh x0 and apply typing_abs.
  assert (lc u) as Hlc. eapply typing_regular_lc. apply Hyp1.
  assert (subst z u (open e (fvar x0)) (open e1' (fvar x0))).
    apply subst_open_var. fsetdec. exact Hlc. exact H7.
  assert (x0 `notin` L). fsetdec.
  apply H0 with (x := x0) (e' := open e1' (fvar x0)) (F0 := F) (E := (x0, T1) :: E0).
    exact H3.
    exact Hyp1.
    simpl. reflexivity.
    exact H2.
  (* app *)
  intros.
  inversion H. subst.
  eapply typing_app; auto.
Qed.

(** *** Exercise

    Complete the proof of the substitution lemma stated in the form we
    need it.  The proof is similar to that of [typing_weakening].  In
    particular, recall the lemma [nil_concat]. *)

Lemma typing_subst : forall E e e' u S T z,
  typing ((z, S) :: E) e T ->
  typing E u S ->
  subst z u e e' ->
  typing E e' T.
Proof.
  intros E e e' u S T z HypInd HypS HypSubst.
  assert (nil ++ E = E) as HypNilConcat. apply nil_concat.
  rewrite <- HypNilConcat.
  apply typing_subst_strengthened with (S := S) (u := u) (z := z) (e := e). 
    simpl. exact HypInd. exact HypS. exact HypSubst.
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
Qed. 


(*************************************************************************)
(** * Preservation *)
(*************************************************************************)

(** *** Note

    In order to prove preservation, we need one more lemma, which
    states that when we open a term, we can instead open the term with
    a fresh variable and then substitute for that variable.

    Technically, the [(lc u)] hypothesis is not needed to prove the
    conclusion.  However, it makes the proof simpler. *)

Lemma subst_intro : forall (x : atom) u e,
  x `notin` (fv e) ->
  lc u ->
  subst x u (open e (fvar x)) (open e u).
Proof.
  intros x u e H J.
  unfold open.
  apply subst_open_rec.
    exact J. apply subst_fresh. exact H. auto.
Qed.

Lemma preservation : forall E e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J.
  inversion J.
  inversion J.
  inversion J; subst.
  inversion H. subst.
  pick fresh x.
  assert (subst x e2 (open e0 (fvar x)) (open e0 e2)) as HypIntro.
    apply subst_intro. fsetdec. inversion H5. exact H1.
  eapply typing_subst with (S := T1) (z := x) 
                          (e := (open e0 (fvar x))) (e' := (open e0 e2)).
    apply H4. fsetdec.
    apply H0.
    apply HypIntro.
  (* application where e1 is reduced *)
  assert (typing E e1' (typ_arrow T1 T2)) as HypPresv.
    apply IHtyping1. exact H5.
  apply typing_app with (T1 := T1). exact HypPresv. exact H0.
  (* application where e2 is reduced *)
  assert (typing E e2' T1) as HypPresv.
    apply IHtyping2. exact H5.
  apply typing_app with (T1 := T1). exact H. exact HypPresv.
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
        exists (app e1 e2'); auto.
      exists (app e1' e2).
        apply eval_app_1. Focus 2. assumption. Check typing_regular_lc.
          eapply typing_regular_lc; eauto.
Qed.

