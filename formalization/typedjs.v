Add LoadPath "metatheory".
Require Import Metatheory.
Require Import Dataflow.

Inductive typ : Set :=
  | typ_string : typ
  | typ_boolean : typ
  | typ_integer : typ
  | typ_arrow : typ -> typ -> typ
  | typ_union : typ -> typ -> typ.

Axiom typ_union_symm : forall t1 t2, typ_union t1 t2 = typ_union t2 t1.

Inductive subtype : typ -> typ -> Prop :=
  | subtype_invariant : forall (t : typ), subtype t t
  | subtype_trans : forall (s t u : typ), 
      subtype s u -> subtype u t -> subtype s t
  | subtype_arrow : forall (s1 s2 t1 t2 : typ),
      subtype t1 s1 /\ subtype s2 t2 -> 
      subtype (typ_arrow s1 s2) (typ_arrow t1 t2)
  | subtype_unionL : forall (s1 s2 t : typ),
      subtype s1 t /\ subtype s2 t -> subtype (typ_union s1 s2) t
  | subtype_unionR : forall (s t1 t2 : typ),
      subtype s t1 \/ subtype s t2 -> subtype s (typ_union t1 t2).

Example subtype_eg0 : subtype typ_string (typ_union typ_string typ_boolean).
Proof.
  apply subtype_unionR.
  left. apply subtype_invariant.
Qed.

Example subtype_eg1 : 
  subtype (typ_union typ_string typ_boolean)
          (typ_union typ_string 
                     (typ_union typ_boolean
                                (typ_arrow typ_string typ_boolean))).
Proof.
  apply subtype_unionL.
  split.
    apply subtype_unionR. left. apply subtype_invariant.
    apply subtype_unionR. right. apply subtype_unionR. left. 
      apply subtype_invariant.
Qed.

(*
Inductive static : rts.t -> typ -> typ -> Prop :=
  | ast_integer : forall r, rts.In rt_number r -> 
      static r typ_integer typ_integer
  | ast_string : forall r, rts.In rt_string r ->
      static r typ_string typ_string
  | ast_boolean : forall r, rts.In rt_boolean r ->
      static r typ_boolean typ_boolean
  | ast_arrow : forall r t1 t2, rts.In rt_function r ->
      static r (typ_arrow t1 t2) (typ_arrow t1 t2)
  | ast_union: forall r t1 t2 t1' t2',
      static r t1 t1' /\ static r t2 t2' -> 
      static r (typ_union t1 t2) (typ_union t1' t2')
  | ast_unionL : forall r t1 t2 t1',
      static r t1 t1' ->
      static r (typ_union t1 t2) t1'
  | ast_unionR : forall r t1 t2 t2',
      static r t2 t2' ->
      static r (typ_union t1 t2) t2'.

Inductive runtime : typ -> rts.t -> Prop :=
  | asrt_integer : runtime typ_integer (rts.singleton rt_number)
  | asrt_string : runtime typ_string (rts.singleton rt_string)
  | asrt_boolean : runtime typ_boolean (rts.singleton rt_boolean)
  | asrt_arrow : forall t1 t2, 
      runtime (typ_arrow t1 t2) (rts.singleton rt_function)
  | asrt_union: forall t1 t2 r1 r2,
      runtime t1 r1 -> runtime t2 r2 -> 
      runtime (typ_union t1 t2) (rts.union r1 r2).

Theorem type_ordering : forall t r1 r2 t1 t2,
  rts.Subset r1 r2 ->
  static r1 t t1 ->
  static r2 t t2.
Proof with subst.
  intros t. induction t.
  intros.
  inversion H0.
  generalize dependent t2.
  apply ast_string with (r := r2).

*)

Fixpoint static (rt : rts.t) (t : typ) { struct t } : option typ := 
  match t with
  | typ_integer => if rts.mem rt_number rt then (Some typ_integer) else None
  | typ_string => if rts.mem rt_string rt then (Some typ_string) else None
  | typ_boolean => if rts.mem rt_boolean rt then (Some typ_boolean) else None
  | typ_arrow _ _ => if rts.mem rt_function rt then (Some t) else None
  | typ_union t1 t2 => 
      match static rt t1, static rt t2 with
      | None, None => None
      | Some t1', Some t2' => Some (typ_union t1' t2')
      | Some t1', None => Some t1'
      | None, Some t2' => Some t2'
      end
  end.

Theorem type_ordering : forall t r1 r2 t1' t2',
  rts.Subset r1 r2 -> 
  Some t1' = static r1 t ->
  Some t2' = static r2 t ->
  subtype t1' t2'.
Proof.
  intros t. induction  t.
  intros. 
  inversion H0.
  remember (rts.mem rt_string r1) as HypIn.
  destruct HypIn.
  assert (rts.mem rt_string r1 = true). auto.
  rewrite <- RTSFacts.mem_iff in H2.
  assert (


Fixpoint runtime (t : typ) { struct t } : rts.t:=
  match t with
  | typ_integer =>  rts.singleton rt_number
  | typ_string => rts.singleton rt_string
  | typ_boolean => rts.singleton rt_boolean
  | typ_arrow _ _ => rts.singleton rt_function
  | typ_union t1 t2 => rts.union (runtime t1) (runtime t2)
  end.


  

Lemma static_runtime_subtyping1 : forall (t2 t1 t3 : typ),
  Some t3 = static (runtime t1) t2 -> (subtype t3 t2).
Proof.
  induction t2.
  intros. destruct t1; (simpl in H; inversion H).
    apply subtype_invariant.
    destruct (rts.mem rt_string (rts.union (runtime t1_1) (runtime t1_2))).
      inversion H. apply subtype_invariant. inversion H.
  (* Same as above, but with typ_boolean *)
  intros. destruct t1; (simpl in H; inversion H).
    apply subtype_invariant.
    destruct (rts.mem rt_boolean (rts.union (runtime t1_1) (runtime t1_2))).
      inversion H. apply subtype_invariant. inversion H.
  (* Same as above, but with typ_number *)
  intros. destruct t1; (simpl in H; inversion H).
    apply subtype_invariant.
    destruct (rts.mem rt_number (rts.union (runtime t1_1) (runtime t1_2))).
      inversion H. apply subtype_invariant. inversion H.
  (* Case for typ_arrow _ _ *)
  intros.
  unfold static in H. 
  destruct (rts.mem rt_function (runtime t1)). 
    inversion H. apply subtype_invariant. inversion H.
  (* Case for typ_union _ _ *)
  intros.
  simpl in H.
  remember (static (runtime t1) t2_1) as T1.
  remember (static (runtime t1) t2_2) as T2.
  destruct T1. destruct T2.
    inversion H.
    apply IHt2_1 in HeqT1.
    apply IHt2_2 in HeqT2.
    apply subtype_unionL. split. 
      apply subtype_unionR. left. exact HeqT1.
      apply subtype_unionR. right. exact HeqT2.
    apply IHt2_1 in HeqT1. 
    inversion H. apply subtype_unionR. left. exact HeqT1.
    destruct T2. apply IHt2_2 in HeqT2.
    inversion H. apply subtype_unionR. right. exact HeqT2.
    inversion H.
Qed.

Lemma static_runtime_subtype1_contra : forall t2 t1 t3,
  not (subtype t3 t2) -> not (Some t3 = static (runtime t1) t2).
Proof.
  intros.
  unfold not in H.
  unfold not.
  intros.
  destruct t2; (apply static_runtime_subtyping1 in H0; apply H in H0; exact H0).
Qed.

Lemma static_runtime_subset : forall t r r',
  rts.Subset r r' -> static r t = Some t -> static r' t = Some t.
Proof.
  intros t.
  induction t; (intros; simpl).
  Focus 5.
  remember (static r' t1) as T1.
  destruct T1.
  Admitted.

Lemma runtime_monotone : forall t t',
  subtype t t' -> rts.Subset (runtime t) (runtime t').
Proof.
  Admitted.

Lemma static_runtime_subtyping2 : forall (t t' : typ),
  static (runtime t) t = Some t -> 
  static (runtime (typ_union t t')) t = Some t.
Proof.
  induction t. 
  intros. simpl.
  assert (rts.mem rt_string (rts.union (rts.singleton rt_string) (runtime t')) = true).
    rewrite <- RTSFacts.mem_iff.
    rewrite -> RTSFacts.union_iff.
    left. rewrite -> RTSFacts.singleton_iff. reflexivity.
    destruct (rts.mem rt_string (rts.union (rts.singleton rt_string) (runtime t'))).
    reflexivity. inversion H0.
  intros. simpl.
  assert (rts.mem rt_boolean (rts.union (rts.singleton rt_boolean) (runtime t')) = true).
    rewrite <- RTSFacts.mem_iff.
    rewrite -> RTSFacts.union_iff.
    left. rewrite -> RTSFacts.singleton_iff. reflexivity.
    destruct (rts.mem rt_boolean (rts.union (rts.singleton rt_boolean) (runtime t'))).
    reflexivity. inversion H0.
  intros. simpl.
  assert (rts.mem rt_number (rts.union (rts.singleton rt_number) (runtime t')) = true).
    rewrite <- RTSFacts.mem_iff.
    rewrite -> RTSFacts.union_iff.
    left. rewrite -> RTSFacts.singleton_iff. reflexivity.
    destruct (rts.mem rt_number (rts.union (rts.singleton rt_number) (runtime t'))).
    reflexivity. inversion H0.
  intros. simpl.
  assert (rts.mem rt_function (rts.union (rts.singleton rt_function) (runtime t')) = true).
    rewrite <- RTSFacts.mem_iff.
    rewrite -> RTSFacts.union_iff.
    left. rewrite -> RTSFacts.singleton_iff. reflexivity.
    destruct (rts.mem rt_function (rts.union (rts.singleton rt_function) (runtime t'))).
    reflexivity. inversion H0.
  (* inductive case for unions *)
  intros.
  unfold runtime.
  
  Admitted.



Theorem static_runtime_lens : forall (t : typ),
  static (runtime t) t = Some t.
Proof.
  induction t.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl.
  remember (static (rts.union (runtime t1) (runtime t2)) t1) as T1.
  remember (static (rts.union (runtime t1) (runtime t2)) t2) as T2.
  assert (rts.union (runtime t1) (runtime t2) = runtime (typ_union t1 t2)).
    simpl. reflexivity.
  rewrite -> H in *.
  destruct T1. destruct T2.
  f_equal.
  apply static_runtime_subtyping2 with (t' := t2) in IHt1.
  apply static_runtime_subtyping2 with (t' := t1) in IHt2.
  rewrite -> IHt1 in HeqT1.
  assert (typ_union t1 t2 = typ_union t2 t1). apply typ_union_symm.
  rewrite <- H0 in IHt2.
  rewrite -> IHt2 in HeqT2.
  inversion HeqT1.
  inversion HeqT2.
  reflexivity.
  (* Remaining are contradictions *)
  apply static_runtime_subtyping2 with (t' := t1) in IHt2.
  assert (typ_union t2 t1 = typ_union t1 t2). apply typ_union_symm.
  rewrite -> H0 in IHt2.
  rewrite -> IHt2 in HeqT2.
  inversion HeqT2.
  destruct T2.
  apply static_runtime_subtyping2 with (t' := t2) in IHt1.
  rewrite -> IHt1 in HeqT1.
  inversion HeqT1.
  apply static_runtime_subtyping2 with (t' := t2) in IHt1.
  rewrite -> IHt1 in  HeqT1.
  inversion HeqT1.
Qed.

