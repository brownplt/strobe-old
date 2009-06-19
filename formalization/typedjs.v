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

Inductive string : Set :=
  | str_number : string
  | str_boolean : string
  | str_function : string
  | str_string : string
  | str_other_string : string.

Inductive split : Set :=
  | split_bvar : nat -> RTS -> RTS -> split
  | no_split : split.

Inductive exp : Set :=
  | e_bvar : RTS -> nat -> exp
  | e_fvar : RTS -> atom -> exp
  | e_equal : exp -> exp -> exp
  | e_typeof : exp -> exp
  | e_if : split -> exp -> exp -> exp -> exp
  | e_app : exp -> exp -> exp
  (* Unlike the POPL tutorial, we need typ on e_abs for lc *)
  | e_abs : typ -> exp -> exp
  | e_num : nat -> exp
  | e_str : string -> exp
  | e_bool : bool -> exp.


(** Substitute z for u in e.  Assume that u is locally closed. *)
Fixpoint subst (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar r n => e_bvar r n
  | e_fvar r x => if x == z then u else e_fvar r x
  | e_equal e1 e2 => e_equal (subst z u e1) (subst z u e2)
  | e_typeof e1 => e_typeof (subst z u e1)
  | e_if s e1 e2 e3 => e_if s (subst z u e1) (subst z u e2) (subst z u e3)
  | e_app e1 e2 => e_app (subst z u e1) (subst z u e2)
  | e_abs t e1 => e_abs t (subst z u e1)
  | e_num n => e_num n
  | e_str s => e_str s
  | e_bool b => e_bool b
  end.

Fixpoint fv (e : exp) {struct e} : atoms :=
  match e with
  | e_bvar r i => {}
  | e_fvar r x => singleton x
  | e_equal e1 e2 => (fv e1) `union` (fv e2)
  | e_typeof e1 => fv e1
  | e_if s e1 e2 e3 => (fv e1) `union` (fv e2) `union` (fv e3)
  | e_app e1 e2 => (fv e1) `union` (fv e2)
  | e_abs t e1 => fv e1
  | e_num _ => {}
  | e_str _ => {}
  | e_bool _ => {}
  end.

Lemma subst_fresh : forall (x : atom) e u,
  x `notin` fv e -> subst x u e = e.
Proof.
  intros x e u.
  intros H.
  induction e; try (simpl; reflexivity).
  (* e_fvar *)
  simpl. destruct (a == x). subst a. simpl in H. destruct H. fsetdec. 
                            reflexivity.
  (* e_equal *)
  simpl. simpl in H.
  assert (x `notin` fv e1). fsetdec. apply IHe1 in H0.
  assert (x `notin` fv e2). fsetdec. apply IHe2 in H1.
  rewrite -> H0. rewrite -> H1. reflexivity.
  (* e_typeof *)
  simpl. simpl in H. apply IHe in H. rewrite -> H. reflexivity.
  (* e_if *)
  simpl. simpl in H.
  assert (x `notin` fv e1). fsetdec. apply IHe1 in H0.
  assert (x `notin` fv e2). fsetdec. apply IHe2 in H1.
  assert (x `notin` fv e3). fsetdec. apply IHe3 in H2.
  rewrite -> H0. rewrite -> H1. rewrite -> H2. reflexivity.
  (* e_app *)
  simpl. simpl in H.
  assert (x `notin` fv e1). fsetdec. apply IHe1 in H0.
  assert (x `notin` fv e2). fsetdec. apply IHe2 in H1.
  rewrite -> H0. rewrite -> H1. reflexivity.
  (* e_abs *)
  simpl. simpl in H. apply IHe in H. rewrite -> H. reflexivity.
Qed.


(** Opening *)

Definition typeof (e : exp) : option RT:=
  match e with
  | e_bool _ => Some rt_boolean
  | e_num _ => Some rt_number
  | _ => None
  end.


Fixpoint open_rec (k : nat) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar r i => 
      if k === i 
        then match u with
             | e_fvar _ x => e_fvar r x
             | _ => u
             end
        else e_bvar r i
  | e_fvar r x => e_fvar r x
  | e_equal e1 e2 => e_equal (open_rec k u e1) (open_rec k u e2)
  | e_typeof e1 => e_typeof (open_rec k u e1)
  | e_if s e1 e2 e3 => 
      match s with
      | no_split => e_if no_split (open_rec k u e1) (open_rec k u e2) (open_rec k u e3)
      | split_bvar k' r1 r2 => if k' === k then
          match typeof u with
          | Some r => match rts.mem r r1, rts.mem r r2 with
                      | true, false => open_rec k u e2
                      | false, true => open_rec k u e3
                      | _, _ => e_if no_split (open_rec k u e1) (open_rec k u e2) (open_rec k u e3)
                      end
          | None => e_if no_split (open_rec k u e1) (open_rec k u e2) (open_rec k u e3) 
          end else
          e_if s (open_rec k u e1) (open_rec k u e2) (open_rec k u e3)
      end
  | e_app e1 e2 => e_app (open_rec k u e1) (open_rec k u e2)
  | e_abs t e1 => e_abs t (open_rec (S k) u e1)
  | e_num n => e_num n
  | e_str s => e_str s
  | e_bool b => e_bool b
  end.

Definition open e u := open_rec 0 u e.

Hint Unfold open.

Fixpoint runtime (t : typ) { struct t } : rts.t:=
  match t with
  | typ_integer =>  rts.singleton rt_number
  | typ_string => rts.singleton rt_string
  | typ_boolean => rts.singleton rt_boolean
  | typ_arrow _ _ => rts.singleton rt_function
  | typ_union t1 t2 => rts.union (runtime t1) (runtime t2)
  end.


Inductive lc : exp -> Prop :=
  (* e_bvar is not locally closed.  They get substituted out when
     opening in lc_abs *)
  | lc_fvar : forall x r, lc (e_fvar r x)
  | lc_equal : forall e1 e2, lc e1 -> lc e2 -> lc (e_equal e1 e2)
  | lc_typeof : forall e1, lc e1 -> lc (e_typeof e1)
  | lc_if : forall s e1 e2 e3, lc e1 -> lc e2 -> lc e3 -> lc (e_if s e1 e2 e3)
  | lc_app : forall e1 e2, lc e1 -> lc e2 -> lc (e_app e1 e2)
  | lc_abs : forall L t e1, 
      (forall x, x `notin` L -> lc (open e1 (e_fvar (runtime t) x))) ->
      lc (e_abs t e1)
  | lc_num : forall n, lc (e_num n)
  | lc_str : forall s, lc (e_str s)
  | lc_bool : forall b, lc (e_bool b).

Hint Constructors lc.


Inductive value : exp -> Prop :=
  | value_num : forall n, value (e_num n)
  | value_str : forall s, value (e_str s)
  | value_bool : forall b, value (e_bool b)
  | value_abs : forall t e, lc (e_abs t e) -> value (e_abs t e).

Inductive eval : exp -> exp -> Prop :=
  | eval_beta : forall t e1 e2,
      lc (e_abs t e1) -> value e2 ->
      eval (e_app (e_abs t e1) e2) (open e1 e2)
  | eval_equal_true : forall v1 v2, value v1 -> value v2 ->
      v1 = v2 -> eval (e_equal v1 v2) (e_bool true)
  | eval_equal_false : forall v1 v2, value v1 -> value v2 ->
      v1 <> v2 -> eval (e_equal v1 v2) (e_bool false)
  | eval_typeof_str : forall s, 
      eval (e_typeof (e_str s)) (e_str str_string)
  | eval_typeof_bool : forall b,
      eval (e_typeof (e_bool b)) (e_str str_boolean)
  | eval_typeof_num : forall n,
      eval (e_typeof (e_num n)) (e_str str_number)
  | eval_typeof_abs : forall t e1, lc (e_abs t e1) ->
      eval (e_typeof (e_abs t e1)) (e_str str_function)
  | e_if_true : forall e1 e2, lc e1 -> lc e2 ->
      eval (e_if no_split (e_bool true) e1 e2) e1
  | e_if_false : forall e1 e2, lc e1 -> lc e2 ->
      eval (e_if no_split (e_bool false) e1 e2) e2
  | cxt_equal_1 : forall e1 e1' e2, lc e2 -> eval e1 e1' ->
      eval (e_equal e1 e2) (e_equal e1' e2)
  | cxt_equal_2 : forall e1 e2 e2', value e1 -> eval e2 e2' ->
      eval (e_equal e1 e2) (e_equal e1 e2')
  | cxt_typeof : forall e e', eval e e' ->
      eval (e_typeof e) (e_typeof e')
  | cxt_if : forall s e1 e1' e2 e3, eval e1 e1' -> lc e2 -> lc e3 ->
      eval (e_if s e1 e2 e3) (e_if s e1' e2 e3)
  | cxt_app_1 : forall e1 e1' e2, lc e2 ->
      eval e1 e1' ->
      eval (e_app e1 e2) (e_app e1' e2)
  | cxt_app_2 : forall e1 e2 e2',
      value e1 ->
      eval e2 e2' ->
      eval (e_app e1 e2) (e_app e1 e2').

Inductive eval_multi : exp -> exp -> Prop :=
  | m_trans : forall e1 e2 e3, eval e1 e2 -> eval_multi e2 e3 -> eval_multi e1 e3
  | m_step : forall e1 e2, eval e1 e2 -> eval_multi e1 e2.

Hint Constructors value eval eval_multi.

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv x) in
  constr:(A `union` B `union` C `union` D).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.

Notation env := (list (atom * typ)).

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

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E (v : atom) R T T',
      ok E -> 
      binds v T E ->
      static R T = Some T' ->
      typing E (e_fvar R v) T'
  | typing_abs : forall L E e T1 T2,
      (forall (v : atom), v `notin` L ->
         typing ((v, T1) :: E) (open e (e_fvar (runtime T1) v)) T2) ->
      typing E (e_abs T1 e) (typ_arrow T1 T2)
  | typing_equal : forall E e1 e2 T,
      typing E e1 T ->
      typing E e2 T ->
      typing E (e_equal e1 e2) typ_boolean
  | typing_typeof : forall E e1 T,
      typing E e1 T ->
      typing E (e_typeof e1) typ_string
  | typing_if : forall E e1 e2 e3 T s,
      typing E e1 typ_boolean ->
      typing E e2 T ->
      typing E e3 T ->
      typing E (e_if s e1 e2 e3) T
  | typing_app : forall E e1 e2 T1 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (e_app e1 e2) T2
  | typing_num : forall E n, typing E (e_num n) typ_integer
  | typing_str : forall E s, typing E (e_str s) typ_string
  | typing_bool : forall E b, typing E (e_bool b) typ_boolean.

Hint Constructors typing.

Definition Number := rts.singleton rt_number.
Definition String := rts.singleton rt_string.

Hint Unfold Number String.

Example eg_typing_1 : 
  typing nil (e_num 9000) typ_integer.
Proof.
  apply typing_num.
Qed.

Example eg_typing_2 :
  typing nil (e_abs typ_integer (e_bvar (rts.singleton rt_number) 0))
             (typ_arrow typ_integer typ_integer).
Proof.
  pick fresh v and apply typing_abs.
  unfold open. simpl.
  apply typing_var with (T := typ_integer).
  auto. auto. auto.
Qed.

Lemma strong_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  ok (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G Eq Ok; subst.
  (* e_fvar *)
  apply typing_var with (T := T). exact Ok. 
  apply binds_weaken with (F := F) in H0. exact H0. exact Ok. exact H1.
  (* e_abs *)
  pick fresh v and apply typing_abs.
  apply H0 with (G0 := (v, T1) :: G).
  fsetdec.
  rewrite -> cons_concat_assoc. reflexivity.
  rewrite -> cons_concat_assoc. auto.
  (* e_equal *)
  apply typing_equal with (T := T).
  apply IHtyping1 with (G0 := G); auto.
  apply IHtyping2 with (G0 := G); auto.
  (* e_type *)
  apply typing_typeof with (T := T).
  apply IHtyping with (G0 := G); auto.
  apply typing_if with (T := T).
  apply IHtyping1 with (G0 := G); auto.
  apply IHtyping2 with (G0 := G); auto.
  apply IHtyping3 with (G0 := G); auto.
  (* e_app *)
  apply typing_app with (T1 := T1).
  apply IHtyping1; auto.
  apply IHtyping2; auto.
  (* constants *)
  apply typing_num.
  apply typing_str.
  apply typing_bool.
Qed.

Lemma weakening : forall E F e T,
    typing E e T ->
    ok (F ++ E) ->
    typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite <- (nil_concat _ (F ++ E)).
  apply strong_weakening; auto.
Qed.

Lemma typing_regular_lc : forall E e T,
  typing E e T -> lc e.
Proof.
  intros E e T H. induction H; eauto.
Qed.

Lemma substitution_var : forall E F u S T T' w v R,
  binds v T' (F ++ (w, S) :: E) ->
  ok (F ++ (w, S) :: E) ->
  Some T = static R T' ->
  typing E u S ->
  typing (F ++ E) (subst w u (e_fvar R v)) T.
Proof.
  intros E F u S T T' w v R Binds Ok Static H.
  simpl.
  destruct (v == w).
  Focus 2.
  (* v <> w, nothing to do *)
  apply typing_var with (T := T').
  apply ok_remove_mid_cons with (x := w) (a := S). exact Ok.
  apply binds_remove_mid with (y := w) (b := S). simpl. exact Binds. exact n.
  rewrite -> Static. reflexivity.
  (* v = w, substitution happens *)
  assert (T = S) as HypTeqS.
    rewrite -> e in Binds.
    apply binds_mid_eq with (F := F) (z := w) (E := E). simpl.
Admitted.

Theorem preservation : forall E e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J.
  inversion J. inversion J. (* contradictions *)
  (* e_equal *)
  inversion J; subst; auto.
  apply typing_equal with (T := T).
  apply IHtyping1.  exact H5. exact H0.
  apply typing_equal with (T := T).
  exact H. apply IHtyping2. exact H5.
  (* e_typeof *)
  inversion J; auto.
  apply typing_typeof with (T := T).
  apply IHtyping. exact H1.
  (* e_if *)
  inversion J; subst; auto. (* gg *)
  (* e_app *)
  
  
  apply IHtyping2.
  
 exact HypPreserv.

  inversion J; subst; auto. auto. auto. auto. auto.
  assert (typing E e' T) as HypPresv.



Example eg_typing_3 :
  typing nil
    (e_abs (e_if (split_bvar 0 Number String) 
                 (e_equal (e_typeof (e_bvar (rts.union Number String) 0))
                          (e_str str_number))
                 (e_bvar Number 0)
                 (e_num 42)))
    (typ_arrow (typ_union typ_integer typ_string) typ_integer).
Proof.
  pick fresh v and apply typing_abs.
  unfold open. simpl.
  apply typing_if.
  apply typing_equal with (T := typ_string).
  apply typing_typeof with (T := typ_union typ_integer typ_string).
  apply typing_var with (T := (typ_union typ_integer typ_string)). auto. auto. auto.
  apply typing_str.
  apply typing_var with (T := typ_union typ_integer typ_string). auto. auto. auto.
  apply typing_num.
Qed.

Example eg_eval_if : eval (e_if no_split (e_bool true) (e_num 50) (e_num 20)) 
                          (e_num 50).
  auto.
Qed.



Example eg_eval_app_if :
  eval (e_app (e_abs (e_if no_split (e_bvar (rts.singleton rt_boolean) 0) (e_num 42) (e_num 90))) (e_bool true))
       (e_if no_split (e_bool true) (e_num 42) (e_num 90)).
Proof.
  assert (open (e_if no_split (e_bvar (rts.singleton rt_boolean) 0) (e_num 42) (e_num 90)) (e_bool true) =
               (e_if no_split (e_bool true) (e_num 42) (e_num 90))).
    auto.
  rewrite <- H. 
  apply eval_beta.
    (* prove local closure *)
    apply lc_abs with (L := {}).
      intros. unfold open. simpl. auto.
    (* prove that (e_bool true) is a value *)
    auto.
Qed.

Example eg_eval_multi_app_if :
    eval_multi (e_app (e_abs (e_if no_split (e_bvar (rts.singleton rt_boolean) 0) (e_num 42) (e_num 90))) (e_bool true))
         (e_num 42).
Proof.
  apply m_trans with (e2 := e_if no_split (e_bool true) (e_num 42) (e_num 90)).
    apply eg_eval_app_if.
  auto.
Qed.
  

(*
  (lambda (x) // x : typ_union int string
    (if (equal? (typeof x) "string")
      (string-append x "hello")
      (+ x 1)))

  (lambda (x) // x : typ_union int string
    (let ([t (equal? (typeof x) "string")])
      (if t
        (string-append x "hello")
        (+ x 1))))

  (lambda (x)
    (app (lambda (t)
      (if t x-string ... x-int))
     (equal? (typeof x) "string")))

*)

Definition eg0 : exp :=
   (e_abs (e_app (e_abs (e_if (split_bvar 1 (rts.singleton rt_string) (rts.singleton rt_number))  (e_bvar (rts.singleton rt_boolean) 0)
                           (e_num 42) 
                           (e_bvar (rts.singleton rt_number) 1)))
                 (e_equal 
                   (e_typeof 
                     (e_bvar (rts.union (rts.singleton rt_string) (rts.singleton rt_number)) 0))
                   (e_str str_string)))).

Example eg_eval_ifsplit1 :
  (eval_multi (e_app eg0 (e_num 9000))
              (e_num 9000)).
Proof.
  unfold eg0.
  assert (
    (open (e_app (e_abs (e_if (split_bvar 1 (rts.singleton rt_string) (rts.singleton rt_number))  (e_bvar (rts.singleton rt_boolean) 0)
                           (e_num 42) 
                           (e_bvar (rts.singleton rt_number) 1)))
                 (e_equal 
                   (e_typeof 
                     (e_bvar (rts.union (rts.singleton rt_string) (rts.singleton rt_number)) 0))
                   (e_str str_string)))
          (e_num 9000)) =
    (e_app (e_abs (e_num 9000))
           (e_equal 
             (e_typeof 
               (e_num 9000))
             (e_str str_string))) ).
    unfold open.  simpl. reflexivity.
  apply m_trans with (e2 := (e_app (e_abs (e_num 9000))
           (e_equal 
             (e_typeof 
               (e_num 9000))
             (e_str str_string)))).
    rewrite <- H. apply eval_beta.
    apply lc_abs with (L := {}).
    intros. unfold open. simpl.
    apply lc_app. apply lc_abs with (L :=  {}).
    intros. unfold open. simpl. apply lc_if. auto. auto. auto.
    auto. auto.
  apply m_step.
  apply eval_beta with (e1 := e_num 9000) (e2 := 
           (e_equal 
             (e_typeof 
               (e_num 9000))
             (e_str str_string))).
  apply lc_abs with (L := {}). intros. unfold open. simpl. apply lc_num.
  apply H0.
  
    simpl. 
  
  apply m_trans with (e2 := open (e_app (e_abs (e_if no_split (e_bvar (rts.singleton rt_boolean) 0)
                           (e_num 42) 
                           (e_bvar (rts.singleton rt_number) 1))).
                 (e_equal 
                   (e_typeof 
                     (e_bvar (rts.union (rts.singleton rt_string) (rts.singleton rt_number)) 0))
                   (e_str str_string))) (e_str str_string)).
    
    auto.
  auto.






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

