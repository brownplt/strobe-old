Add LoadPath "metatheory".
Require Import Metatheory.

Inductive RT : Set :=
  | rt_number : RT
  | rt_string : RT
  | rt_boolean : RT
  | rt_function : RT.

Module RT_as_OT.

  Require Import Coq.FSets.OrderedType.
  Require Import Compare_dec.

  Definition t := RT.
  Definition eq := @eq RT.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition lt (x y:RT) : Prop := match x, y with
  | rt_number, rt_string => True
  | rt_number, rt_boolean => True
  | rt_number, rt_function => True
  | rt_string, rt_boolean => True
  | rt_string, rt_function => True
  | rt_boolean, rt_function => True
  | _, _ => False
  end.


  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    destruct x;
    destruct y;
    destruct z;
    (inversion H0 || inversion H || apply H || (simpl; simpl in H; apply H)).
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~ x=y.
  Proof.
    intros.
    destruct x; destruct y; (inversion H || discriminate).
  Qed.     
  Check forall x y , Compare lt eq x y.

  Definition compare : forall x y, Compare lt eq x y.
    intros. 
    destruct x; destruct y;
    ((apply EQ; unfold eq; reflexivity) || 
     (apply LT; unfold lt; exact I) ||
     (apply GT; unfold lt; exact I)).
  Defined.

  Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
    intros.
    destruct x; destruct y; 
    ((apply left; reflexivity) || (apply right; discriminate)).
  Qed.

End RT_as_OT.

Require Import FiniteSets.
Require Import FSetDecide.

Module rts_module := FiniteSets.Make (RT_as_OT).
Module rts := rts_module.F.
Module rts_props := FSetProperties.Properties (rts).
Module rts_facts := FSetFacts.Facts (rts).
Module rts_decide := FSetDecide.Decide (rts).

Ltac rtsdec := try apply rts_module.eq_if_Equal; rts_decide.fsetdec.

Notation RTS := rts_module.F.t.

