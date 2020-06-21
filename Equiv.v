Set Warnings "-notation-overridden,-parsing".
From LF  Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From LF  Require Import Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (a1 a2 : bexp) : Prop :=
    forall (st : state),
      beval st a1 = beval st a2.

(**)
Theorem aequiv_example: aequiv (X - X) 0.
Proof.
    intros st. simpl. omega.
Qed.

Theorem bequiv_example: bequiv (X - X = 0)%imp true.
Proof.
  intros st.  unfold beval. rewrite aequiv_example. auto.
Qed.

(*For commands it's not as simple as eval, since the ending state might not be reached*)

Definition cequiv (c1 c2 : com) : Prop :=
    forall (st st':state), st =[c1]=> st' <-> st=[c2]=>st'.


Theorem skip_left : forall c,
  cequiv
    (SKIP;; c)
    c.
Proof.
    intros c st st'. split; intros H.
    - inversion H; subst. inversion H2; subst. assumption.
    - eapply E_Seq. apply E_Skip. assumption.
Qed.
    
Theorem skip_right : forall c,
  cequiv c
    (c ;; SKIP).
Proof.
    intros c st st'. split; intros H.
    - apply E_Seq with st'. assumption. apply E_Skip.
    - inversion H; subst. inversion H5; subst. assumption.
Qed.

(*Will continue this later after types and STLC.*)
    
    
Print All.
