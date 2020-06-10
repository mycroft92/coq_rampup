Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From LF Require Import Maps.

Module AExp.

Inductive aexp : Type :=
 | ANum (n : nat)
 | APlus (a1 a2 : aexp)
 | AMinus (a1 a2 : aexp)
 | AMult (a1 a2  : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a:aexp) : nat :=
  match a with
  | ANum x => x
  | APlus a1 a2  => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2  => (aeval a1) * (aeval a2)
  end.

Compute  aeval (APlus (ANum 2) (ANum 2)) .

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

  Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1 eqn:Ea1.
    + destruct n eqn:En.
      * simpl. apply IHa2.
      * simpl. rewrite -> IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
    rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1.
    rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

(*The above proof with case reductions and automation*)
Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity); try (* ANum *) reflexivity.
    - destruct a1 eqn:Ea1;
      try (simpl; simpl in IHa1; rewrite IHa1;rewrite IHa2;reflexivity).
      destruct n eqn:En ; simpl; rewrite IHa2; reflexivity.

Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1)  (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
intros b.
induction b ;  
(*For aeval just rewrite with already proven stuff*)
try (simpl; repeat rewrite optimize_0plus_sound ;  reflexivity).
- simpl.  rewrite IHb. reflexivity.
- simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(*Presburger arithmetic*)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.



Module aevalR_first_try.
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).


    
End aevalR_first_try.

Notation "e '\\' n"
      := (aevalR_first_try.aevalR e n)
         (at level 50, left associativity)
      : type_scope.


Module bevalR_first_try.
Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue  : bevalR BTrue true 
  | E_BFalse : bevalR BFalse false
  | E_BEq (e1 e2: aexp) (n1 n2 :nat) : 
    aevalR_first_try.aevalR e1 n1 ->
    aevalR_first_try.aevalR e2 n2 ->
    bevalR (BEq e1 e2) (n1 =? n2)
  | E_BLe (e1 e2: aexp) (n1 n2 :nat) : 
    aevalR_first_try.aevalR e1 n1 ->
    aevalR_first_try.aevalR e2 n2 ->
    bevalR (BLe e1 e2) (n1 <=? n2)
  | E_BNot (b: bexp) (bv: bool) :
    bevalR b bv ->
    bevalR (BNot b) (negb bv)
  | E_BAnd (b1 b2: bexp) (bv1 bv2: bool) :
    bevalR b1 bv1 ->
    bevalR b2 bv2 ->
    bevalR (BAnd b1 b2) ( bv1 && bv2).

    
End bevalR_first_try.


Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  split.
  - intros H. 
    induction H; 
    simpl;  try (rewrite -> IHaevalR1; rewrite -> IHaevalR2) ; reflexivity.
  - generalize dependent n. 
    induction a; simpl; intros; subst; constructor; 
    try apply IHa1 ; try apply IHa2; reflexivity.
Qed. 

Lemma beval_iff_bevalR : forall b bv,
  bevalR_first_try.bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros H. 
    induction H as [| |e1 e2 n1 n2 He1 He2| e1 e2 n1 n2 He1 He2| b bv Hb| b1 b2 bv1 bv2  Hb1 Hb2];
    simpl; 
    try (apply (aeval_iff_aevalR e1) in He1; apply (aeval_iff_aevalR e2) in He2); subst; reflexivity. 
  - generalize dependent bv.
   induction b; 
   simpl; intros; subst; constructor;
   try apply aeval_iff_aevalR; try reflexivity; 
   [apply IHb|  apply IHb1|  apply IHb2]; reflexivity.
Qed.



    
End AExp.


Definition state := total_map nat.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive aexp : Type :=
 | ANum (n : nat)
 | APlus (a1 a2 : aexp)
 | AId (x:string)
 | AMinus (a1 a2 : aexp)
 | AMult (a1 a2  : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).


Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.
Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~(X <= 4))%imp : bexp.
(* Set Printing Coercions.
Print example_bexp. *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
match a with
| ANum n => n
| AId x => st x(* <--- NEW *)
| APlus a1 a2 => (aeval st a1) + (aeval st a2)
| AMinus a1 a2 => (aeval st a1) - (aeval st a2)
| AMult a1 a2 => (aeval st a1) * (aeval st a2)
end.
Fixpoint beval (st : state) (b : bexp) : bool :=
match b with
| BTrue => true
| BFalse => false
| BEq a1 a2 => (aeval st a1) =? (aeval st a2)
| BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
| BNot b1 => negb (beval st b1)
| BAnd b1 b2 => andb (beval st b1) (beval st b2)
end.

Definition empty_st := (_ !-> 0).
Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))%imp
  = 13.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).