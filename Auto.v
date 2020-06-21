
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import omega.Omega.
From LF Require Import Maps.
From LF Require Import Imp.

Ltac inv H := inversion H; subst; clear H.

Ltac rew_inv H1 h2 := rewrite h2 in H1; inversion H1.

Ltac find_rwinv :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rew_inv H1 H2
  end.

Ltac find_eqn :=
    match goal with
    H1 : forall x, ?P x -> ?L = ?R,
    H2 : ?P ?X
    |- _ => rewrite (H1 X H2) in *; auto
    end.

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
    intros c st st1 st2 E1 E2. generalize dependent st2; 
    induction E1; intros st2 E2; inv E2; try find_rwinv; auto. 
    - find_eqn. (* rewrite (IHE1_1 st'0 H1) in *. auto. *)
    - find_eqn. (*rewrite (IHE1_1 st'0 H3) in *. auto. *)
    (* -  
        + rewrite H in H5. inversion H5.
    - 
        + rew_inv H5 H.
    - 
        + rew_inv H2 H.
    -   
        + rew_inv H4 H. *)
    (* - assert (st' = st'0) as EQ2 by auto. subst st'0. auto.  *)
Qed.