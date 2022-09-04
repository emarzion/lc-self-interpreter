Require Import LC.Util.Fin.
Require Import LC.Util.Vec.
Require Import LC.Util.Star.
Require Import LC.LC.

Definition TRUE {n} : Term n :=
  Lam (Lam (var 1)).

#[export]
Instance TRUE_Const : Const (@TRUE).
Proof.
  constructor; reflexivity.
Defined.

Lemma TRUE_normal {n} :
  @normal n TRUE.
Proof.
  exact I.
Qed.

Definition FALSE {n} : Term n :=
  Lam (Lam (var 0)).

Lemma FALSE_normal {n} :
  @normal n FALSE.
Proof.
  exact I.
Qed.

#[export]
Instance FALSE_Const : Const (@FALSE).
Proof.
  constructor; reflexivity.
Qed.

Lemma TRUE_reds {n} : forall M N : Term n,
  reds (App (App TRUE M) N) M.
Proof.
  intros M N.
  eapply R_star.
  { apply app_red_l.
    apply beta_red.
  }
  simpl.
  rewrite avoid_refl.
  eapply R_star.
  { apply beta_red. }
  rewrite subst_weaken.
  apply star_refl.
Qed.

#[global]
Opaque TRUE.

Lemma FALSE_reds {n} : forall M N : Term n,
  reds (App (App FALSE M) N) N.
Proof.
  intros M N.
  eapply R_star.
  { apply app_red_l.
    apply beta_red.
  }
  simpl.
  eapply R_star.
  { apply beta_red. }
  simpl.
  rewrite avoid_refl.
  apply star_refl.
Qed.

#[global]
Opaque FALSE.
