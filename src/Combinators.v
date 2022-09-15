Require Import LC.Util.Fin.
Require Import LC.Util.Vec.
Require Import LC.Util.Star.
Require Import LC.LC.
Require Import LC.CNum.
Require Import LC.Bool.
Require Import LC.Tuple.

Definition S_COMB {n} : Term n :=
  Lam (Lam (Lam (var 2 # var 0 # (var 1 # var 0)))).

Definition S_COMB_reds {n} (M N P : Term n) :
  reds (S_COMB # M # N # P) (M # P # (N # P)).
Proof.
  unfold S_COMB.
  normal_order.
Qed.

#[export]
Instance S_COMB_Const : Const (@S_COMB).
Proof.
  constructor; reflexivity.
Qed.

#[global]
Opaque S_COMB.

Definition FLIP_CURRY {n} : Term n :=
  Lam (Lam (Lam (var 2 # (PAIR # var 0 # var 1)))).

#[export]
Instance FLIP_CURRY_Const : Const (@FLIP_CURRY).
Proof.
  constructor; reflexivity.
Qed.

Lemma FLIP_CURRY_reds {n} (F E : Term n ) :
  reds (FLIP_CURRY # F # E) (Lam
     (weaken F (inl tt)
      # (PAIR # var 0
         # weaken E (inl tt)))).
Proof.
  unfold FLIP_CURRY.
  normal_order.
Qed.

#[global]
Opaque FLIP_CURRY.
