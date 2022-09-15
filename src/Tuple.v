Require Import LC.Util.Fin.
Require Import LC.Util.Vec.
Require Import LC.Util.Star.
Require Import LC.LC.
Require Import LC.Bool.

Definition PAIR {n} : Term n :=
  Lam (Lam (Lam (var 0 # var 2 # var 1))).

Definition NIL {n} : Term n :=
  Lam TRUE.

Opaque NIL.

#[export]
Instance NIL_Const : Const (@NIL).
Proof.
  constructor; reflexivity.
Qed.

Fixpoint tup {m n} : Vec (Term n) m -> Term n :=
  match m with
  | 0 => fun _ => NIL
  | S p => fun '(t, ts) => PAIR # t # tup ts
  end.

Definition Vars n : Term n :=
  tup (vmap Var (Fins n)).

Definition FST {n} : Term n :=
  Lam (var 0 # TRUE).

#[export]
Instance FST_Const : Const (@FST).
Proof.
  constructor; reflexivity.
Qed.

Definition SND {n} : Term n :=
  Lam (var 0 # FALSE).

#[export]
Instance SND_Const : Const (@SND).
Proof.
  constructor; reflexivity.
Qed.

Lemma FST_PAIR {n} : forall M N : Term n,
  reds (FST # (PAIR # M # N)) M.
Proof.
  intros M N.
  unfold FST, PAIR.
  normal_order.
  apply TRUE_reds.
Qed.

Lemma SND_PAIR {n} : forall M N : Term n,
  reds (SND # (PAIR # M # N)) N.
Proof.
  intros M N.
  unfold SND, PAIR.
  normal_order.
  apply FALSE_reds.
Qed.

#[export]
Instance PAIR_Const : Const (@PAIR).
Proof.
  constructor; reflexivity.
Qed.

Opaque PAIR.

Definition LOOKUP {n} : Term n :=
  Lam (var 0 # Lam (Lam (var 1 # (SND # var 0))) # FST).

#[export]
Instance LOOKUP_Const : Const (@LOOKUP).
Proof.
  constructor; reflexivity.
Qed.
