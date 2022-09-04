Require Import LC.Util.Fin.
Require Import LC.Util.Vec.
Require Import LC.Util.Star.
Require Import LC.LC.

Fixpoint cnum_aux {n} (x : nat) : Term (S (S n)) :=
  match x with
  | 0 => Var (inl tt : Fin (S (S n)))
  | S y => App (Var (inr (inl tt) : Fin (S (S n))))
            (cnum_aux y)
  end.

Definition cnum (i : nat) {n} : Term n :=
  Lam (Lam (cnum_aux i)).

Lemma cnum_aux_normal {n} (x : nat) :
  normal (@cnum_aux n x).
Proof.
  induction x; simpl; tauto.
Qed.

#[export]
Instance cnum_Const {x} : Const (@cnum x).
Proof.
  constructor.
  unfold cnum.
  simpl.
  intros n i.
  do 2 f_equal.
  induction x.
  { reflexivity. }
  { simpl.
    now rewrite IHx.
  }
Qed.

Opaque cnum.
