Require Import List.
Import ListNotations.

Require Import LC.Util.Fin.
Require Import LC.Util.Vec.
Require Import LC.Util.Star.

Inductive Term : nat -> Type :=
  | Var : forall {n}, Fin n -> Term n
  | App : forall {n}, Term n -> Term n -> Term n
  | Lam : forall {n}, Term (S n) -> Term n.

Infix "#" := App (left associativity, at level 40).

Definition var {n} (i : nat) : Term (i + S n) :=
  Var (Fin_of_nat i).

Fixpoint weaken {n} (t : Term n) : Fin (S n) -> Term (S n) :=
  match t with
  | Var j => fun i => Var (shift i j)
  | t1 # t2 => fun i => weaken t1 i # (weaken t2 i)
  | Lam t' => fun i => Lam (weaken t' (inr i))
  end.

Fixpoint subst {n} (t : Term (S n)) : Fin (S n) -> Term n -> Term n :=
  match t in Term m
    return S n = m -> Fin (S n) -> Term n -> Term n with
  | Var j => fun pf i u =>
    match pf with
    | eq_refl => fun j' =>
      match avoid i j' with
      | Some k => Var k
      | None => u
      end
    end j
  | t1 # t2 => fun pf i u =>
    match pf with
    | eq_refl => fun s1 s2 =>
      subst s1 i u # subst s2 i u
    end t1 t2
  | Lam t' => fun pf i u =>
    match pf with
    | eq_refl => fun s =>
      Lam (@subst (S n) s (inr i) (weaken u i))
    end t'
  end eq_refl.

Lemma subst_weaken {n} : forall (M N : Term n) (i : Fin (S n)),
  subst (weaken M i) i N = M.
Proof.
  induction M; intros; simpl.
  - now rewrite avoid_shift.
  - now rewrite IHM1, IHM2.
  - now rewrite IHM.
Qed.

Inductive red : forall {n}, Term n -> Term n -> Prop :=
  | beta_red : forall {n} (t : Term (S n)) (u : Term n),
    red (Lam t # u) (subst t (inl tt) u)
  | app_red_l : forall {n} (t t' u : Term n),
    red t t' -> red (t # u) (t' # u)
  | app_red_r : forall {n} (t u u' : Term n),
    red u u' -> red (t # u) (t # u')
  | lam_red : forall {n} (t t' : Term (S n)),
    red t t' -> red (Lam t) (Lam t').

Definition reds {n} : Term n -> Term n -> Prop :=
  star red.

Lemma app_reds_l : forall {n} (t t' u : Term n),
  reds t t' -> reds (t # u) (t' # u).
Proof.
  intros n t t' u r.
  induction r.
  { apply star_refl. }
  { eapply R_star.
    { apply app_red_l; eauto. }
    { auto. }
  }
Qed.

Lemma app_reds_r : forall {n} (t u u' : Term n),
  reds u u' -> reds (t # u) (t # u').
Proof.
  intros n t t' u r.
  induction r.
  { apply star_refl. }
  { eapply R_star.
    { apply app_red_r; eauto. }
    { auto. }
  }
Qed.

Lemma lam_reds : forall {n} (t t' : Term (S n)),
  reds t t' -> reds (Lam t) (Lam t').
Proof.
  intros n t t' r.
  induction r.
  { apply star_refl. }
  { eapply R_star.
    { apply lam_red; eauto. }
    { auto. }
  }
Qed.

Definition not_lam {n} (t : Term n) : Prop :=
  match t with
  | Lam _ => False
  | _ => True
  end.

Fixpoint normal {n} (t : Term n) : Prop :=
  match t with
  | Var _ => True
  | App t1 t2 =>
         not_lam t1
      /\ normal t1
      /\ normal t2
  | Lam t' => normal t'
  end.

Lemma normal_no_red : forall {n} (t t' : Term n),
  normal t -> ~ red t t'.
Proof.
  intros n t t' norm_t red_tt'.
  induction red_tt';
  simpl in norm_t; tauto.
Qed.

Lemma no_red_normal : forall {n} (t : Term n),
  (forall t', ~ red t t') -> normal t.
Proof.
  intros n t.
  induction t; intros.
  - exact I.
  - simpl; repeat split.
    + destruct t1; [exact I|exact I|].
      eapply H.
      apply beta_red.
    + apply IHt1.
      intros t' Hr.
      eapply H.
      apply app_red_l; eauto.
    + apply IHt2.
      intros t' Hr.
      eapply H.
      apply app_red_r; eauto.
  - apply IHt.
    intros t' Hr.
    eapply H.
    apply lam_red; eauto.
Qed.

Class Const (T : forall n, Term n) : Prop := {
  weaken_const : forall n i, weaken (T n) i = T (S n)
  }.

Lemma subst_const {T} `{Const T} :
  forall n i U, subst (T (S n)) i U = T n.
Proof.
  intros.
  rewrite <- (weaken_const _ i).
  now rewrite subst_weaken.
Qed.
