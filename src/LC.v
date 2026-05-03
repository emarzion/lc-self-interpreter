Require Import List Lia.
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

Fixpoint var_map {n m} (T : Term n) : (Fin n -> Term m) -> Term m :=
  match T with
  | Var i => fun f => f i
  | App T1 T2 => fun f => App (var_map T1 f) (var_map T2 f)
  | Lam T' => fun f => Lam (var_map T' (fun i =>
    match i with
    | inl _ => var 0
    | inr j => weaken (f j) (inl tt)
    end))
  end.

Lemma var_map_ext {n} (T : Term n) : forall m
  (f g : Fin n -> Term m),
  (forall i, f i = g i) ->
  var_map T f = var_map T g.
Proof.
  induction T; intros.
  - simpl. apply H.
  - simpl.
    rewrite (IHT1 _ f g H).
    now rewrite (IHT2 _ f g H).
  - simpl. f_equal.
    apply IHT; intros [|].
    + auto.
    + simpl.
      rewrite H.
      auto.
Qed.

Lemma var_map_weaken {n} (T : Term n) : forall (i : Fin (S n)) m
  (f : Fin (S n) -> Term m),
  var_map (weaken T i) f =
  var_map T (fun j => f (shift i j)).
Proof.
  induction T; intros.
  - simpl. auto.
  - simpl.
    rewrite IHT1.
    rewrite IHT2.
    auto.
  - simpl. f_equal.
    rewrite IHT.
    apply var_map_ext.
    intros [|].
    + simpl. auto.
    + simpl. auto.
Qed.

Definition subst {n} (t : Term (S n)) (i : Fin (S n)) (u : Term n) : Term n :=
  var_map t (fun j =>
    match avoid i j with
    | Some k => Var k
    | None => u
    end).

Lemma shift_inl {n} (i : Fin n) :
  shift (inl tt) i = inr i.
Proof.
  destruct n.
  - destruct i.
  - auto.
Qed.

Lemma var_map_Var {n} (T : Term n) :
  var_map T Var = T.
Proof.
  induction T.
  - simpl. auto.
  - simpl; congruence.
  - simpl.
    rewrite var_map_ext with (g := Var).
    + congruence.
    + intros [[]|j]; auto.
      now rewrite shift_inl.
Qed.

Lemma subst_weaken {n} : forall (M N : Term n) (i : Fin (S n)),
  subst (weaken M i) i N = M.
Proof.
  unfold subst; intros.
  rewrite var_map_weaken.
  rewrite var_map_ext with (g := Var).
  - apply var_map_Var.
  - intro; now rewrite avoid_shift.
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

Lemma subst_Var {n} (j i : Fin (S n)) (U : Term n) :
  subst (Var j) i U =
  match avoid i j with
  | Some j' => Var j'
  | None => U
  end.
Proof.
  auto.
Qed.

Lemma subst_App {n} (T1 T2 : Term (S n)) (i : Fin (S n))
  (U : Term n) :
  subst (T1 # T2) i U = subst T1 i U # subst T2 i U.
Proof.
  auto.
Qed.

Lemma subst_Lam {n} (T : Term (S (S n))) (i : Fin (S n)) (U : Term n) :
  subst (Lam T) i U = Lam (subst T (inr i) (weaken U (inl tt))).
Proof.
  unfold subst; simpl.
  f_equal.
  apply var_map_ext.
  intros [|j].
  - auto.
  - destruct (avoid i j).
    + simpl.
      rewrite shift_inl. auto.
    + auto.
Qed.

Lemma weaken_var_map {n} (T : Term n) (i : Fin (S n)) :
  weaken T i = var_map T (fun j => Var (shift i j)).
Proof.
  induction T.
  - simpl. auto.
  - simpl.
    rewrite IHT1, IHT2. auto.
  - simpl.
    rewrite IHT. f_equal.
    apply var_map_ext.
    intros [|j]; auto.
Qed.

Lemma avoid_shift_inv {n} (i j : Fin (S n)) (j' : Fin n) :
  avoid i j = Some j' ->
  shift i j' = j.
Proof.
  induction n; intro pf.
  - destruct j'.
  - simpl in *.
    destruct i.
    + destruct j; congruence.
    + destruct j.
      * inversion pf. now destruct u.
      * destruct (avoid s s0) eqn:?; [|discriminate].
        apply IHn in Heqo.
        inversion pf. congruence.
Qed.

Fixpoint nat_shift (block x : nat) : nat :=
  match block with
  | 0 => S x
  | S block' =>
    match x with
    | 0 => 0
    | S y => S (nat_shift block' y)
    end
  end.

Lemma ltb_S x y :
  Nat.ltb (S x) (S y) = Nat.ltb x y.
Proof.
  unfold Nat.ltb.
  simpl; now destruct y.
Qed.

Lemma nat_shift_order block : forall x,
  nat_shift block x =
  if Nat.ltb x block then x else S x.
Proof.
  induction block; intro x.
  - auto.
  - destruct x as [|y]; simpl.
    + auto.
    + rewrite ltb_S.
      rewrite IHblock.
      now destruct Nat.ltb.
Qed.

Fixpoint nat_avoid (block x : nat) : option nat :=
  match block with
  | 0 =>
    match x with
    | 0 => None
    | S y => Some y
    end
  | S block' =>
    match x with
    | 0 => Some 0
    | S y => option_map S (nat_avoid block' y)
    end
  end.

Lemma avoid_inr_inr {n} (i j : Fin (S n)) :
  avoid ((inr i) : Fin (S (S n))) (inr j) = option_map inr (avoid i j).
Proof.
  simpl.
  destruct (avoid i j); auto.
Qed.

Lemma nat_of_Fin_inr {n} (i : Fin n) :
  nat_of_Fin ((inr i) : Fin (S n)) = S (nat_of_Fin i).
Proof.
  auto.
Qed.

Lemma nat_avoid_correct {n} (i j : Fin (S n)) :
  option_map nat_of_Fin (avoid i j) =
  nat_avoid (nat_of_Fin i) (nat_of_Fin j).
Proof.
  induction n.
  - destruct i as [|[]].
    destruct j as [|[]].
    auto.
  - destruct i as [|i'].
    + destruct j as [|j']; auto.
    + destruct j as [|j']; auto.
      specialize (IHn i' j').
      rewrite avoid_inr_inr.
      repeat rewrite nat_of_Fin_inr.
      unfold nat_avoid; fold nat_avoid.
      rewrite <- IHn.
      destruct (avoid i' j'); auto.
Qed.

Lemma nat_avoid_order2 block : forall x,
  match Nat.compare block x with
  | Eq => nat_avoid block x = None
  | Lt => option_map S (nat_avoid block x) = Some x
  | Gt => nat_avoid block x = Some x
  end.
Proof.
  induction block; intro x.
  - destruct x as [|y].
    + simpl; auto.
    + simpl; auto.
  - destruct x as [|y].
    + simpl; auto.
    + simpl.
      specialize (IHblock y).
      destruct Nat.compare;
        rewrite IHblock; auto.
Qed.

Lemma nat_avoid_order block : forall x,
  nat_avoid block x =
  match Nat.compare block x with
  | Eq => None
  | Lt => Some (pred x)
  | Gt => Some x
  end.
Proof.
  induction block; intro x.
  - destruct x as [|y].
    + auto.
    + auto.
  - destruct x as [|y].
    + auto.
    + simpl.
      rewrite IHblock.
      destruct Nat.compare eqn:?; auto.
      simpl.
      rewrite PeanoNat.Nat.compare_lt_iff in Heqc.
      f_equal; lia.
Qed.

Lemma nat_shift_correct {n} (i : Fin (S n)) (j : Fin n) :
  nat_of_Fin (shift i j) = nat_shift (nat_of_Fin i) (nat_of_Fin j).
Proof.
  induction n.
  - destruct j.
  - simpl shift.
    destruct i.
    + destruct j; auto.
    + destruct j; auto.
      repeat rewrite @nat_of_Fin_inr.
      unfold nat_shift; fold nat_shift.
      rewrite IHn; auto.
Qed.

Lemma Fin_ext {n} (i j : Fin n) :
  nat_of_Fin i = nat_of_Fin j -> i = j.
Proof.
  induction n; intro pf.
  - destruct i.
  - destruct i.
    + destruct j.
      * now destruct u, u0.
      * discriminate.
    + destruct j.
      * discriminate.
      * simpl in pf; inversion pf.
        apply IHn in H0. congruence.
Qed.

Lemma Some_inj {X} (x x' : X) :
  Some x = Some x' -> x = x'.
Proof.
  intro pf; inversion pf; auto.
Qed.

Lemma shift_shift {n} (i j : Fin (S (S n))) (i' j' : Fin (S n)) :
  avoid i j = Some j' ->
  avoid j i = Some i' -> forall k,
  shift j (shift i' k) = shift i (shift j' k).
Proof.
  intros pf1 pf2 k.
  apply Fin_ext.
  repeat rewrite nat_shift_correct.
  apply (f_equal (option_map nat_of_Fin)) in pf1, pf2.
  rewrite nat_avoid_correct in pf1, pf2.
  unfold option_map in pf1, pf2.
  pose proof (nat_avoid_order2 (nat_of_Fin i) (nat_of_Fin j)) as pf3.
  pose proof (nat_avoid_order2 (nat_of_Fin j) (nat_of_Fin i)) as pf4.
  rewrite PeanoNat.Nat.compare_antisym in pf4.
  pose (fi := nat_of_Fin i).
  pose (fj := nat_of_Fin j).
  pose (fi' := nat_of_Fin i').
  pose (fj' := nat_of_Fin j').
  pose (fk := nat_of_Fin k).
  fold fi fj fi' fj' in pf1, pf2, pf3, pf4.
  fold fi fj fi' fj' fk.
  destruct (Nat.compare fi fj) eqn:Hc.
  - congruence.
  - simpl CompOpp in pf4; cbv iota in pf4.
    unfold option_map in pf3.
    rewrite pf1 in pf3.
    rewrite pf2 in pf4.
    apply Some_inj in pf3, pf4.
    rewrite (nat_shift_order fi' fk).
    rewrite (nat_shift_order fj' fk).
    rewrite <- Compare_dec.nat_compare_lt in Hc.
    rewrite <- pf3, <- pf4 in *.
    destruct (Nat.ltb fk fi') eqn:Hc1.
    + rewrite PeanoNat.Nat.ltb_lt in Hc1.
      assert (fk < fj') as pf5 by lia.
      rewrite <- PeanoNat.Nat.ltb_lt in pf5.
      rewrite pf5.
      repeat rewrite nat_shift_order.
      rewrite <- PeanoNat.Nat.ltb_lt in Hc1.
      rewrite Hc1.
      rewrite PeanoNat.Nat.ltb_lt in pf5.
      apply PeanoNat.Nat.lt_lt_succ_r in pf5.
      rewrite <- PeanoNat.Nat.ltb_lt in pf5.
      now rewrite pf5.
    + rewrite PeanoNat.Nat.ltb_ge in Hc1.
      simpl nat_shift.
      destruct (Nat.ltb fk fj') eqn:Hc2.
      * repeat rewrite nat_shift_order.
        rewrite Hc2.
        rewrite <- PeanoNat.Nat.ltb_ge in Hc1.
        now rewrite Hc1.
      * repeat rewrite nat_shift_order.
        rewrite Hc2.
        rewrite PeanoNat.Nat.ltb_ge in Hc2.
        assert (fi' <= S fk) as pf5 by lia.
        rewrite <- PeanoNat.Nat.ltb_ge in pf5.
        now rewrite pf5.
  - simpl CompOpp in pf4; cbv iota in pf4.
    unfold option_map in pf4.
    rewrite pf1 in pf3.
    rewrite pf2 in pf4.
    apply Some_inj in pf3, pf4.
    rewrite (nat_shift_order fi' fk).
    rewrite (nat_shift_order fj' fk).
    rewrite <- Compare_dec.nat_compare_gt in Hc.
    rewrite <- pf3, <- pf4 in *.
    destruct (Nat.ltb fk fj') eqn:Hc1.
    + rewrite PeanoNat.Nat.ltb_lt in Hc1.
      assert (fk < fi') as pf5 by lia.
      rewrite <- PeanoNat.Nat.ltb_lt in pf5.
      rewrite pf5.
      repeat rewrite nat_shift_order.
      rewrite <- PeanoNat.Nat.ltb_lt in Hc1.
      rewrite Hc1.
      rewrite PeanoNat.Nat.ltb_lt in pf5.
      apply PeanoNat.Nat.lt_lt_succ_r in pf5.
      rewrite <- PeanoNat.Nat.ltb_lt in pf5.
      now rewrite pf5.
    + rewrite PeanoNat.Nat.ltb_ge in Hc1.
      simpl nat_shift.
      destruct (Nat.ltb fk fi') eqn:Hc2.
      * repeat rewrite nat_shift_order.
        rewrite Hc2.
        rewrite <- PeanoNat.Nat.ltb_ge in Hc1.
        now rewrite Hc1.
      * repeat rewrite nat_shift_order.
        rewrite Hc2.
        rewrite PeanoNat.Nat.ltb_ge in Hc2.
        assert (fj' <= S fk) as pf5 by lia.
        rewrite <- PeanoNat.Nat.ltb_ge in pf5.
        now rewrite pf5.
Qed.

Lemma weaken_comm {n} (T : Term n) : forall i i' j j',
  avoid i j = Some j' ->
  avoid j i = Some i' ->
  weaken (weaken T i') j = weaken (weaken T j') i.
Proof.
  induction T; intros.
  - unfold weaken. f_equal.
    apply shift_shift; auto.
  - simpl.
    erewrite IHT1, IHT2; eauto.
  - simpl. f_equal.
    apply IHT.
    + rewrite @avoid_inr_inr.
      rewrite H; auto.
    + rewrite @avoid_inr_inr.
      rewrite H0; auto.
Qed.

Lemma weak_var_map {n} (T : Term n) : forall {m} (f : Fin n -> Term m) i,
  weaken (var_map T f) i =
  var_map T (fun j => weaken (f j) i).
Proof.
  induction T; intros.
  - auto.
  - simpl.
    rewrite IHT1, IHT2. auto.
  - simpl; rewrite IHT.
    f_equal.
    apply var_map_ext.
    intros [|j]; auto.
    induction (f j).
    + simpl. rewrite shift_inl. auto.
    + simpl.
      rewrite IHt1, IHt2; auto.
    + apply weaken_comm.
      * simpl. auto.
      * simpl. auto.
Qed.

Lemma var_map_comps {n} (T : Term n) : forall m k
  (f : Fin n -> Term m) (g : Fin m -> Term k),
  var_map (var_map T f) g =
  var_map T (fun i => var_map (f i) g).
Proof.
  induction T; intros.
  - auto.
  - simpl; rewrite IHT1, IHT2; auto.
  - simpl; rewrite IHT.
    f_equal.
    apply var_map_ext.
    intros [|j]; auto.
    rewrite var_map_weaken.
    rewrite weak_var_map.
    apply var_map_ext.
    intro i; now rewrite shift_inl.
Qed.

Lemma reds_refl {n} (T T' : Term n) :
  T = T' -> reds T T'.
Proof.
  intro; subst.
  constructor.
Qed.

Lemma avoid_inl_inr {n} (i : Fin n) :
  avoid (inl tt) (inr i) = Some i.
Proof.
  destruct n.
  - destruct i.
  - auto.
Qed.

Definition sw {n} (T U : Term n) (i j : Fin (S n)) : Term n :=
  var_map T (fun k =>
    match avoid j (shift i k) with
    | Some k' => Var k'
    | None => U
    end).

Lemma subst_weaken_master {n} (T U : Term n) (i j : Fin (S n)) :
  subst (weaken T i) j U = sw T U i j.
Proof.
  unfold subst.
  rewrite var_map_weaken. auto.
Qed.

Definition gap n : Type := Fin (S n).

Definition shiftg {n} : gap n -> Fin n -> Fin (S n) := shift.

Fixpoint avoidg {n} : Fin (S n) -> gap (S n) -> gap n.
  destruct n.
  - exact (fun _ _ => inl tt).
  - intros i g.
    destruct i.
    + exact (match g with
           | inl _ => inl tt
           | inr g' => g'
            end).
    + destruct g.
      * exact (inl tt).
      * exact (inr (avoidg _ f f0)).
Defined.

Lemma shift_val {n} (g : Fin (S n)) (i : Fin n) :
  nat_of_Fin (shift g i) =
  if Nat.leb (nat_of_Fin g) (nat_of_Fin i) then S (nat_of_Fin i) else
  nat_of_Fin i.
Proof.
  induction n.
  - destruct i.
  - simpl.
    destruct g.
    + destruct i; auto.
    + destruct i; auto.
      specialize (IHn f f0).
      simpl in *.
      destruct (shift f f0).
      * destruct f; simpl in *.
        -- congruence.
        -- destruct (nat_of_Fin f0); auto.
           destruct Nat.leb; auto.
      * destruct f; simpl in *; auto.
        destruct (nat_of_Fin f0); auto.
        destruct Nat.leb; auto.
Qed.

Lemma avoidg_val {n} (i : Fin (S n)) (g : gap (S n)) :
  nat_of_Fin (avoidg i g) =
  if Nat.leb (nat_of_Fin g) (nat_of_Fin i) then nat_of_Fin g else pred (nat_of_Fin g).
Proof.
  induction n.
  - simpl.
    destruct g; auto.
    simpl. destruct i.
    + destruct f; auto.
      destruct f.
    + destruct f0.
  - simpl.
    destruct i.
    + destruct g; auto.
    + destruct g; auto.
      specialize (IHn f f0).
      destruct (avoidg f f0); simpl in *.
      * destruct f0; simpl in *; auto.
        destruct f; simpl in *.
        -- now rewrite <- IHn.
        -- destruct s.
           ++ inversion IHn.
           ++ destruct Nat.leb; auto.
      * destruct f0; simpl in *.
        -- congruence.
        -- destruct f.
           ++ rewrite <- IHn. auto.
           ++ destruct s.
              ** simpl in *; congruence.
              ** simpl in *.
                 destruct (nat_of_Fin f); auto. 
                 rewrite IHn.
                 destruct Nat.leb; auto.
Qed.

Lemma avoid_inl {n} (i : Fin n) :
  avoid (inl tt) (inr i) = Some i.
Proof.
  destruct n.
  - destruct i.
  - auto.
Qed.

Lemma avoid_inr_inl {n} (i : Fin (S n)) :
  @avoid (S n) (inr i) (inl tt) = Some (inl tt).
Proof.
  auto.
Qed.

Lemma avoid_shift_shift {n} (i : Fin (S (S n))) (j j' : Fin (S n)) :
  avoid (shift i j) (shift i j') =
  option_map (shift (avoidg j i)) (avoid j j').
Proof.
  induction n.
  - simpl.
    destruct i; auto.
    destruct j.
    + destruct j'; auto.
      destruct f0.
    + destruct f0.
  - simpl.
    destruct i.
    + destruct j.
      * destruct j'; auto.
      * destruct j'; auto.
    + destruct j.
      * destruct j'; auto.
      * destruct j'; auto.
        specialize (IHn f f0 f1).
        simpl in *.
        destruct f.
        -- destruct (avoid f0 f1).
           ++ simpl in *; congruence.
           ++ auto.
        -- destruct f0.
           ++ destruct f1; auto.
              ** destruct u, u0.
                 rewrite avoid_refl; auto.
              ** destruct u. rewrite avoid_inl; simpl.
                 rewrite avoid_inl in IHn.
                 simpl in IHn.
                 congruence.
           ++ destruct f1.
              ** simpl.
                 destruct u.
                 destruct n.
                 --- destruct f.
                 --- rewrite (@avoid_inr_inl) in *.
                     simpl. auto.
              ** simpl. rewrite IHn.
                 simpl. destruct (avoid (inr f) (inr f0)).
                 --- simpl. auto.
                 --- auto.
Qed.

Lemma subst_weaken_weaken {n} (T : Term (S n)) (U : Term n) i i' j j' :
  avoid j i = Some i' ->
  avoid i j = Some j' ->
  subst (weaken T i) j (weaken U i') =
  weaken (subst T j' U) i'.
Proof.
  intros.
  unfold subst.
  rewrite var_map_weaken.
  rewrite weak_var_map.
  apply var_map_ext.
  apply avoid_shift_inv in H, H0.
  rewrite <- H0.
  intro.
  rewrite avoid_shift_shift.
  destruct (avoid j' i0) eqn:?; auto.
  simpl; f_equal.
  f_equal.
  apply Fin_ext.
  rewrite avoidg_val.
  apply (f_equal nat_of_Fin) in H, H0.
  rewrite shift_val in H, H0.
  destruct (Nat.leb (nat_of_Fin i) (nat_of_Fin j')) eqn:?.
  - rewrite <- H.
    destruct (Nat.leb (nat_of_Fin j)) eqn:?.
    + rewrite <- H0 in Heqb0.
      rewrite PeanoNat.Nat.leb_le in *.
      lia.
    + auto.
  - rewrite H0 in *.
    destruct (Nat.leb (nat_of_Fin j) _) eqn:?.
    + rewrite <- H; auto.
    + rewrite PeanoNat.Nat.leb_gt in *. lia.
Qed.

Ltac subst_simpl_once :=
  match goal with
  | [ |- context [ var ] ] => unfold var
  | [ |- context [ subst (Var ?i) ?j ?u ] ] => rewrite @subst_Var
  | [ |- context [ subst (?t1 # ?t2) ?i ?u ] ] => rewrite @subst_App
  | [ |- context [ subst (Lam ?t) ] ] => rewrite @subst_Lam
  | [ |- context [ subst (weaken ?M ?i) ?i ?N ] ] => rewrite @subst_weaken
  | [ |- context [subst (weaken ?T ?i) ?j (weaken ?U ?i')] ] =>
    erewrite @subst_weaken_weaken; [ | reflexivity | reflexivity ]
  | [ |- context [avoid ?x ?x] ] => rewrite avoid_refl
  | [ |- context [avoid _ _] ] => simpl avoid; cbv iota
  end.

Ltac subst_simpl := repeat subst_simpl_once.

Ltac beta :=
  match goal with
  | [ |- red (Lam _ # _) _ ] =>
    apply beta_red;
    simpl
  | [ |- red (Lam _) _ ] =>
    apply lam_red;
    beta
  | [ |- red (_ # _) _ ] =>
    first
    [ apply app_red_l; beta
    | apply app_red_r; beta
    ]
  | _ => fail
  end.

Ltac normal_order :=
  match goal with
  | [ |- reds _ _ ] => unfold reds; normal_order
  | [ |- star red _ _ ] => apply star_refl
  | [ |- context [ avoid ?t ?t ] ] =>
      rewrite avoid_refl; normal_order
  | [ |- star red _ _ ] =>
      eapply R_star;
      [ beta
      | simpl;
        repeat rewrite subst_const;
        repeat rewrite weaken_const;
        repeat rewrite subst_weaken
      ]; normal_order
  | _ => idtac
  end.

Ltac normal_order2 :=
  match goal with
  | [ |- reds _ _ ] => unfold reds; normal_order2
  | [ |- star red _ _ ] => apply star_refl
  | [ |- context [ avoid ?t ?t ] ] =>
      rewrite avoid_refl; normal_order2
  | [ |- star red _ _ ] =>
      eapply R_star;
      [ beta
      | simpl;
        subst_simpl;
        repeat rewrite subst_const
      ]; normal_order2
  | _ => idtac
  end.
