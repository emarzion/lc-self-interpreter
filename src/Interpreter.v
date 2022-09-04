Require Import LC.Util.Fin.
Require Import LC.Util.Vec.
Require Import LC.Util.Star.
Require Import LC.LC.
Require Import LC.CNum.
Require Import LC.Bool.
Require Import LC.Tuple.
Require Import LC.Combinators.

Record Interpretation : Type := {
  q : Term 0 -> Term 0;
  q_normal : forall t, normal (q t);
  E : Term 0;
  E_q : forall t, reds (E # q t) t
  }.

Fixpoint quote_aux {m n} (t : Term n) : Term (S (S (S m))) :=
  match t with
  | Var i => var 2 # cnum (nat_of_Fin i)
  | App t1 t2 => var 1 # quote_aux t1 # quote_aux t2
  | Lam t' => var 0 # quote_aux t'
  end.

Lemma quote_aux_normal {m n} (t : Term n) :
  normal (@quote_aux m n t).
Proof.
  induction t.
  - simpl; repeat split.
    apply cnum_aux_normal.
  - simpl; repeat split; auto.
  - simpl; repeat split; auto.
Qed.

Definition quote {m n} (t : Term n) : Term m :=
  Lam (Lam (Lam (quote_aux t))).

Lemma quote_normal {m n} (t : Term n) :
  normal (@quote m n t).
Proof.
  apply quote_aux_normal.
Qed.

Definition EVAL_WITHOUT_ENV {n} : Term n :=
  Lam (var 0 # LOOKUP # S_COMB # FLIP_CURRY).

#[export]
Instance EVAL_WITHOUT_ENV_Const : Const (@NIL).
Proof.
  constructor; reflexivity.
Qed.

Definition tri_subst {n} (T : Term n) {m} : Term m :=
subst
     (subst
        (subst (quote_aux T)
           (inr (inr (inl tt))) LOOKUP)
        (inr (inl tt)) S_COMB) 
     (inl tt) FLIP_CURRY.

Opaque cnum.

#[export]
Instance tri_subst_Const {n} (T : Term n) :
  Const (@tri_subst n T).
Proof.
  constructor.
  intros m i.
  unfold tri_subst.
  induction T.
  - simpl.
    rewrite avoid_refl.
    repeat rewrite subst_const.
    now repeat rewrite weaken_const.
  - simpl.
    rewrite avoid_refl.
    repeat rewrite subst_const.
    repeat rewrite weaken_const.
    now rewrite IHT1, IHT2.
  - simpl.
    rewrite avoid_refl.
    repeat rewrite weaken_const.
    now rewrite IHT.
Qed.

Lemma weaken_tup {n m} (ts : Vec (Term n) m) i :
  weaken (tup ts) i = tup (vmap (fun t => weaken t i) ts).
Proof.
  induction m.
  { reflexivity. }
  { destruct ts; simpl.
    rewrite IHm.
    reflexivity.
  }
Qed.

Lemma weaken_Var_Var_inr {n m} (is : Vec (Fin n) m) :
  vmap (fun t => weaken t (inl tt)) (vmap Var is) =
  vmap (@Var (S n)) (vmap inr is).
Proof.
  induction m.
  { reflexivity. }
  { destruct is; simpl.
    f_equal.
    { destruct n;
      [destruct f| reflexivity].
    }
    now rewrite IHm.
  }
Qed.

Lemma LOOKUP_0_reds {n} (T : Term n) :
  reds (LOOKUP # cnum 0 # T) (FST # T).
Proof.
  Transparent cnum.
  Opaque FST.
  unfold cnum; simpl.
  unfold LOOKUP.
  eapply R_star.
  { apply app_red_l.
    apply beta_red.
  }
  simpl.
  rewrite avoid_refl.
  eapply R_star.
  { do 2 apply app_red_l.
    apply beta_red.
  }
  simpl.
  eapply R_star.
  { apply app_red_l.
    apply beta_red.
  }
  simpl.
  rewrite avoid_refl.
  rewrite subst_const.
  apply star_refl.
  Transparent FST.
  Opaque cnum.
Qed.

Lemma LOOKUP_reds {n m} (ts : Vec (Term n) m) (i : Fin m) :
  reds (LOOKUP # cnum (nat_of_Fin i) # tup ts) (vlookup i ts).
Proof.
  unfold LOOKUP.
  Opaque FST.
  Opaque SND.
  eapply R_star.
  { apply app_red_l.
    apply beta_red.
  }
  simpl.
  rewrite avoid_refl.
  repeat rewrite subst_const.
  Transparent cnum.
  unfold cnum.
  eapply R_star.
  { do 2 apply app_red_l.
    apply beta_red.
  }
  simpl.
  repeat rewrite weaken_const.
  eapply R_star.
  { apply app_red_l. apply beta_red. }
  simpl.
  induction m.
  { destruct i. }
  { destruct i; destruct ts; simpl.
    { rewrite avoid_refl.
      apply FST_PAIR.
    }
    { rewrite avoid_refl.
      simpl.
      repeat rewrite subst_const.
      eapply R_star.
      { eapply app_red_l.
        apply beta_red.
      }
      simpl.
      rewrite avoid_refl.
      repeat rewrite subst_const.
      eapply R_star.
      { eapply beta_red. }
      simpl.
      rewrite subst_weaken.
      rewrite avoid_refl.
      repeat rewrite subst_const.
      eapply star_trans.
      { eapply app_reds_r.
        apply SND_PAIR.
      }
      apply IHm.
    }
  }
  Opaque cnum.
  Transparent FST.
  Transparent SND.
Qed.

Lemma tri_subst_reds {n} (T : Term n) :
  reds (tri_subst T # Vars n) T.
Proof.
  induction T.
  { unfold tri_subst; simpl.
    rewrite avoid_refl.
    repeat rewrite subst_const.
    rewrite <- vlookup_Fins at 2.
    rewrite <- vlookup_vmap.
    apply LOOKUP_reds.
  }
  { unfold tri_subst; simpl.
    rewrite avoid_refl.
    repeat rewrite subst_const.
    eapply star_trans.
    { apply S_COMB_reds. }
    eapply star_trans.
    { apply app_reds_l.
      exact IHT1.
    }
    { apply app_reds_r.
      exact IHT2.
    }
  }
  { unfold tri_subst; simpl.
    rewrite avoid_refl.
    eapply star_trans.
    { apply FLIP_CURRY_reds. }
    apply lam_reds.
    assert
      (PAIR # var 0 # weaken (Vars n) (inl tt) = Vars (S n)).
    { unfold Vars.
      simpl.
      f_equal.
      rewrite weaken_tup.
      now rewrite weaken_Var_Var_inr.
    }
    rewrite H.
    clear H.
    epose (weaken_const) as Hwc.
    unfold tri_subst in Hwc.
    rewrite Hwc.
    exact IHT.
  }
Qed.

Lemma EVAL_WITHOUT_ENV_quote_Vars {n} (T : Term n) :
  reds (EVAL_WITHOUT_ENV # quote T # Vars n) T.
Proof.
  eapply R_star.
  { apply app_red_l.
    apply beta_red.
  }
  simpl.
  rewrite avoid_refl.
  repeat rewrite subst_const.
  unfold quote.
  eapply R_star.
  { do 3 apply app_red_l.
    apply beta_red.
  }
  simpl.
  eapply R_star.
  { do 2 apply app_red_l.
    apply beta_red.
  }
  simpl.
  repeat rewrite weaken_const.
  eapply R_star.
  { apply app_red_l.
    apply beta_red.
  }
  apply tri_subst_reds.
Qed.

Definition EVAL : Term 0 :=
  Lam (EVAL_WITHOUT_ENV # var 0 # NIL).

Theorem EVAL_quote : forall (T : Term 0),
  reds (EVAL # quote T) T.
Proof.
  intro T.
  eapply R_star.
  { apply beta_red. }
  simpl.
  simpl.
  repeat rewrite subst_const.
  exact (EVAL_WITHOUT_ENV_quote_Vars T).
Qed.

Definition EVAL_Interpreter : Interpretation := {|
  q := quote;
  q_normal := quote_normal;
  E := EVAL;
  E_q := EVAL_quote
  |}.
