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
Instance EVAL_WITHOUT_ENV_Const : Const (@EVAL_WITHOUT_ENV).
Proof.
  constructor; reflexivity.
Qed.

Lemma quote_aux_var {m n} (i : Fin n) :
  (quote_aux (Var i) : Term (S (S (S m)))) = var 2 # cnum (nat_of_Fin i).
Proof.
  auto.
Qed.

Lemma weaken_app {n} (T1 T2 : Term n) (i : Fin (S n)) :
  weaken (T1 # T2) i = weaken T1 i # weaken T2 i.
Proof.
  auto.
Qed.

#[export]
Instance quote_Const {n} (T : Term n) : Const (fun m => @quote m n T).
Proof.
  constructor.
  intros m i.
  unfold quote; simpl.
  repeat f_equal.
  generalize i; clear i.
  induction T; intro i.
  - repeat rewrite quote_aux_var.
    rewrite weaken_app.
    rewrite weaken_const; auto.
  - simpl quote_aux.
    repeat rewrite weaken_app.
    rewrite IHT1, IHT2.
    auto.
  - simpl quote_aux.
    rewrite weaken_app.
    rewrite IHT.
    auto.
Qed.

Lemma weaken_quote {m n} (T : Term n) (i : Fin (S m)) :
  weaken (quote T) i = quote T.
Proof.
  destruct (quote_Const T).
  apply weaken_const.
Qed.

Lemma subst_quote {m n} (T : Term n) (U : Term m) (i : Fin (S m)) :
  subst (quote T) i U = quote T.
Proof.
  apply (@subst_const _ (quote_Const T)).
Qed.

Definition tri_subst {n} (T : Term n) {m} : Term m :=
subst
     (subst
        (subst (quote_aux T)
           (inr (inr (inl tt))) LOOKUP)
        (inr (inl tt)) S_COMB) 
     (inl tt) FLIP_CURRY.

Lemma tri_subst_app {n} (T1 T2 : Term n) {m} :
  (tri_subst (T1 # T2) : Term m) = S_COMB # tri_subst T1 # tri_subst T2.
Proof.
  unfold tri_subst.
  simpl quote_aux.
  subst_simpl.
  rewrite subst_const.
  auto.
Qed.

Lemma tri_subst_var {n} (i : Fin n) {m} :
  (tri_subst (Var i) : Term m) = LOOKUP # cnum (nat_of_Fin i).
Proof.
  unfold tri_subst.
  simpl quote_aux.
  subst_simpl.
  repeat rewrite subst_const.
  auto.
Qed.

Check Lam.

Lemma tri_subst_lam {n} (T : Term (S n)) {m} :
  (tri_subst (Lam T) : Term m) = FLIP_CURRY # tri_subst T.
Proof.
  unfold tri_subst.
  simpl quote_aux.
  subst_simpl.
  auto.
Qed.

Opaque cnum.

#[export]
Instance tri_subst_Const {n} (T : Term n) :
  Const (@tri_subst n T).
Proof.
  constructor.
  intros m i.
  induction T.
  - repeat rewrite tri_subst_var.
    rewrite weaken_app.
    repeat rewrite weaken_const.
    auto.
  - repeat rewrite tri_subst_app.
    repeat rewrite weaken_app.
    rewrite weaken_const.
    congruence.
  - repeat rewrite tri_subst_lam.
    rewrite weaken_app.
    rewrite weaken_const.
    congruence.
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

Lemma LOOKUP_reds {n m} (ts : Vec (Term n) m) (i : Fin m) :
  reds (LOOKUP # cnum (nat_of_Fin i) # tup ts) (vlookup i ts).
Proof.
  unfold LOOKUP.
  Opaque FST.
  Opaque SND.
  normal_order.
  subst_simpl.
  eapply star_trans.
  { apply app_reds_l.
    apply cnum_reds.
  }
  induction m.
  { destruct i. }
  { destruct i; destruct ts; simpl.
    { rewrite subst_const.
      apply FST_PAIR. }
    { normal_order.
      subst_simpl.
      normal_order.
      subst_simpl.
      eapply star_trans.
      { apply app_reds_r.
        rewrite subst_const.
        apply SND_PAIR.
      }
      specialize (IHm v f).
      rewrite subst_const in IHm.
      auto.
    }
  }
Qed.

Lemma tri_subst_reds {n} (T : Term n) :
  reds (tri_subst T # Vars n) T.
Proof.
  induction T.
  { rewrite tri_subst_var.
    rewrite <- vlookup_Fins at 2.
    rewrite <- vlookup_vmap.
    apply LOOKUP_reds.
  }
  { rewrite tri_subst_app.
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
  { rewrite tri_subst_lam.
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
    rewrite weaken_const.
    exact IHT.
  }
Qed.

Lemma EVAL_WITHOUT_ENV_quote_Vars {n} (T : Term n) :
  reds (EVAL_WITHOUT_ENV # quote T # Vars n) T.
Proof.
  unfold EVAL_WITHOUT_ENV.
  unfold quote.
  normal_order.
  subst_simpl.
  repeat rewrite subst_const.
  normal_order.
  subst_simpl.
  normal_order.
  subst_simpl.
  normal_order.
  apply tri_subst_reds.
Qed.

Opaque EVAL_WITHOUT_ENV.

Definition EVAL : Term 0 :=
  Lam (EVAL_WITHOUT_ENV # var 0 # NIL).

Print EVAL.
Eval vm_compute in EVAL.

Theorem EVAL_quote : forall (T : Term 0),
  reds (EVAL # quote T) T.
Proof.
  intro T.
  unfold EVAL.
  Opaque NIL.
  normal_order.
  exact (EVAL_WITHOUT_ENV_quote_Vars T).
Qed.

Definition EVAL_Interpreter : Interpretation := {|
  q := quote;
  q_normal := quote_normal;
  E := EVAL;
  E_q := EVAL_quote
  |}.

Require Import String.

From Coq Require Import Numbers.DecimalString Numbers.DecimalNat.

Definition nat_to_string (n : nat) : string :=
  NilZero.string_of_uint (Decimal.rev (Unsigned.to_lu n)).

Fixpoint print_term {n} (T : Term n) : string :=
  match T with
  | Var i => nat_to_string (nat_of_Fin i)
  | T1 # T2 => "(" ++ print_term T1 ++ " " ++ print_term T2 ++ ")"
  | Lam T' => "(λ" ++ print_term T' ++ ")"
  end.
