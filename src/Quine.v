Require Import LC.Util.Fin.
Require Import LC.Util.Vec.
Require Import LC.Util.Star.
Require Import LC.LC.
Require Import LC.CNum.
Require Import LC.Bool.
Require Import LC.Tuple.
Require Import LC.Combinators.
Require Import LC.Interpreter.

(* fun t1 t2 v a l => a (t1 v a l) (t2 v a l) *)

Definition A {m} : Term m :=
  Lam (Lam (Lam (Lam (Lam (
    var 1 # (var 4 # var 2 # var 1 # var 0) # (var 3 # var 2 # var 1 # var 0)
  ))))).

Global Instance A_const : Const (@A).
Proof.
  constructor.
  intros; reflexivity.
Qed.

Lemma app_reds {n} (T1 T2 U1 U2 : Term n) :
  reds T1 T2 ->
  reds U1 U2 ->
  reds (T1 # U1) (T2 # U2).
Proof.
  intros.
  eapply star_trans.
  - apply app_reds_l; eauto.
  - apply app_reds_r; auto.
Qed.

Lemma quote_with_vars {m n} (T : Term n) :
  reds (quote T # var 2 # var 1 # var 0) ((@quote_aux m n T)).
Proof.
  unfold quote; simpl.
  normal_order2.
  induction T.
  - simpl. subst_simpl.
    repeat rewrite subst_const.
    normal_order.
  - simpl. subst_simpl.
    apply app_reds.
    + apply app_reds_r.
      auto.
    + auto.
  - simpl. subst_simpl.
    apply app_reds_r.
    auto.
Qed.

Lemma A_reds {m n} (T1 T2 : Term n) :
  reds ((A : Term m) # quote T1 # quote T2) (quote (T1 # T2)).
Proof.
  unfold A.
  eapply R_star; [beta|].
  subst_simpl.
  repeat rewrite weaken_quote.
  eapply R_star; [beta|].
  subst_simpl.
  repeat rewrite weaken_quote.
  repeat rewrite subst_quote.
  unfold quote at 3.
  do 3 apply lam_reds.
  simpl quote_aux.
  eapply app_reds.
  - apply app_reds_r.
    apply quote_with_vars.
  - apply quote_with_vars.
Qed.

Fixpoint quote_with_terms {m n} (t : Term n) (V A L : Term m) : Term m :=
  match t with
  | Var i => V # (cnum (nat_of_Fin i))
  | t1 # t2 => A # quote_with_terms t1 V A L # quote_with_terms t2 V A L
  | Lam t' => L # quote_with_terms t' V A L
  end.

Lemma quote_aux_quote_with_terms {m n} (t : Term n) :
  (quote_aux t : Term (S (S (S m)))) =
  quote_with_terms t (var 2) (var 1) (var 0).
Proof.
  induction t.
  - simpl. auto.
  - simpl. rewrite IHt1, IHt2. auto.
  - simpl. rewrite IHt. auto.
Qed.

Lemma quote_with_terms_subst {m n} (t : Term n) (V A L : Term (S m))
  (i : Fin (S m)) (U : Term m) :
  subst (quote_with_terms t V A L) i U =
  quote_with_terms t (subst V i U) (subst A i U) (subst L i U).
Proof.
  induction t.
  - simpl; subst_simpl.
    now rewrite subst_const.
  - simpl; subst_simpl.
    congruence.
  - simpl; subst_simpl.
    congruence.
Qed.

Definition NQhat {m} : Term m :=
  Lam (Lam (Lam (Lam
    (var 0 # (var 2 # (var 3 # cnum 1)) # (var 3 # cnum 0))))).

Global Instance NQhat_const : Const (@NQhat).
Proof.
  constructor; intros; reflexivity.
Qed.

Definition NQ {m} : Term m :=
  Lam (Lam (Lam (Lam
    (var 1 # (var 1 # (NQhat # var 3  # var 2 # var 1 # var 0)))))).

Global Instance NQ_const : Const (@NQ).
Proof.
  constructor; intros; reflexivity.
Qed.

Lemma NQ_correct {m} (A B C : Term m) n :
  reds (NQ # A # B # C # (cnum n)) (quote_with_terms (cnum n : Term m) A B C).
Proof.
  unfold NQ.
  normal_order2.
  do 2 apply app_reds_r.
  unfold NQhat.
  normal_order2.
  eapply star_trans; [apply cnum_reds|].
  induction n.
  - apply star_refl.
  - simpl; apply app_reds_r.
    auto.
Qed.

Definition VQ {m} : Term m :=
  Lam (Lam (Lam (Lam (var 2 # (var 3 # cnum 2) # (NQ # var 3 # var 2 # var 1 # var 0))))).

Global Instance VQ_const : Const (@VQ).
Proof.
  constructor; intros; reflexivity.
Qed.

Definition AQ {m} : Term m :=
  Lam (Lam (Lam (Lam (var 2 # (var 2 # (var 3 # cnum 1) # var 0))))).

Global Instance AQ_const : Const (@AQ).
Proof.
  constructor; intros; reflexivity.
Qed.

Definition LQ {m} : Term m :=
  Lam (Lam (Lam (var 1 # (var 2 # cnum 0)))).

Global Instance LQ_const : Const (@LQ).
Proof.
  constructor; intros; reflexivity.
Qed.

Definition Qhat {m} : Term m :=
  Lam (Lam (Lam (Lam
    (var 3 #
      (VQ # var 2 # var 1 # var 0) #
      (AQ # var 2 # var 1 # var 0) #
      (LQ # var 2 # var 1 # var 0))))).

Global Instance Qhat_const : Const (@Qhat).
Proof.
  constructor; intros; reflexivity.
Qed.

Definition Q {m} : Term m :=
  Lam (Lam (Lam (Lam
    (var 0 # (var 0 # (var 0 # (Qhat # var 3 # var 2 # var 1 # var 0))))))).

Global Instance QQ_const : Const (@Q).
Proof.
  constructor; intros; reflexivity.
Qed.

Lemma quote_aux_app {m n} (T1 T2 : Term n) :
  (quote_aux (T1 # T2) : Term (S (S (S m)))) =
  var 1 # quote_aux T1 # quote_aux T2.
Proof.
  auto.
Qed.

Lemma quote_aux_lam {m n} (T : Term (S n)) :
  (quote_aux (Lam T) : Term (S (S (S m)))) =
  var 0 # quote_aux T.
Proof.
  auto.
Qed.

Lemma quote_var {m} {n} (i : Fin n) :
  (quote (Var i) : Term m) = Lam (Lam (Lam (var 2 # (cnum (nat_of_Fin i))))).
Proof.
  auto.
Qed.

Lemma weaken_Var {n} (i : Fin n) (j : Fin (S n)) :
  weaken (Var i) j = Var (shift j i).
Proof.
  auto.
Qed.

Lemma weaken_App {n} (T1 T2 : Term n) (j : Fin (S n)) :
  weaken (T1 # T2) j = weaken T1 j # weaken T2 j.
Proof.
  auto.
Qed.

Lemma weaken_Lam {n} (T : Term (S n)) (j : Fin (S n)) :
  weaken (Lam T) j = Lam (weaken T (inr j)).
Proof.
  auto.
Qed.

(*
Lemma Qhat_reds {m n} (T : Term n) :
  reds  T T.
*)

Lemma Q_reds {m n} (T : Term n) :
  reds ((Q : Term m) # quote T) (quote (quote T : Term m)).
Proof.
  unfold Q.
  eapply R_star; [beta|].
  subst_simpl.
  do 3 apply lam_reds.
  simpl quote_aux at 1.
  do 3 apply app_reds_r.
  repeat rewrite weaken_quote.
  rewrite subst_const.
  unfold Qhat.
  eapply R_star; [beta|].
  subst_simpl.
  repeat rewrite weaken_quote.
  repeat rewrite subst_const.
  eapply R_star; [beta|].
  subst_simpl.
  repeat rewrite subst_quote.
  repeat rewrite subst_const.
  simpl weaken.
  eapply R_star; [beta|].
  subst_simpl.
  repeat rewrite subst_quote.
  repeat rewrite subst_const.
  simpl weaken.
  eapply R_star; [beta|].
  subst_simpl.
  repeat rewrite subst_quote.
  repeat rewrite subst_const.
  unfold quote.
  eapply R_star; [beta|].
  subst_simpl.
  repeat rewrite weaken_app.
  repeat rewrite weaken_const.
  simpl weaken.
  eapply R_star; [beta|].
  subst_simpl.
  repeat rewrite weaken_app.
  repeat rewrite weaken_const.
  simpl weaken.
  eapply R_star; [beta|].
  rewrite quote_aux_quote_with_terms.
  unfold var.
  rewrite @quote_with_terms_subst.
  subst_simpl.
  rewrite @quote_with_terms_subst.
  subst_simpl.
  rewrite @quote_with_terms_subst.
  subst_simpl.
  repeat rewrite subst_const.
  induction T.
  - simpl.
    unfold VQ.
    normal_order2.
    apply app_reds_r.
    eapply star_trans; [apply NQ_correct|].
    unfold cnum; simpl.
    rewrite quote_aux_quote_with_terms.
    normal_order.
  - simpl.
    unfold AQ.
    normal_order2.
    apply app_reds; auto.
    do 2 apply app_reds_r.
    auto.
  - simpl.
    unfold LQ.
    normal_order2.
    apply app_reds; auto.
    apply star_refl.
Qed.

Definition pre_KFP {m} (P : Term m) : Term m.
Proof.
  apply Lam.
  apply App.
  - exact (weaken P (inl tt)).
  - apply App.
    + apply App.
      * exact A.
      * exact (var 0).
    + apply App.
      * exact Q.
      * exact (var 0).
Defined.

Definition KFP {m} (P : Term m) : Term m :=
  (pre_KFP P) # quote (pre_KFP P).

Theorem Kleene_Recursion_Thm {m} (P : Term m) :
  reds (KFP P) (P # quote (KFP P)).
Proof.
  pose (QP := pre_KFP P).
  unfold KFP at 1.
  unfold pre_KFP at 1.
  fold QP.
  apply star_trans with (y := P # (A # quote QP # (Q # quote QP))).
  - normal_order2.
  - apply app_reds_r.
    eapply star_trans with (y := A # quote QP # (quote (quote QP))).
    + apply app_reds_r.
      apply Q_reds.
    + apply A_reds.
Qed.

Definition I_comb {n} : Term n :=
  Lam (var 0).

Lemma I_reds {n} (T : Term n) :
  reds (I_comb # T) T.
Proof.
  unfold I_comb.
  normal_order2.
Qed.

Definition Quine : Term 0 :=
  KFP I_comb.

Theorem Quine_correct :
  reds Quine (quote Quine).
Proof.
  eapply star_trans.
  - apply Kleene_Recursion_Thm.
  - apply I_reds.
Qed.

Set Printing Depth 1000000.
Require Import String.

Eval vm_compute in Quine.
Eval vm_compute in print_term Quine.
