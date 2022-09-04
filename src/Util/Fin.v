Fixpoint Fin n : Type :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Fixpoint nat_of_Fin {n} : Fin n -> nat :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ => 0
    | inr j => S (nat_of_Fin j)
    end
  end.

(* TODO: change option to have better names*)
Fixpoint avoid {n} : Fin (S n) -> Fin (S n) ->
  option (Fin n) :=
  match n with
  | 0 => fun _ _ => None
  | S m => fun i j  =>
    match i with
    | inl _ =>
      match j with
      | inl _ => None
      | inr j' => Some j'
      end
    | inr i' =>
      match j with
      | inl _ => Some (inl tt)
      | inr j' =>
        match avoid i' j' with
        | Some k => Some (inr k)
        | None => None
        end
      end
    end
  end.

Lemma avoid_refl : forall n (i : Fin (S n)),
  avoid i i = None.
Proof.
  induction n; intro.
  - reflexivity.
  - destruct i.
    + reflexivity.
    + simpl.
      rewrite IHn.
      reflexivity.
Qed.

Fixpoint shift {n} : Fin (S n) -> Fin n -> Fin (S n) :=
  match n with
  | 0 => fun _ e =>
    match e with
    end
  | S m => fun k i =>
    match k with
    | inl _ => inr i
    | inr k' =>
      match i with
      | inl _ => inl tt
      | inr i' => inr (shift k' i')
      end
    end
  end.

Lemma avoid_shift {n} (i : Fin (S n))
  (j : Fin n) : avoid i (shift i j) = Some j.
Proof.
  induction n.
  - destruct j.
  - simpl.
    destruct i.
    + reflexivity.
    + destruct j.
      * destruct u; reflexivity.
      * now rewrite IHn.
Qed.

Fixpoint Fin_of_nat {m} (n : nat) : Fin (n + S m) :=
  match n with
  | 0 => inl tt
  | S k => inr (Fin_of_nat k)
  end.
