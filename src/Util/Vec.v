Require Import LC.Util.Fin.

Fixpoint Vec X n : Type :=
  match n with
  | 0 => unit
  | S m => X * Vec X m
  end.

Fixpoint vmap {X Y} {n} (f : X -> Y) : Vec X n -> Vec Y n :=
  match n with
  | 0 => fun _ => tt
  | S m => fun '(x, xs) => (f x, vmap f xs)
  end.

Fixpoint vlookup {X} {n} : Fin n -> Vec X n -> X :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i v =>
    match i with
    | inl _ => fst v
    | inr j => vlookup j (snd v)
    end
  end.

Lemma vlookup_vmap {X Y} {n} (f : X -> Y) (v : Vec X n) (i : Fin n) :
  vlookup i (vmap f v) = f (vlookup i v).
Proof.
  induction n.
  - destruct i.
  - destruct i; destruct v; simpl.
    + reflexivity.
    + now rewrite IHn.
Qed.

Fixpoint Fins n : Vec (Fin n) n :=
  match n with
  | 0 => tt
  | S m => (inl tt, vmap inr (Fins m))
  end.

Lemma vlookup_Fins {n} : forall i : Fin n,
  vlookup i (Fins n) = i.
Proof.
  induction n; intro i.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + simpl.
      rewrite vlookup_vmap.
      now rewrite IHn.
Qed.
