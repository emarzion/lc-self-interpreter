Inductive star {X} (R : X -> X -> Prop) : X -> X -> Prop :=
  | star_refl : forall x, star R x x
  | R_star : forall x y z, R x y -> star R y z -> star R x z.

Lemma star_trans {X} (R : X -> X -> Prop) :
  forall x y z, star R x y -> star R y z ->
  star R x z.
Proof.
  intros x y z Hxy Hyz.
  induction Hxy.
  - exact Hyz.
  - eapply R_star.
    + exact H.
    + apply IHHxy.
      exact Hyz.
Qed.
