import Mathlib

def reflexive_fixed_point : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (C : Set X) (T : C → C),
    (Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)) →
    (Set.Nonempty C) →
    (IsClosed C) →
    (Bornology.IsBounded C) →
    (Convex ℝ C) →
      (∀ (x y : C),
      ‖(T x : X) - (T y : X)‖ ≤ ‖(x : X) - (y : X)‖) →
        (∃ (z : C), Function.IsFixedPt T z)
