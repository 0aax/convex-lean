import Mathlib

def klee_chebyshev_set_conjecture : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H),
    C.Nonempty →
    (∀ x : H, ∃! c : H, c ∈ C ∧ ∀ y ∈ C, dist x c ≤ dist x y) →
    Convex ℝ C
