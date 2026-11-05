import Mathlib

noncomputable def supportFun
  {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun y => inner ℝ x y) '' K)

def plank {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (a b : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | a ≤ inner ℝ u x ∧ inner ℝ u x ≤ b}

noncomputable def width {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  supportFun K u + supportFun K (-u)

def bang_affine_plank : Prop :=
  ∀ (m n : ℕ),
    (n > 0) →
    ∀ (K : Set (EuclideanSpace ℝ (Fin n))),
      ((interior K).Nonempty) →
      (Convex ℝ K) →
      (IsCompact K) →
      ∀ (u : Fin m → EuclideanSpace ℝ (Fin n)) (a b : Fin m → ℝ),
        (∀ i : Fin m, ‖u i‖ = 1) →
        (∀ i : Fin m, a i ≤ b i) →
        (K ⊆ ⋃ i : Fin m, plank (u i) (a i) (b i)) →
        ∑ i : Fin m, (b i - a i) / (width K (u i)) ≥ 1

theorem bang_affine_plank_POS : bang_affine_plank := by
  sorry

theorem bang_affine_plank_NEG : ¬ bang_affine_plank := by
  sorry
