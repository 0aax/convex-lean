import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def convexNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : E) (C : Set E) : Set E :=
  {s : E | ∀ y ∈ C, inner ℝ s (y - x) ≤ 0}

def setAdd {E : Type*} [NormedAddCommGroup E]
    (C : Set E) (K : Set E)
    : Set E
    := {v : E | ∃ c ∈ C, ∃ k ∈ K, v = c + k}

theorem CAMA_chap_3_5_3_1
  (x : E)
  (C₁ : Set E)
  (C₂ : Set E)
  (hC₁₀ : Set.Nonempty C₁)
  (hC₁₁ : IsClosed C₁)
  (hC₁₂ : Convex ℝ C₁)
  (hC₂₀ : Set.Nonempty C₂)
  (hC₂₁ : IsClosed C₂)
  (hC₂₂ : Convex ℝ C₂) :
  (x ∈ C₁ ∩ C₂ → posTangentConeAt (C₁ ∩ C₂) x ⊆ posTangentConeAt C₁ x ∩ posTangentConeAt C₂ x ∧
    convexNormalCone x (C₁ ∩ C₂) ⊇ setAdd (convexNormalCone x C₁) (convexNormalCone x C₂)) ∧
  (∀ (D : Set F), Set.Nonempty D → IsClosed D → Convex ℝ D →
    ∀ (x₁ : E) (x₂ : F), x₁ ∈ C₁ → x₂ ∈ D →
      posTangentConeAt (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F))) (WithLp.toLp 2 (x₁, x₂))
        = WithLp.ofLp ⁻¹' (posTangentConeAt C₁ x₁ ×ˢ posTangentConeAt D x₂) ∧
      convexNormalCone (WithLp.toLp 2 (x₁, x₂)) (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F)))
        = WithLp.ofLp ⁻¹' (convexNormalCone x₁ C₁ ×ˢ convexNormalCone x₂ D)) ∧
  (∀ (y₀ : F) (A₀ : E →L[ℝ] F), x ∈ C₁ →
    posTangentConeAt ((fun z => y₀ + A₀ z) '' C₁) (y₀ + A₀ x)
      = closure (A₀ '' posTangentConeAt C₁ x) ∧
    convexNormalCone (y₀ + A₀ x) ((fun z => y₀ + A₀ z) '' C₁)
      = (ContinuousLinearMap.adjoint A₀) ⁻¹' (convexNormalCone x C₁)) ∧
  (∀ (x₁ x₂ : E), x₁ ∈ C₁ → x₂ ∈ C₂ →
    posTangentConeAt (setAdd C₁ C₂) (x₁ + x₂)
      = closure (setAdd (posTangentConeAt C₁ x₁) (posTangentConeAt C₂ x₂)) ∧
    convexNormalCone (x₁ + x₂) (setAdd C₁ C₂)
      = convexNormalCone x₁ C₁ ∩ convexNormalCone x₂ C₂) := by
  sorry
