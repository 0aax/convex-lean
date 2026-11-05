import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem FCA_chap_D_4_4_5
  (Y : Set F)
  (g : E → F → ℝ)
  (hY_compact : IsCompact Y)
  (hf_usc : ∀ x, ∀ y, y ∈ Y → LowerSemicontinuousAt (fun v => (-1 : ℝ) * g x v) y)
  (hf_convex : ∀ y ∈ Y, ConvexOn ℝ Set.univ (fun x => g x y))
  (hf_differentiable : ∀ y ∈ Y, Differentiable ℝ (fun x => g x y))
  (hf_finite : ∀ x, ⨆ y ∈ Y, (g x y : EReal) < ⊤) :
  let F_fun : E → EReal := fun x => ⨆ y ∈ Y, (g x y : EReal)
  ∀ (x₀ : E) (y₀ : F),
    ((y₀ ∈ Y) ∧
      IsMaxOn (fun (y : F) => g x₀ y) Y y₀ ∧
      (∀ (y : F), y ∈ Y → IsMaxOn (fun (y : F) => g x₀ y) Y y → y = y₀)) →
    (∃ (F_finite : E → ℝ),
      (∀ (x : E), (F_finite x : EReal) = F_fun x) ∧
      DifferentiableAt ℝ F_finite x₀ ∧
      (gradient F_finite x₀ = gradient (fun (x : E) => g x y₀) x₀)) := by
  sorry
