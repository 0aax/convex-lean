import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def InDomIsSubgradientAt {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (w : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ 𝓧, f y ≥ f x + inner ℝ (y - x) w

noncomputable def pC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) (C : Set E)
    (hC₁ : IsClosed C) (hC₂ : Convex ℝ C) (hC₃ : Set.Nonempty C) : E
    := Classical.choose (exists_norm_eq_iInf_of_complete_convex hC₃ hC₁.isComplete hC₂ x)

noncomputable def projSubgradientStep {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (g : EuclideanSpace ℝ (Fin n))
  (η : ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : EuclideanSpace ℝ (Fin n) :=
  let y_next := x - η • g
  pC y_next 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty

def IsProjectedSubgradientSequence {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (g : ℕ → EuclideanSpace ℝ (Fin n))
  (η : ℕ → ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : Prop :=
  (∀ t, x (t + 1) = projSubgradientStep 𝓧 (x t) (g t) (η t) h𝓧_nonempty h𝓧_compact h𝓧_convex) ∧
  (∀ t, InDomIsSubgradientAt 𝓧 f (x t) (g t))

theorem subgradient_bound {t : ℕ}
    (𝓧 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (g : ℕ → EuclideanSpace ℝ (Fin n))
    (R L : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
    (hx_init : x 0 ∈ 𝓧)
    (h𝓧_nonempty : Set.Nonempty 𝓧)
    (h𝓧_compact : IsCompact 𝓧)
    (h𝓧_convex : Convex ℝ 𝓧)
    (h𝓧_contained : 𝓧 ⊆ Metric.ball (x 0) R)
    (hR : R > 0) (hL : L > 0) (ht : t > 0)
    (hf_convex : ConvexOn ℝ 𝓧 f)
    (hf_exists_subgrad : ∀ x ∈ 𝓧, ∃ w, InDomIsSubgradientAt 𝓧 f x w)
    (hg_bounded : ∀ s, ‖g s‖ ≤ L)
    (h_ps_seq : IsProjectedSubgradientSequence 𝓧 f x g (fun _ => R / (L * Real.sqrt t))
      h𝓧_nonempty h𝓧_compact h𝓧_convex)
    (hx_star_mem : x_star ∈ 𝓧)
    (hx_star : IsMinOn f 𝓧 x_star) :
    f ((1 / (t : ℝ)) • (∑ i ∈ Finset.range t, x i)) - f x_star ≤
      (R * L) / Real.sqrt t := by
  sorry
