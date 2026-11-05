import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def pC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) (C : Set E)
    (hC₁ : IsClosed C) (hC₂ : Convex ℝ C) (hC₃ : Set.Nonempty C) : E
    := Classical.choose (exists_norm_eq_iInf_of_complete_convex hC₃ hC₁.isComplete hC₂ x)

theorem FCA_chap_A_ex_14 (C : ℕ → Set E) (h_closed : ∀ k, IsClosed (C k))
    (h_convex : ∀ k, Convex ℝ (C k)) (h_anti : Antitone C)
    (h_ne : Set.Nonempty (⋂ k, C k)) :
    let Cinf := ⋂ k, C k
    (∀ x : E,
      Filter.Tendsto
        (fun k ↦ pC x (C k) (h_closed k) (h_convex k)
          (h_ne.mono (Set.iInter_subset C k)))
        Filter.atTop
        (𝓝 (pC x Cinf (isClosed_iInter fun k ↦ h_closed k)
          (convex_iInter fun k ↦ h_convex k) h_ne))) ∧
    (∀ x : E,
      Monotone (fun k ↦ Metric.infDist x (C k)) ∧
      Filter.Tendsto (fun k ↦ Metric.infDist x (C k))
        Filter.atTop (𝓝 (Metric.infDist x Cinf))) := by
  sorry
