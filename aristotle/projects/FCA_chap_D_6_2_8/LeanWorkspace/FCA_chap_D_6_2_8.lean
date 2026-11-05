import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Filter Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_6_2_8
    (fk : ℕ → (E → ℝ))
    (f : E → ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (fk i))
    (hf_seq_diff : ∀ i, Differentiable ℝ (fk i))
    (hf_diff : Differentiable ℝ f)
    (hf_pointwise : ∀ v, Filter.Tendsto (fun k => fk k v) Filter.atTop (𝓝 (f v))) :
    ∀ (K : Set E), IsCompact K →
    TendstoUniformlyOn (fun k => (fun x => gradient (fk k) x))
    (fun x => gradient f x) Filter.atTop K := by
  sorry
