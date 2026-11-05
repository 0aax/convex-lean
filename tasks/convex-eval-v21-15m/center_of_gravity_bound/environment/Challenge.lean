import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def InDomIsSubgradientAt {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (w : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ 𝓧, f y ≥ f x + inner ℝ (y - x) w

def IsMinimizerAtTforCoG {n : ℕ}
  (t : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  : Prop :=
  (∀ (i : ℕ), i ≤ t → f x ≤ f (c i)) ∧
  (∃ (i : ℕ), i ≤ t ∧ (c i) = x)

noncomputable def barycenter {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (K : Set E) : E :=
  (MeasureTheory.volume.real K)⁻¹ • ∫ x in K, x

noncomputable def centerOfGravityStep {n : ℕ}
  (S_prev : Set (EuclideanSpace ℝ (Fin n)))
  (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) × Set (EuclideanSpace ℝ (Fin n)) :=
  let c := barycenter S_prev
  (c, S_prev ∩ {x | inner ℝ (x - c) w ≤ 0})

def IsCenterOfGravitySequence {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (S : ℕ → Set (EuclideanSpace ℝ (Fin n)))
  (w : ℕ → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (c 0 = barycenter (S 0)) ∧
  (S 0 = 𝓧) ∧
  (∀ t, c (t + 1) = (centerOfGravityStep (S t) (w t)).1) ∧
  (∀ t, S (t + 1) = (centerOfGravityStep (S t) (w t)).2) ∧
  (∀ t, InDomIsSubgradientAt 𝓧 f (c (t + 1)) (w t)) ∧
  (∀ t, IsMinimizerAtTforCoG t f c (x t))

theorem center_of_gravity_bound {n t : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n)) (S : ℕ → Set (EuclideanSpace ℝ (Fin n)))
  (w : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
  (B R r : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty (interior 𝓧))
  (h𝓧_contained : 𝓧 ⊆ Metric.ball 0 R ∧ Metric.ball 0 r ⊆ 𝓧)
  (hf_continuous : Continuous f)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_bounded : ∀ x ∈ 𝓧, f x ≤ B ∧ f x ≥ -B)
  (h_cog_sequence : IsCenterOfGravitySequence 𝓧 f c S w x)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star)
  (hn : n > 0) :
  f (x t) - f x_star ≤ 2 * B * (1 - 1 / (Real.exp 1)) ^ ((t : ℝ) / (n : ℝ)) := by
  sorry
