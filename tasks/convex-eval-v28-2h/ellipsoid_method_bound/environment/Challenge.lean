import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


def InDomIsSubgradientAt {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (w : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ 𝓧, f y ≥ f x + inner ℝ (y - x) w

def IsMinimizerAtTforEllipsoid {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (t : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  : Prop :=
  x ∈ 𝓧 ∧
  (∃ i : ℕ, i ≤ t ∧ c i = x) ∧
  (∀ i : ℕ, i ≤ t → c i ∈ 𝓧 → f x ≤ f (c i))

def IsSeparatingHyperplane {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (c w : EuclideanSpace ℝ (Fin n)) : Prop :=
  𝓧 ⊆ {x | inner ℝ (x - c) w ≤ 0}

noncomputable def innerRightLM {n : ℕ}
  (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
  { toFun    := fun v => inner ℝ w v
    map_add' := by
      intro x y
      simp [inner_add_right]
    map_smul' := by
      intro a x
      simp [inner_smul_right] }

noncomputable def updateHRank1 {n : ℕ}
  (w : EuclideanSpace ℝ (Fin n))
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  let phi : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := (innerRightLM w).comp H
  LinearMap.smulRight phi (H w)

noncomputable def ellipsoidAxesLinMap {n : ℕ}
  (w : EuclideanSpace ℝ (Fin n))
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  let a : ℝ := ((n : ℝ)^2) / (((n : ℝ)^2) - 1)
  let b : ℝ := (2 / ((n : ℝ) + 1)) / (inner ℝ w (H w))
  a • (H - b • updateHRank1 w H)

noncomputable def ellipsoidMethodStep {n : ℕ}
  (w c : EuclideanSpace ℝ (Fin n))
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
  let c_next := c - ((1 / ((n : ℝ) + 1)) *
    (1 / Real.sqrt (inner ℝ w (H w)))) • (H w)
  let H_next : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := ellipsoidAxesLinMap w H
  (c_next, H_next)

def IsEllipsoidMethodSequence {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (H : ℕ → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
  (w : ℕ → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (R : ℝ) : Prop :=
  (c 0 = 0) ∧
  (H 0 = (R ^ 2 • LinearMap.id)) ∧
  (∀ t, w t ≠ 0) ∧
  (∀ t, c (t + 1) = (ellipsoidMethodStep (w t) (c t) (H t)).1) ∧
  (∀ t, H (t + 1) = (ellipsoidMethodStep (w t) (c t) (H t)).2) ∧
  (∀ t,
    (c t ∈ 𝓧 ∧ InDomIsSubgradientAt 𝓧 f (c t) (w t)) ∨
    (c t ∉ 𝓧 ∧ IsSeparatingHyperplane 𝓧 (c t) (w t))) ∧
  (∀ t, IsMinimizerAtTforEllipsoid 𝓧 t f c (x t))

noncomputable def ellipsoidDecay (n i : ℕ) : ℝ :=
  Real.exp (-(i : ℝ) / (2 * (n : ℝ) ^ 2))

noncomputable def ellipsoidGapBound (B R r : ℝ) (n i : ℕ) : ℝ :=
  2 * B * R * ellipsoidDecay n i / r

theorem ellipsoid_method_bound {n t : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (H : ℕ → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
  (w : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
  (B R r : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (ht : (t : ℝ) ≥ 2 * (n : ℝ) ^ 2 * Real.log (R / r))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty (interior 𝓧))
  (h𝓧_contained : 𝓧 ⊆ Metric.closedBall 0 R ∧ Metric.ball 0 r ⊆ 𝓧)
  (hf_continuous : Continuous f)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_bounded : ∀ x ∈ 𝓧, f x ≤ B ∧ f x ≥ -B)
  (h_cog_sequence : IsEllipsoidMethodSequence 𝓧 f c H w x R)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star)
  (hn : n > 1)
  (hR : R > 0)
  (hr : r > 0)
  (hB : B > 0) :
  (∃ s ≤ t, c s ∈ 𝓧) ∧
  f (x t) - f x_star ≤ ellipsoidGapBound B R r n t := by
  sorry
