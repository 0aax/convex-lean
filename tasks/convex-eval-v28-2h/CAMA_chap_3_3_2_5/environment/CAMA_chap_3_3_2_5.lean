import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsConvexCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C,
  ∀ (α : ℝ), α ≥ 0 → ∀ (β : ℝ), β ≥ 0 → α • x + β • y ∈ C

noncomputable def pC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) (C : Set E)
    (hC₁ : IsClosed C) (hC₂ : Convex ℝ C) (hC₃ : Set.Nonempty C) : E
    := Classical.choose (exists_norm_eq_iInf_of_complete_convex hC₃ hC₁.isComplete hC₂ x)

lemma convexCone_isConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E} (hC : IsConvexCone C) : Convex ℝ C := by
  intro x hx y hy a b ha hb hab
  exact hC x hx y hy a ha b hb

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

lemma polarCone_isClosed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E} : IsClosed (polarCone K) := by
  have pc_intersection : (polarCone K) = ⋂ x ∈ K, {s : E | inner ℝ s x ≤ 0} := by
    ext s
    simp [polarCone]
  rw [pc_intersection]
  have h_cont (x : E) : Continuous (fun s : E => (inner ℝ s x : ℝ)) :=
    continuous_inner.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ => x)))
  have h_closed : ∀ x ∈ K, IsClosed {s : E | inner ℝ s x ≤ 0} := by
    intro x _
    exact IsClosed.preimage (h_cont x) isClosed_Iic
  exact isClosed_biInter h_closed

lemma polarCone_isConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E} : Convex ℝ (polarCone K) := by
  intro x hx y hy a b ha hb hab
  have h_combo : ∀ z ∈ K, inner ℝ (a • x + b • y) z ≤ 0 := by
    intro z hz
    simp [inner_add_left, inner_smul_left_eq_star_smul]
    have hx' : a * (inner ℝ x z) ≤ 0 := by
      have non_mul_x := hx.out z hz
      have := mul_le_mul_of_nonneg_left non_mul_x ha
      simpa [mul_zero] using this
    have hy' : b * (inner ℝ y z) ≤ 0 := by
      have non_mul_y := hy.out z hz
      have := mul_le_mul_of_nonneg_left non_mul_y hb
      simpa [mul_zero] using this
    have := add_le_add hx' hy'
    simpa [add_zero] using this
  exact h_combo

lemma polarCone_isNonempty {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E} : Set.Nonempty (polarCone K) :=
  ⟨0, by simp [polarCone]⟩

theorem CAMA_chap_3_3_2_5
  (K : Set E)
  (x x₁ x₂ : E)
  (hK₀ : IsConvexCone K)
  (hK₁ : IsClosed K)
  (hK₂ : Set.Nonempty K) :
  let K' := (polarCone K)
  x = x₁ + x₂ ∧ x₁ ∈ K ∧ x₂ ∈ K' ∧ inner ℝ x₁ x₂ = 0 ↔
  x₁ = pC x K hK₁ (convexCone_isConvex hK₀) hK₂ ∧
  x₂ = pC x K' polarCone_isClosed polarCone_isConvex polarCone_isNonempty := by
  sorry
