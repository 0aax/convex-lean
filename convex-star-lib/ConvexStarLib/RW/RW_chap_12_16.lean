import ConvexStarLib.Defs

/-!
# `RW_chap_12_16`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_16` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_16`, so the main result is `RW_chap_12_16.RW_chap_12_16`.
-/

namespace RW_chap_12_16

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem RW_chap_12_16
  (F : E → Set E)
  (hF : IsNonexpansive F)
  (hF_nonempty : ∀ x, (F x).Nonempty) :
  let D := subMap idMap F
  IsMaximalMonotone D := by
  intro D
  constructor
  · intro x₀ x₁ v₀ v₁ hv₀ hv₁
    obtain ⟨u₀, hu₀, w₀, hw₀, rfl⟩ := hv₀
    obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hv₁
    have hu₀' : u₀ = x₀ := hu₀
    have hu₁' : u₁ = x₁ := hu₁
    subst hu₀' hu₁'
    have h1 : ‖w₁ - w₀‖ ≤ ‖u₁ - u₀‖ := hF u₀ u₁ w₀ w₁ hw₀ hw₁
    have h2 : inner ℝ (w₁ - w₀) (u₁ - u₀) ≤ ‖w₁ - w₀‖ * ‖u₁ - u₀‖ := real_inner_le_norm _ _
    have h3 : (u₁ - w₁ - (u₀ - w₀)) = (u₁ - u₀) - (w₁ - w₀) := by abel
    rw [h3, inner_sub_left, real_inner_self_eq_norm_sq]
    have h4 : 0 ≤ ‖u₁ - u₀‖ := norm_nonneg _
    nlinarith
  · intro x_hat v_hat hv
    obtain ⟨w₀, hw₀⟩ := hF_nonempty x_hat
    set d : E := v_hat - x_hat + w₀ with hd
    have hd_ne : d ≠ 0 := by
      intro h
      apply hv
      refine ⟨x_hat, rfl, w₀, hw₀, ?_⟩
      have : v_hat = d + x_hat - w₀ := by rw [hd]; abel
      rw [this, h]
      abel
    set x_tilde : E := x_hat + (1/4 : ℝ) • d with hx_tilde
    obtain ⟨w₁, hw₁⟩ := hF_nonempty x_tilde
    refine ⟨x_tilde, x_tilde - w₁, ⟨x_tilde, rfl, w₁, hw₁, rfl⟩, ?_⟩
    have h1 : ‖w₁ - w₀‖ ≤ ‖x_tilde - x_hat‖ := hF x_hat x_tilde w₀ w₁ hw₀ hw₁
    have h2 : x_tilde - x_hat = (1/4 : ℝ) • d := by rw [hx_tilde]; abel
    rw [h2, norm_smul] at h1
    have h3 : v_hat - (x_tilde - w₁) = (3/4 : ℝ) • d + (w₁ - w₀) := by
      rw [hx_tilde, hd]; module
    have h4 : x_hat - x_tilde = (-(1/4) : ℝ) • d := by
      rw [hx_tilde]; module
    rw [h3, h4, inner_smul_right, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    have h5 : inner ℝ (w₁ - w₀) d ≥ -(‖w₁ - w₀‖ * ‖d‖) := by
      have := abs_real_inner_le_norm (w₁ - w₀) d
      linarith [neg_abs_le (inner ℝ (w₁ - w₀) d)]
    have h6 : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
    have h7 : ‖(1/4 : ℝ)‖ = 1/4 := by norm_num
    rw [h7] at h1
    simp only [RCLike.conj_to_real]
    nlinarith [norm_nonneg (w₁ - w₀)]

end RW_chap_12_16
