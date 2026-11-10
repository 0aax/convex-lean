import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_2_1`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_2_1`, so the main result is `CAMA_chap_3_2_2_1.CAMA_chap_3_2_2_1`.
-/

namespace CAMA_chap_3_2_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_2_1
  (C : Set E)
  (x₁ x₂ : E)
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hx₁ : x₁ ∈ C)
  (hx₂ : x₂ ∈ C) :
  (asymptoticConeAt C x₁) = (asymptoticConeAt C x₂) := by
  have key : ∀ y₁ y₂ : E, y₁ ∈ C → y₂ ∈ C →
      asymptoticConeAt C y₁ ⊆ asymptoticConeAt C y₂ := by
    intro y₁ y₂ hy₁ hy₂ d hd t ht
    have hg : Continuous (fun ε : ℝ => (1 - ε) • y₂ + ε • y₁ + t • d) := by
      fun_prop
    have hmem : ∀ᶠ ε in 𝓝[>] (0:ℝ), (1 - ε) • y₂ + ε • y₁ + t • d ∈ C := by
      filter_upwards [Ioo_mem_nhdsGT (one_pos : (0:ℝ) < 1)] with ε hε
      have h1 : y₁ + (t / ε) • d ∈ C := hd (t / ε) (div_pos ht hε.1)
      have h2 := hC₁ hy₂ h1 (by linarith [hε.2] : (0:ℝ) ≤ 1 - ε) hε.1.le (by ring)
      have hε0 : ε ≠ 0 := hε.1.ne'
      have h3 : ε * (t / ε) = t := by field_simp
      convert h2 using 1
      rw [smul_add, smul_smul, h3, add_assoc]
    have htend : Filter.Tendsto (fun ε : ℝ => (1 - ε) • y₂ + ε • y₁ + t • d)
        (𝓝[>] 0) (𝓝 (y₂ + t • d)) := by
      have := hg.tendsto 0
      simp only [sub_zero, one_smul, zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hC₀.mem_of_tendsto htend hmem
  exact Set.Subset.antisymm (key x₁ x₂ hx₁ hx₂) (key x₂ x₁ hx₂ hx₁)

end CAMA_chap_3_2_2_1
