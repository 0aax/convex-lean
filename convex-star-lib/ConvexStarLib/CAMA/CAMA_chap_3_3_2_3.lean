import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_3_2_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_3_2_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_3_2_3`, so the main result is `CAMA_chap_3_3_2_3.CAMA_chap_3_3_2_3`.
-/

namespace CAMA_chap_3_3_2_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_3_2_3
  (K : Set E)
  (x y : E)
  (hK₀ : IsConvexCone K)
  (hK₁ : IsClosed K)
  (hK₂ : Set.Nonempty K) :
  y = pC x K hK₁ (convexCone_isConvex hK₀) hK₂ ↔
  (y ∈ K) ∧ (x - y ∈ polarCone K) ∧ (inner ℝ (x - y) y = 0) := by
  have hconv : Convex ℝ K := convexCone_isConvex hK₀
  have hspec : pC x K hK₁ (convexCone_isConvex hK₀) hK₂ ∈ K ∧
      ‖x - pC x K hK₁ (convexCone_isConvex hK₀) hK₂‖ = ⨅ w : K, ‖x - w‖ :=
    Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex hK₂ hK₁.isComplete (convexCone_isConvex hK₀) x)
  generalize pC x K hK₁ (convexCone_isConvex hK₀) hK₂ = p at hspec ⊢
  obtain ⟨hpK, hpnorm⟩ := hspec
  have hpchar : ∀ w ∈ K, inner ℝ (x - p) (w - p) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hconv hpK).1 hpnorm
  obtain ⟨k, hk⟩ := hK₂
  have h0 : (0 : E) ∈ K := by
    simpa using hK₀ k hk k hk 0 le_rfl 0 le_rfl
  have hadd : ∀ u ∈ K, ∀ v ∈ K, u + v ∈ K := fun u hu v hv => by
    simpa using hK₀ u hu v hv 1 zero_le_one 1 zero_le_one
  constructor
  · rintro rfl
    refine ⟨hpK, ?_, ?_⟩
    · intro w hw
      have := hpchar (w + y) (hadd w hw y hpK)
      simpa using this
    · have a := hpchar 0 h0
      have b := hpchar (y + y) (hadd y hpK y hpK)
      rw [zero_sub, inner_neg_right, neg_nonpos] at a
      rw [add_sub_cancel_right] at b
      exact le_antisymm b a
  · rintro ⟨hyK, hpol, horth⟩
    have hychar : ∀ w ∈ K, inner ℝ (x - y) (w - y) ≤ 0 := fun w hw => by
      rw [inner_sub_right, horth, sub_zero]
      exact hpol w hw
    have h1 := hychar p hpK
    have h2 := hpchar y hyK
    have key : inner ℝ (p - y) (p - y) ≤ 0 := by
      have e : p - y = (x - y) - (x - p) := by abel
      calc inner ℝ (p - y) (p - y) = inner ℝ ((x - y) - (x - p)) (p - y) := by rw [← e]
        _ = inner ℝ (x - y) (p - y) - inner ℝ (x - p) (p - y) := inner_sub_left _ _ _
        _ = inner ℝ (x - y) (p - y) + inner ℝ (x - p) (y - p) := by
          rw [← neg_sub p y, inner_neg_right]; ring
        _ ≤ 0 := by linarith
    rw [real_inner_self_nonpos, sub_eq_zero] at key
    exact key.symm

end CAMA_chap_3_3_2_3
