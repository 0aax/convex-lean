import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_4_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_4_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_4_2`, so the main result is `FCA_chap_B_2_4_2.FCA_chap_B_2_4_2`.
-/

namespace FCA_chap_B_2_4_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem FCA_chap_B_2_4_2
  (A : F →ₗ[ℝ] E)
  (g : F → EReal)
  (hg_convex : InConvRn g)
  (hg_bounded : ∀ x, imageFun A g x > ⊥) :
  InConvRn (imageFun A g) := by
  obtain ⟨_hbot, ⟨x0, hx0⟩, hconv⟩ := hg_convex
  refine ⟨fun x => hg_bounded x, ⟨A x0, ?_⟩, ?_⟩
  · calc imageFun A g (A x0) ≤ g x0 := sInf_le ⟨x0, rfl, rfl⟩
      _ < ⊤ := hx0
  · intro p hp q hq a b ha hb hab
    obtain ⟨x1, r1⟩ := p
    obtain ⟨x2, r2⟩ := q
    simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    apply le_of_forall_gt_imp_ge_of_dense
    intro w hw
    induction w using EReal.rec with
    | bot => exact absurd hw not_lt_bot
    | top => exact le_top
    | coe w =>
      have hw' : a * r1 + b * r2 < w := by exact_mod_cast hw
      have hεpos : 0 < w - (a * r1 + b * r2) := by linarith
      set ε := w - (a * r1 + b * r2) with hε
      have h1 : imageFun A g x1 < ((r1 + ε : ℝ) : EReal) := by
        calc imageFun A g x1 ≤ r1 := hp
          _ < ((r1 + ε : ℝ) : EReal) := by exact_mod_cast (by linarith : r1 < r1 + ε)
      have h2 : imageFun A g x2 < ((r2 + ε : ℝ) : EReal) := by
        calc imageFun A g x2 ≤ r2 := hq
          _ < ((r2 + ε : ℝ) : EReal) := by exact_mod_cast (by linarith : r2 < r2 + ε)
      obtain ⟨_, ⟨y1, hy1, rfl⟩, hgy1⟩ := sInf_lt_iff.mp h1
      obtain ⟨_, ⟨y2, hy2, rfl⟩, hgy2⟩ := sInf_lt_iff.mp h2
      have hy1' : A y1 = x1 := hy1
      have hy2' : A y2 = x2 := hy2
      have hm1 : ((y1, r1 + ε) : F × ℝ) ∈ epigraph g := le_of_lt hgy1
      have hm2 : ((y2, r2 + ε) : F × ℝ) ∈ epigraph g := le_of_lt hgy2
      have hm := hconv hm1 hm2 ha hb hab
      simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] at hm
      have hA : A (a • y1 + b • y2) = a • x1 + b • x2 := by
        rw [map_add, map_smul, map_smul, hy1', hy2']
      have hsum : a * (r1 + ε) + b * (r2 + ε) = w := by
        have : a * (r1 + ε) + b * (r2 + ε) = a * r1 + b * r2 + (a + b) * ε := by ring
        rw [this, hab, hε]; ring
      calc imageFun A g (a • x1 + b • x2) ≤ g (a • y1 + b • y2) := sInf_le ⟨_, hA, rfl⟩
        _ ≤ ((a * (r1 + ε) + b * (r2 + ε) : ℝ) : EReal) := hm
        _ = (w : EReal) := by rw [hsum]

end FCA_chap_B_2_4_2
