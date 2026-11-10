import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_2`, so the main result is `FCA_chap_A_ex_2.FCA_chap_A_ex_2`.
-/

namespace FCA_chap_A_ex_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_2 :
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | p 0 > 0 ∧ p 1 > 0 ∧ p 0 * p 1 ≥ 1}
  (C = ⋂ (t : ℝ) (_ : t > 0), {p : EuclideanSpace ℝ (Fin 2) | p 0 + t ^ 2 * p 1 ≥ 2 * t}) ∧
  ({s : EuclideanSpace ℝ (Fin 2) |
      Set.Nonempty (exposedFace C s) ∧ exposedFace C s ≠ C}
    = {s : EuclideanSpace ℝ (Fin 2) | s 0 < 0 ∧ s 1 < 0}) := by
  intro C
  have hinner : ∀ s y : EuclideanSpace ℝ (Fin 2), inner ℝ s y = s 0 * y 0 + s 1 * y 1 := by
    intro s y
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hmem : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ C ↔ (p 0 > 0 ∧ p 1 > 0 ∧ p 0 * p 1 ≥ 1) :=
    fun p => Iff.rfl
  have hface : ∀ s x : EuclideanSpace ℝ (Fin 2),
      x ∈ exposedFace C s ↔ (x ∈ C ∧ ∀ y ∈ C, inner ℝ s y ≤ inner ℝ s x) :=
    fun s x => Iff.rfl
  have hvec0 : ∀ a b : ℝ, (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) 0 = a := fun a b => by simp
  have hvec1 : ∀ a b : ℝ, (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) 1 = b := fun a b => by simp
  constructor
  · -- Part 1: description of `C` as an intersection of half-planes
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq, hmem]
    constructor
    · rintro ⟨h0, h1, h01⟩ t ht
      nlinarith [sq_nonneg (t * p 1 - 1)]
    · intro h
      have h1 : p 1 > 0 := by
        by_contra hle
        push_neg at hle
        have ht : (0:ℝ) < |p 0| + 1 := by positivity
        have h' := h (|p 0| + 1) ht
        have hneg : (|p 0| + 1) ^ 2 * p 1 ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
        have := le_abs_self (p 0)
        have := abs_nonneg (p 0)
        linarith
      have h' := h (1 / p 1) (by positivity)
      have h01 : p 0 * p 1 ≥ 1 := by
        have e : (1 / p 1) ^ 2 * p 1 = 1 / p 1 := by
          field_simp
        rw [e] at h'
        have h'' : p 0 ≥ 1 / p 1 := by linarith
        have := (div_le_iff₀ h1).mp h''
        linarith
      refine ⟨?_, h1, h01⟩
      by_contra hle
      push_neg at hle
      nlinarith
  · -- Part 2: the directions with a nonempty proper exposed face
    ext s
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨x, hx⟩, hne⟩
      rw [hface] at hx
      obtain ⟨hxC, hxmax⟩ := hx
      obtain ⟨hx0, hx1, hx01⟩ := (hmem x).mp hxC
      -- two test points
      have hyC : (!₂[2 * x 0, x 1 / 2] : EuclideanSpace ℝ (Fin 2)) ∈ C := by
        rw [hmem, hvec0, hvec1]
        refine ⟨by linarith, by linarith, by nlinarith⟩
      have hzC : (!₂[x 0 / 2, 2 * x 1] : EuclideanSpace ℝ (Fin 2)) ∈ C := by
        rw [hmem, hvec0, hvec1]
        refine ⟨by linarith, by linarith, by nlinarith⟩
      have hy := hxmax _ hyC
      have hz := hxmax _ hzC
      rw [hinner, hinner, hvec0, hvec1] at hy
      rw [hinner, hinner, hvec0, hvec1] at hz
      -- u = s 0 * x 0, v = s 1 * x 1 satisfy u ≤ v / 2 and v ≤ u / 2
      have hu : s 0 * x 0 ≤ s 1 * x 1 / 2 := by linarith
      have hv : s 1 * x 1 ≤ s 0 * x 0 / 2 := by linarith
      rcases lt_trichotomy (s 0) 0 with h0 | h0 | h0
      · have hu' : s 0 * x 0 < 0 := mul_neg_of_neg_of_pos h0 hx0
        have hv' : s 1 * x 1 < 0 := by linarith
        refine ⟨h0, ?_⟩
        by_contra hge
        push_neg at hge
        have := mul_nonneg hge hx1.le
        linarith
      · exfalso
        apply hne
        have hv0 : s 1 * x 1 = 0 := by
          rw [h0] at hu hv
          linarith
        have h1 : s 1 = 0 := by
          rcases mul_eq_zero.mp hv0 with h | h
          · exact h
          · linarith
        ext y
        rw [hface]
        constructor
        · exact fun hy => hy.1
        · intro hy
          refine ⟨hy, fun z _ => ?_⟩
          rw [hinner, hinner, h0, h1]
          simp
      · exfalso
        have hu' : 0 < s 0 * x 0 := mul_pos h0 hx0
        linarith
    · rintro ⟨hs0, hs1⟩
      have hss : 0 < s 0 * s 1 := mul_pos_of_neg_of_neg hs0 hs1
      have hs0' : s 0 ≠ 0 := hs0.ne
      have hs1' : s 1 ≠ 0 := hs1.ne
      obtain ⟨c, hc, hc2⟩ : ∃ c : ℝ, 0 < c ∧ c * c = s 0 * s 1 :=
        ⟨Real.sqrt (s 0 * s 1), Real.sqrt_pos.mpr hss, Real.mul_self_sqrt hss.le⟩
      have hxC : (!₂[-c / s 0, -c / s 1] : EuclideanSpace ℝ (Fin 2)) ∈ C := by
        rw [hmem, hvec0, hvec1]
        refine ⟨div_pos_of_neg_of_neg (by linarith) hs0,
          div_pos_of_neg_of_neg (by linarith) hs1, ?_⟩
        have e : -c / s 0 * (-c / s 1) = 1 := by
          field_simp
          linarith [hc2]
        rw [e]
      have hsx : inner ℝ s (!₂[-c / s 0, -c / s 1] : EuclideanSpace ℝ (Fin 2)) = -2 * c := by
        rw [hinner, hvec0, hvec1]
        field_simp
        ring
      refine ⟨⟨_, (hface _ _).mpr ⟨hxC, fun y hy => ?_⟩⟩, ?_⟩
      · rw [hsx, hinner]
        obtain ⟨hy0, hy1, hy01⟩ := (hmem y).mp hy
        have hA : 0 < -(s 0) * y 0 := mul_pos (neg_pos.mpr hs0) hy0
        have hB : 0 < -(s 1) * y 1 := mul_pos (neg_pos.mpr hs1) hy1
        have hAB : (-(s 0) * y 0) * (-(s 1) * y 1) ≥ c * c := by
          rw [hc2]
          have e : (-(s 0) * y 0) * (-(s 1) * y 1) = (s 0 * s 1) * (y 0 * y 1) := by ring
          rw [e]
          nlinarith
        nlinarith [sq_nonneg ((-(s 0) * y 0) - (-(s 1) * y 1))]
      · intro heq
        have h22 : (!₂[(2:ℝ), 2] : EuclideanSpace ℝ (Fin 2)) ∈ C := by
          rw [hmem, hvec0, hvec1]; norm_num
        have h11 : (!₂[(1:ℝ), 1] : EuclideanSpace ℝ (Fin 2)) ∈ C := by
          rw [hmem, hvec0, hvec1]; norm_num
        rw [← heq, hface] at h22
        have := h22.2 _ h11
        rw [hinner, hinner, hvec0, hvec1, hvec0, hvec1] at this
        linarith

end FCA_chap_A_ex_2
