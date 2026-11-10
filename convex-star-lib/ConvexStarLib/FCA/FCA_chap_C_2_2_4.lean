import ConvexStarLib.Defs

/-!
# `FCA_chap_C_2_2_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_2_2_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_2_2_4`, so the main result is `FCA_chap_C_2_2_4.FCA_chap_C_2_2_4`.
-/

namespace FCA_chap_C_2_2_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_2_2_4
  [FiniteDimensional ℝ E]
  (S : Set E)
  (x : E)
  (hS_nonempty : Set.Nonempty S)
  (hS_closed : IsClosed S)
  (hS_convex : Convex ℝ S)
  (hx : x ∈ S) :
  let σS := supportFunction S
  let Sinfty := asymptoticConeAt S x
  (polarCone (closure (effDom σS)) = Sinfty) ∧
  (closure (effDom σS) = polarCone Sinfty) := by
  intro σS Sinfty
  -- characterization of the effective domain
  have hdom : ∀ w : E, w ∈ effDom σS ↔ ∃ M : ℝ, ∀ v ∈ S, inner ℝ v w ≤ M := by
    intro w
    constructor
    · intro hw
      obtain ⟨r, hr, -⟩ := EReal.lt_iff_exists_real_btwn.mp hw
      refine ⟨r, fun v hv => ?_⟩
      have h1 : ((inner ℝ v w : ℝ) : EReal) ≤ σS w :=
        le_sSup (Set.mem_image_of_mem _ hv)
      exact_mod_cast (h1.trans_lt hr).le
    · rintro ⟨M, hM⟩
      have h1 : σS w ≤ (M : EReal) := by
        apply sSup_le
        rintro _ ⟨v, hv, rfl⟩
        exact EReal.coe_le_coe_iff.mpr (hM v hv)
      exact h1.trans_lt (EReal.coe_lt_top M)
  set D := effDom σS with hD
  -- D is convex
  have hDconv : Convex ℝ D := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    obtain ⟨M₁, hM₁⟩ := (hdom w₁).mp hw₁
    obtain ⟨M₂, hM₂⟩ := (hdom w₂).mp hw₂
    refine (hdom _).mpr ⟨a * M₁ + b * M₂, fun v hv => ?_⟩
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    exact add_le_add (mul_le_mul_of_nonneg_left (hM₁ v hv) ha)
      (mul_le_mul_of_nonneg_left (hM₂ v hv) hb)
  have h0D : (0 : E) ∈ D := (hdom 0).mpr ⟨0, fun v _ => by simp⟩
  have hDcone : ∀ w ∈ D, ∀ s : ℝ, 0 < s → s • w ∈ D := by
    intro w hw s hs
    obtain ⟨M, hM⟩ := (hdom w).mp hw
    refine (hdom _).mpr ⟨s * M, fun v hv => ?_⟩
    rw [inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hM v hv) hs.le
  -- Part 1
  have part1 : polarCone (closure D) = Sinfty := by
    ext d
    constructor
    · intro hd t ht
      by_contra hnot
      obtain ⟨f, u, hfS, hfu⟩ := geometric_hahn_banach_closed_point hS_convex hS_closed hnot
      set w := (InnerProductSpace.toDual ℝ E).symm f with hw
      have hfw : ∀ y, f y = inner ℝ w y := fun y => (InnerProductSpace.toDual_symm_apply).symm
      have hwD : w ∈ D := (hdom w).mpr ⟨u, fun v hv => by
        rw [real_inner_comm, ← hfw]; exact (hfS v hv).le⟩
      have hdw : inner ℝ d w ≤ 0 := hd w (subset_closure hwD)
      have hxu := hfS x hx
      rw [hfw] at hxu hfu
      rw [inner_add_right, inner_smul_right, real_inner_comm d w] at hfu
      nlinarith
    · intro hd
      have key : ∀ w ∈ D, inner ℝ d w ≤ 0 := by
        intro w hw
        obtain ⟨M, hM⟩ := (hdom w).mp hw
        by_contra hpos
        push_neg at hpos
        have hxM := hM x hx
        set t := (M - inner ℝ x w + 1) / inner ℝ d w with ht
        have htpos : 0 < t := by
          apply div_pos _ hpos
          linarith
        have := hM _ (hd t htpos)
        rw [inner_add_left, real_inner_smul_left] at this
        have h2 : t * inner ℝ d w = M - inner ℝ x w + 1 := by
          rw [ht]; field_simp
        linarith
      intro w hw
      have hcl : IsClosed {w : E | inner ℝ d w ≤ 0} :=
        isClosed_le (continuous_const.inner continuous_id) continuous_const
      exact closure_minimal key hcl hw
  refine ⟨part1, ?_⟩
  ext w
  constructor
  · intro hw d hd
    rw [← part1] at hd
    rw [real_inner_comm]
    exact hd w hw
  · intro hw
    by_contra hnot
    obtain ⟨f, u, hfD, hfu⟩ :=
      geometric_hahn_banach_closed_point hDconv.closure isClosed_closure hnot
    set d := (InnerProductSpace.toDual ℝ E).symm f with hd
    have hfd : ∀ y, f y = inner ℝ d y := fun y => (InnerProductSpace.toDual_symm_apply).symm
    have hu0 : 0 < u := by
      have := hfD 0 (subset_closure h0D)
      simpa using this
    have hdpol : d ∈ polarCone (closure D) := by
      have key : ∀ a ∈ D, inner ℝ d a ≤ 0 := by
        intro a ha
        by_contra hpos
        push_neg at hpos
        set s := (u + 1) / inner ℝ d a with hs
        have hspos : 0 < s := div_pos (by linarith) hpos
        have := hfD _ (subset_closure (hDcone a ha s hspos))
        rw [hfd, inner_smul_right] at this
        have h2 : s * inner ℝ d a = u + 1 := by rw [hs]; field_simp
        linarith
      intro a ha
      have hcl : IsClosed {a : E | inner ℝ d a ≤ 0} :=
        isClosed_le (continuous_const.inner continuous_id) continuous_const
      exact closure_minimal key hcl ha
    rw [part1] at hdpol
    have := hw d hdpol
    rw [hfd, real_inner_comm] at hfu
    linarith

end FCA_chap_C_2_2_4
