import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_4_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_4_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_4_2`, so the main result is `FCA_chap_E_1_4_2.FCA_chap_E_1_4_2`.
-/

namespace FCA_chap_E_1_4_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_1_4_2
  (f : E → EReal)
  (x : E)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  x ∈ intrinsicInterior ℝ (effDom f) → Set.Nonempty (convexSubdifferential f x) := by
  intro hx
  obtain ⟨-, -, hconv⟩ := hf_convex
  set D := effDom f with hD_def
  have hxD : x ∈ D := intrinsicInterior_subset hx
  have hxD' : f x < ⊤ := hxD
  -- key convexity inequality, derived from convexity of the epigraph
  have key : ∀ u v : E, u ∈ D → v ∈ D → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • u + b • v) ≤ ((a * (f u).toReal + b * (f v).toReal : ℝ) : EReal) := by
    intro u v hu hv a b ha hb hab
    have hu' : (u, (f u).toReal) ∈ epigraph f := by
      show f u ≤ ((f u).toReal : EReal)
      rw [EReal.coe_toReal (show f u < ⊤ from hu).ne (f_ne_bot u).ne']
    have hv' : (v, (f v).toReal) ∈ epigraph f := by
      show f v ≤ ((f v).toReal : EReal)
      rw [EReal.coe_toReal (show f v < ⊤ from hv).ne (f_ne_bot v).ne']
    have := hconv hu' hv' ha hb hab
    simpa [epigraph] using this
  set A := affineSpan ℝ D with hA_def
  set V := A.direction with hV_def
  set P := V.starProjection with hP_def
  have hxA : x ∈ A := subset_affineSpan ℝ D hxD
  have hprA : ∀ y : E, P (y - x) + x ∈ A := fun y =>
    AffineSubspace.vadd_mem_of_mem_direction (V.starProjection_apply_mem _) hxA
  have hpr_self : ∀ y ∈ A, P (y - x) + x = y := by
    intro y hy
    have : y - x ∈ V := AffineSubspace.vsub_mem_direction hy hxA
    rw [Submodule.starProjection_eq_self_iff.mpr this, sub_add_cancel]
  have hpr_aff : ∀ (u v : E) (a b : ℝ), a + b = 1 →
      P ((a • u + b • v) - x) + x = a • (P (u - x) + x) + b • (P (v - x) + x) := by
    intro u v a b hab
    obtain rfl : b = 1 - a := by linarith
    have e1 : (a • u + (1 - a) • v) - x = a • (u - x) + (1 - a) • (v - x) := by module
    rw [e1, map_add, map_smul, map_smul]
    module
  set C : Set E := {y : E | P (y - x) + x ∈ D} with hC_def
  set g : E → ℝ := fun y => (f (P (y - x) + x)).toReal with hg_def
  have hgC : ConvexOn ℝ C g := by
    refine ⟨?_, ?_⟩
    · intro u hu v hv a b ha hb hab
      show f (P ((a • u + b • v) - x) + x) < ⊤
      rw [hpr_aff u v a b hab]
      exact lt_of_le_of_lt (key _ _ hu hv a b ha hb hab) (EReal.coe_lt_top _)
    · intro u hu v hv a b ha hb hab
      simp only [hg_def, smul_eq_mul]
      rw [hpr_aff u v a b hab]
      have h1 := key _ _ hu hv a b ha hb hab
      have h2 := EReal.toReal_le_toReal h1 (f_ne_bot _).ne' (EReal.coe_ne_top _)
      rwa [EReal.toReal_coe] at h2
  have hxC : x ∈ interior C := by
    obtain ⟨z, hz, hzx⟩ := mem_intrinsicInterior.mp hx
    let pr : E → A := fun y => ⟨P (y - x) + x, hprA y⟩
    have hpr_cont : Continuous pr := by
      apply Continuous.subtype_mk
      fun_prop
    have hprx : pr x = z := by
      apply Subtype.ext
      simp [pr, hzx]
    rw [mem_interior]
    refine ⟨pr ⁻¹' interior ((↑) ⁻¹' D), ?_, isOpen_interior.preimage hpr_cont, ?_⟩
    · intro y hy
      exact interior_subset (s := ((↑) ⁻¹' D : Set A)) hy
    · rw [Set.mem_preimage, hprx]; exact hz
  have hgcont : ContinuousOn g (interior C) := hgC.continuousOn_interior
  set S : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ interior C ∧ g p.1 < p.2} with hS_def
  have hS_conv : Convex ℝ S :=
    (hgC.subset interior_subset hgC.1.interior).convex_strict_epigraph
  have hS_open : IsOpen S := by
    have h1 : IsOpen (Prod.fst ⁻¹' interior C : Set (E × ℝ)) :=
      isOpen_interior.preimage continuous_fst
    have h2 : ContinuousOn (fun p : E × ℝ => p.2 - g p.1) (Prod.fst ⁻¹' interior C) := by
      apply ContinuousOn.sub continuous_snd.continuousOn
      exact hgcont.comp continuous_fst.continuousOn (fun p hp => hp)
    have := h2.isOpen_inter_preimage h1 (isOpen_Ioi (a := (0 : ℝ)))
    convert this using 1
    ext p
    simp [S, sub_pos]
  have hxS : (x, g x) ∉ S := fun h => lt_irrefl _ h.2
  obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hS_conv hS_open hxS
  have hLdec : ∀ (y : E) (t : ℝ), L (y, t) = L (y, 0) + t * L (0, 1) := by
    intro y t
    have : ((y, t) : E × ℝ) = (y, 0) + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set c := L (0, 1) with hc_def
  have hc : c < 0 := by
    have h := hL (x, g x + 1) ⟨hxC, by linarith⟩
    rw [hLdec x (g x + 1), hLdec x (g x)] at h
    linarith
  set k : ℝ := -c with hk_def
  have hk : 0 < k := by linarith
  set ℓ : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ) with hℓ_def
  have hℓ : ∀ y, ℓ y = L (y, 0) := fun y => rfl
  set s₀ : E := k⁻¹ • (InnerProductSpace.toDual ℝ E).symm ℓ with hs₀_def
  have hs₀ : ∀ y, inner ℝ s₀ y = k⁻¹ * ℓ y := by
    intro y
    rw [hs₀_def, real_inner_smul_left, InnerProductSpace.toDual_symm_apply]
  have hint : ∀ y ∈ interior C, g x + inner ℝ s₀ (y - x) ≤ g y := by
    intro y hy
    rw [hs₀, map_sub, hℓ, hℓ]
    have h : ∀ ε > 0, L (y, 0) + (g y + ε) * c < L (x, 0) + g x * c := by
      intro ε hε
      have := hL (y, g y + ε) ⟨hy, by linarith⟩
      rwa [hLdec y, hLdec x] at this
    have h' : L (y, 0) + g y * c ≤ L (x, 0) + g x * c := by
      apply le_of_forall_pos_lt_add
      intro ε hε
      have := h (ε / k) (div_pos hε hk)
      have e : (g y + ε / k) * c = g y * c - ε := by
        have hc0 : c ≠ 0 := hc.ne
        rw [hk_def]; field_simp; ring
      linarith
    have : k⁻¹ * (L (y, 0) - L (x, 0)) ≤ g y - g x := by
      rw [inv_mul_le_iff₀ hk]
      rw [hk_def]
      linarith
    linarith
  have hall : ∀ y ∈ C, g x + inner ℝ s₀ (y - x) ≤ g y := by
    intro y hy
    have hm : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ interior C :=
      hgC.1.combo_interior_self_mem_interior hxC hy (by norm_num) (by norm_num) (by norm_num)
    have h1 := hint _ hm
    have h2 := hgC.2 (interior_subset hxC) hy (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have h3 : (1/2 : ℝ) • x + (1/2 : ℝ) • y - x = (1/2 : ℝ) • (y - x) := by module
    rw [h3, real_inner_smul_right] at h1
    simp only [smul_eq_mul] at h2
    linarith
  refine ⟨s₀, fun y => ?_⟩
  show f y ≥ f x + ((inner ℝ s₀ (y - x) : ℝ) : EReal)
  by_cases hy : f y < ⊤
  · have hyD : y ∈ D := hy
    have hyA : y ∈ A := subset_affineSpan ℝ D hyD
    have hyC : y ∈ C := by
      show P (y - x) + x ∈ D
      rw [hpr_self y hyA]; exact hyD
    have := hall y hyC
    have egy : g y = (f y).toReal := by simp only [hg_def]; rw [hpr_self y hyA]
    have egx : g x = (f x).toReal := by simp only [hg_def]; rw [hpr_self x hxA]
    rw [egy, egx] at this
    rw [← EReal.coe_toReal hy.ne (f_ne_bot y).ne', ← EReal.coe_toReal hxD'.ne (f_ne_bot x).ne']
    rw [ge_iff_le, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact this
  · rw [not_lt, top_le_iff] at hy
    rw [hy]; exact le_top

end FCA_chap_E_1_4_2
