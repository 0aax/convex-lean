import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_5_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_5_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_5_1`, so the main result is `FCA_chap_D_4_5_1.FCA_chap_D_4_5_1`.
-/

namespace FCA_chap_D_4_5_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma dirSubdiff_eq_of_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → ℝ) (hh : ConvexOn ℝ Set.univ h) (x : E) :
    directionalSubdifferential (liftRealtoEReal h) x
      = {s | ∀ z, inner ℝ s z ≤ h (x + z) - h x} := by
  have hq : ∀ d : E, ∀ t : ℝ, differenceQuotient (liftRealtoEReal h) x d t
      = (((h (x + t • d) - h x) / t : ℝ) : EReal) := by
    intro d t
    rfl
  have hmono : ∀ d : E, MonotoneOn (fun t => differenceQuotient (liftRealtoEReal h) x d t)
      (Set.Ioi 0) := by
    intro d t1 ht1 t2 ht2 h12
    simp only [hq]
    rw [EReal.coe_le_coe_iff]
    have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => h (x + t • d)) := by
      have := (hh.translate_right x).comp_linearMap (LinearMap.toSpanSingleton ℝ E d)
      simpa [Function.comp_def] using this
    have := hφ.secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ t1) (Set.mem_univ t2)
      (ne_of_gt ht1) (ne_of_gt ht2) h12
    simpa using this
  have hlim : ∀ d : E, directionalDeriv (liftRealtoEReal h) x d
      = sInf ((fun t => differenceQuotient (liftRealtoEReal h) x d t) '' Set.Ioi 0) := by
    intro d
    exact ((hmono d).tendsto_nhdsGT (OrderBot.bddBelow _)).limUnder_eq
  ext s
  simp only [directionalSubdifferential, Set.mem_setOf_eq]
  constructor
  · intro H z
    have h1 : (inner ℝ s z : EReal) ≤ directionalDeriv (liftRealtoEReal h) x z := H z
    rw [hlim z] at h1
    have h2 : (inner ℝ s z : EReal) ≤ differenceQuotient (liftRealtoEReal h) x z 1 :=
      h1.trans (sInf_le ⟨1, Set.mem_Ioi.mpr one_pos, rfl⟩)
    simp only [hq, EReal.coe_le_coe_iff] at h2
    simpa using h2
  · intro H d
    rw [hlim d]
    apply le_sInf
    rintro _ ⟨t, ht, rfl⟩
    simp only [hq]
    rw [EReal.coe_le_coe_iff]
    have := H (t • d)
    rw [inner_smul_right] at this
    rw [le_div_iff₀ ht]
    linarith

theorem FCA_chap_D_4_5_1 (g : F → ℝ)
    (A : F →ₗ[ℝ] E)
    (x : E)
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hg_bounded : BddBelow (Set.image g {y | A y = x}))
    (hA_surjective : Function.Surjective A) :
    let Ag := fun x => sInf (Set.image g {y | A y = x})
    let Yx := {y | (A y = x) ∧ (g y = Ag x)}
    (Set.Nonempty Yx) → ∀ y ∈ Yx,
    (directionalSubdifferential (liftRealtoEReal Ag) x =
    {s | A.adjoint s ∈ directionalSubdifferential (liftRealtoEReal g) y}) ∧
    (directionalSubdifferential (liftRealtoEReal Ag) x =
    Set.preimage A.adjoint (directionalSubdifferential (liftRealtoEReal g) y)) := by
  intro Ag Yx _ y hy
  obtain ⟨hAy, hgy⟩ := hy
  -- bounded below everywhere
  have hbdd : ∀ x' : E, BddBelow (g '' {y | A y = x'}) := by
    intro x'
    obtain ⟨m, hm⟩ := hg_bounded
    obtain ⟨y'', hy''⟩ := hA_surjective ((2:ℝ) • x - x')
    refine ⟨2 * m - g y'', ?_⟩
    rintro _ ⟨y', hy', rfl⟩
    simp only [Set.mem_setOf_eq] at hy'
    have h1 : A ((1/2:ℝ) • y' + (1/2:ℝ) • y'') = x := by
      rw [map_add, map_smul, map_smul, hy', hy'']
      module
    have h2 : m ≤ g ((1/2:ℝ) • y' + (1/2:ℝ) • y'') := hm ⟨_, h1, rfl⟩
    have h3 := hg_convex.2 (Set.mem_univ y') (Set.mem_univ y'') (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at h3
    linarith
  have hne : ∀ x' : E, (g '' {y | A y = x'}).Nonempty := by
    intro x'
    obtain ⟨y', hy'⟩ := hA_surjective x'
    exact ⟨g y', y', hy', rfl⟩
  have hAg_le : ∀ y' : F, Ag (A y') ≤ g y' := fun y' => csInf_le (hbdd _) ⟨y', rfl, rfl⟩
  have hconv : ConvexOn ℝ Set.univ Ag := by
    refine ⟨convex_univ, ?_⟩
    intro x1 _ x2 _ a b ha hb hab
    simp only [smul_eq_mul]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨_, ⟨y1, hy1, rfl⟩, hy1ε⟩ := Real.lt_sInf_add_pos (hne x1) hε
    obtain ⟨_, ⟨y2, hy2, rfl⟩, hy2ε⟩ := Real.lt_sInf_add_pos (hne x2) hε
    have hy1ε' : g y1 < Ag x1 + ε := hy1ε
    have hy2ε' : g y2 < Ag x2 + ε := hy2ε
    simp only [Set.mem_setOf_eq] at hy1 hy2
    have h1 : A (a • y1 + b • y2) = a • x1 + b • x2 := by
      rw [map_add, map_smul, map_smul, hy1, hy2]
    have h2 := hAg_le (a • y1 + b • y2)
    rw [h1] at h2
    have h3 := hg_convex.2 (Set.mem_univ y1) (Set.mem_univ y2) ha hb hab
    simp only [smul_eq_mul] at h3
    have h4 : a * g y1 ≤ a * (Ag x1 + ε) := mul_le_mul_of_nonneg_left hy1ε'.le ha
    have h5 : b * g y2 ≤ b * (Ag x2 + ε) := mul_le_mul_of_nonneg_left hy2ε'.le hb
    have h6 : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
    nlinarith
  have hAgx : Ag x = g y := hgy.symm
  rw [dirSubdiff_eq_of_convex Ag hconv x, dirSubdiff_eq_of_convex g hg_convex y]
  have key : {s | ∀ z, inner ℝ s z ≤ Ag (x + z) - Ag x} =
      {s | A.adjoint s ∈ {s' | ∀ w, inner ℝ s' w ≤ g (y + w) - g y}} := by
    ext s
    simp only [Set.mem_setOf_eq]
    constructor
    · intro H w
      rw [LinearMap.adjoint_inner_left]
      have h1 := H (A w)
      have h2 := hAg_le (y + w)
      rw [map_add, hAy] at h2
      linarith
    · intro H z
      rw [hAgx, le_sub_iff_add_le]
      apply le_csInf (hne _)
      rintro _ ⟨y', hy', rfl⟩
      simp only [Set.mem_setOf_eq] at hy'
      have h1 := H (y' - y)
      rw [LinearMap.adjoint_inner_left, map_sub, hy', hAy] at h1
      have e1 : x + z - x = z := by abel
      have e2 : y + (y' - y) = y' := by abel
      rw [e1, e2] at h1
      linarith
  exact ⟨key, key⟩

end FCA_chap_D_4_5_1
