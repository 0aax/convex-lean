import ConvexStarLib.Defs

/-!
# `FCA_chap_C_ex3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_ex3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_ex3`, so the main result is `FCA_chap_C_ex3.FCA_chap_C_ex3`.
-/

namespace FCA_chap_C_ex3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Multiplication by a positive real, as an order isomorphism of `EReal`. -/
noncomputable def FCA_mulPosIso (t : ℝ) (ht : 0 < t) : EReal ≃o EReal :=
  Equiv.toOrderIso
    { toFun := fun a => (t : EReal) * a
      invFun := fun a => ((t⁻¹ : ℝ) : EReal) * a
      left_inv := fun a => by
        simp only
        rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ht.ne', EReal.coe_one, one_mul]
      right_inv := fun a => by
        simp only
        rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht.ne', EReal.coe_one, one_mul] }
    (fun a b hab => mul_le_mul_of_nonneg_left hab (by exact_mod_cast ht.le))
    (fun a b hab => mul_le_mul_of_nonneg_left hab (by exact_mod_cast (inv_pos.mpr ht).le))

theorem FCA_mulPosIso_apply (t : ℝ) (ht : 0 < t) (a : EReal) :
    FCA_mulPosIso t ht a = (t : EReal) * a := rfl

theorem FCA_mulPosIso_symm_apply (t : ℝ) (ht : 0 < t) (a : EReal) :
    (FCA_mulPosIso t ht).symm a = ((t⁻¹ : ℝ) : EReal) * a := rfl

theorem FCA_lscHull_lsc {X : Type*} [TopologicalSpace X] (g : X → EReal) :
    LowerSemicontinuous (lscHull g) := by
  intro x y hy
  obtain ⟨z, hyz, hz⟩ := exists_between hy
  have h1 : ∀ᶠ w in 𝓝 x, z < g w := Filter.eventually_lt_of_lt_liminf hz
  rw [← eventually_eventually_nhds] at h1
  filter_upwards [h1] with x' hx'
  exact lt_of_lt_of_le hyz (Filter.le_liminf_of_le (by isBoundedDefault) (hx'.mono fun w hw => hw.le))

theorem FCA_lscHull_le {X : Type*} [TopologicalSpace X] (g : X → EReal) (x : X) :
    lscHull g x ≤ g x :=
  Filter.liminf_le_of_le (by isBoundedDefault) (fun _ hb => hb.self_of_nhds)

theorem FCA_epigraph_lscHull {X : Type*} [PseudoMetricSpace X] (g : X → EReal) :
    epigraph (lscHull g) = closure (epigraph g) := by
  apply Set.Subset.antisymm
  · rintro ⟨x, r⟩ hxr
    rw [Metric.mem_closure_iff]
    intro ε hε
    have h1 : lscHull g x < ((r + ε / 2 : ℝ) : EReal) :=
      lt_of_le_of_lt hxr (EReal.coe_lt_coe_iff.mpr (by linarith))
    have h2 : ∃ᶠ y in 𝓝 x, g y < ((r + ε / 2 : ℝ) : EReal) :=
      Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) h1
    obtain ⟨y, hy1, hy2⟩ := (h2.and_eventually (Metric.ball_mem_nhds x hε)).exists
    refine ⟨(y, r + ε / 2), hy1.le, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [_root_.dist_comm]; exact hy2
    · simp only [Real.dist_eq]
      rw [abs_lt]; constructor <;> linarith
  · apply closure_minimal
    · intro p hp
      exact le_trans (FCA_lscHull_le g p.1) hp
    · have hc : IsClosed {q : X × EReal | lscHull g q.1 ≤ q.2} :=
        (FCA_lscHull_lsc g).isClosed_epigraph
      exact hc.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

theorem FCA_convex_epigraph_funFromSet {X : Type*} [AddCommGroup X] [Module ℝ X]
    {C : Set (X × ℝ)} (hC : Convex ℝ C) : Convex ℝ (epigraph (funFromSet C)) := by
  intro p hp q hq a b ha hb hab
  simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hp hq ⊢
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  have hz' : a * p.2 + b * q.2 < z := EReal.coe_lt_coe_iff.mp hz
  set ε := z - (a * p.2 + b * q.2) with hε
  have hεpos : 0 < ε := by linarith
  obtain ⟨_, ⟨s1, hs1, rfl⟩, hs1lt⟩ := sInf_lt_iff.mp
    (lt_of_le_of_lt hp (EReal.coe_lt_coe_iff.mpr (by linarith : p.2 < p.2 + ε)))
  obtain ⟨_, ⟨s2, hs2, rfl⟩, hs2lt⟩ := sInf_lt_iff.mp
    (lt_of_le_of_lt hq (EReal.coe_lt_coe_iff.mpr (by linarith : q.2 < q.2 + ε)))
  have hs1lt' : s1 < p.2 + ε := EReal.coe_lt_coe_iff.mp hs1lt
  have hs2lt' : s2 < q.2 + ε := EReal.coe_lt_coe_iff.mp hs2lt
  have hmem : (a • p.1 + b • q.1, a * s1 + b * s2) ∈ C := by
    have := hC hs1 hs2 ha hb hab
    simpa using this
  have h3 : funFromSet C (a • p.1 + b • q.1) ≤ ((a * s1 + b * s2 : ℝ) : EReal) :=
    sInf_le ⟨_, hmem, rfl⟩
  refine le_trans h3 (EReal.coe_le_coe_iff.mpr ?_)
  nlinarith [mul_le_mul_of_nonneg_left hs1lt'.le ha, mul_le_mul_of_nonneg_left hs2lt'.le hb]


theorem FCA_le_clco {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f ψ : X → EReal) (hψl : LowerSemicontinuous ψ)
    (hψc : Convex ℝ (epigraph ψ)) (hψf : ∀ x, ψ x ≤ f x) (x : X) :
    ψ x ≤ lscHull (convexHullFun f) x := by
  have h1 : convexHull ℝ (epigraph f) ⊆ epigraph ψ :=
    convexHull_min (fun p hp => le_trans (hψf p.1) hp) hψc
  have h2 : ∀ y, ψ y ≤ convexHullFun f y := by
    intro y
    apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    exact h1 hr
  calc ψ x ≤ Filter.liminf ψ (𝓝 x) := hψl.le_liminf x
    _ ≤ Filter.liminf (convexHullFun f) (𝓝 x) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall h2)

theorem FCA_cHF_le_homog {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (hf : IsERealPosHomogeneous f) (t : ℝ) (ht : 0 < t)
    (x : X) : convexHullFun f (t • x) ≤ (t : EReal) * convexHullFun f x := by
  have hcone : ∀ p ∈ convexHull ℝ (epigraph f), t • p ∈ convexHull ℝ (epigraph f) := by
    intro p hp
    have hsub : epigraph f ⊆ (fun z => t • z) ⁻¹' convexHull ℝ (epigraph f) := by
      intro q hq
      apply subset_convexHull ℝ (epigraph f)
      show f (t • q.1) ≤ ((t * q.2 : ℝ) : EReal)
      rw [hf q.1 t ht, EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left hq (by exact_mod_cast ht.le)
    exact convexHull_min hsub ((convex_convexHull ℝ _).smul_preimage t) hp
  rw [← FCA_mulPosIso_apply t ht, ← OrderIso.symm_apply_le]
  apply le_sInf
  rintro _ ⟨s, hs, rfl⟩
  rw [OrderIso.symm_apply_le, FCA_mulPosIso_apply, ← EReal.coe_mul]
  apply sInf_le
  refine ⟨t * s, ?_, rfl⟩
  have := hcone _ hs
  simpa using this

theorem FCA_cHF_homog {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (hf : IsERealPosHomogeneous f) (t : ℝ) (ht : 0 < t)
    (x : X) : convexHullFun f (t • x) = (t : EReal) * convexHullFun f x := by
  apply le_antisymm (FCA_cHF_le_homog f hf t ht x)
  have h := FCA_cHF_le_homog f hf t⁻¹ (inv_pos.mpr ht) (t • x)
  rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, ← FCA_mulPosIso_symm_apply t ht,
    OrderIso.le_symm_apply] at h
  exact h

theorem FCA_lscHull_homog {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (g : X → EReal) (hg : ∀ (y : X) (t : ℝ), 0 < t → g (t • y) = (t : EReal) * g y)
    (t : ℝ) (ht : 0 < t) (x : X) : lscHull g (t • x) = (t : EReal) * lscHull g x := by
  unfold lscHull
  have hmap : Filter.map (fun y => t • y) (𝓝 x) = 𝓝 (t • x) :=
    (Homeomorph.smulOfNeZero t ht.ne').map_nhds_eq x
  rw [← hmap, ← Filter.liminf_comp, ← FCA_mulPosIso_apply t ht, OrderIso.liminf_apply]
  congr 1
  funext y
  exact hg y t ht

theorem FCA_cHF_le {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] (f : X → EReal)
    (y : X) : convexHullFun f y ≤ f y := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  apply sInf_le
  exact ⟨z, subset_convexHull ℝ _ (show f y ≤ (z : EReal) from hz.le), rfl⟩


set_option linter.unusedVariables false in
theorem FCA_chap_C_ex3
  (f : E → EReal)
  (hf_pos_homog : IsERealPosHomogeneous f)
  (hf_nondegenerate : IsNondegenerate f)
  (hfinite : ∀ x, lscHull ((convexHullFun f)) x < ⊤)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let clco_f := lscHull ((convexHullFun f))
  let sup_minorized := fun x => sSup {v | ∃ (σ : E → ℝ),
                                (LowerSemicontinuous (liftRealtoEReal σ)) ∧
                                (IsSublinear (liftRealtoEReal σ)) ∧
                                (∀ x, σ x ≤ f x) ∧
                                (v = σ x)}
  ∀ x, clco_f x = sup_minorized x := by
  intro clco_f sup_minorized x
  obtain ⟨_, ⟨s, b, hsb⟩⟩ := hf_nondegenerate
  -- an affine minorant of `f` gives a lower bound on `clco_f`
  have hlow : ∀ y, ((inner ℝ s y - b : ℝ) : EReal) ≤ clco_f y := by
    intro y
    apply FCA_le_clco f (fun y => ((inner ℝ s y - b : ℝ) : EReal))
    · exact (continuous_coe_real_ereal.comp
        ((continuous_const.inner continuous_id).sub continuous_const)).lowerSemicontinuous
    · intro p hp q hq α β hα hβ hαβ
      simp only [epigraph, Set.mem_setOf_eq, EReal.coe_le_coe_iff, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, inner_add_right, inner_smul_right] at hp hq ⊢
      have h1 := mul_le_mul_of_nonneg_left hp hα
      have h2 := mul_le_mul_of_nonneg_left hq hβ
      have h3 : α * b + β * b = b := by rw [← add_mul, hαβ, one_mul]
      nlinarith [h1, h2, h3]
    · intro z
      rw [EReal.coe_sub]
      exact hsb z
  have hbot : ∀ y, ⊥ < clco_f y := fun y => lt_of_lt_of_le (EReal.bot_lt_coe _) (hlow y)
  have hfin : ∀ y, ((clco_f y).toReal : EReal) = clco_f y :=
    fun y => EReal.coe_toReal (hfinite y).ne (hbot y).ne'
  set σ : E → ℝ := fun y => (clco_f y).toReal with hσ
  have hlift : liftRealtoEReal σ = clco_f := funext fun y => hfin y
  have hconv : ConvexEReal clco_f := by
    show Convex ℝ (epigraph (lscHull (convexHullFun f)))
    rw [FCA_epigraph_lscHull]
    exact (FCA_convex_epigraph_funFromSet (convex_convexHull ℝ (epigraph f))).closure
  have hhom : IsERealPosHomogeneous clco_f := fun y t ht =>
    FCA_lscHull_homog (convexHullFun f) (fun z τ hτ => FCA_cHF_homog f hf_pos_homog τ hτ z) t ht y
  have hmem : σ x ∈ {v | ∃ (σ : E → ℝ),
                                (LowerSemicontinuous (liftRealtoEReal σ)) ∧
                                (IsSublinear (liftRealtoEReal σ)) ∧
                                (∀ x, σ x ≤ f x) ∧
                                (v = σ x)} := by
    refine ⟨σ, ?_, ?_, ?_, rfl⟩
    · rw [hlift]; exact FCA_lscHull_lsc _
    · rw [hlift]; exact ⟨⟨hbot, ⟨x, hfinite x⟩, hconv⟩, hhom⟩
    · intro y
      show ((clco_f y).toReal : EReal) ≤ f y
      rw [hfin y]
      exact (FCA_lscHull_le _ y).trans (FCA_cHF_le f y)
  have hub : ∀ v ∈ {v | ∃ (σ : E → ℝ),
                                (LowerSemicontinuous (liftRealtoEReal σ)) ∧
                                (IsSublinear (liftRealtoEReal σ)) ∧
                                (∀ x, σ x ≤ f x) ∧
                                (v = σ x)}, v ≤ σ x := by
    rintro v ⟨τ, hτl, hτs, hτf, rfl⟩
    have h : liftRealtoEReal τ x ≤ clco_f x := FCA_le_clco f (liftRealtoEReal τ) hτl hτs.1.2.2 hτf x
    rw [← hfin x] at h
    exact EReal.coe_le_coe_iff.mp h
  have hsup : sup_minorized x = σ x := IsGreatest.csSup_eq ⟨hmem, hub⟩
  show clco_f x = ((sup_minorized x : ℝ) : EReal)
  rw [hsup]
  exact (hfin x).symm

end FCA_chap_C_ex3
