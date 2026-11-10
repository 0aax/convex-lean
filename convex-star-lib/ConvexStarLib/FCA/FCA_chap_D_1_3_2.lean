import ConvexStarLib.Defs

/-!
# `FCA_chap_D_1_3_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_1_3_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_1_3_2`, so the main result is `FCA_chap_D_1_3_2.FCA_chap_D_1_3_2`.
-/

namespace FCA_chap_D_1_3_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_1_3_2 (f : E → ℝ) (x : E) (hf : ConvexOn ℝ Set.univ f) :
    let S := sublevelSetFun (liftRealtoEReal f) x
    posTangentConeAt S x ⊆ {d | directionalDeriv (liftRealtoEReal f) x d ≤ 0} := by
  intro S y hy
  obtain ⟨α, l, hl, c, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  haveI := hl
  set g : ℝ → ℝ := fun t => f (x + t • y) with hg_def
  have hg : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ μ ν hμ hν hμν
    have := hf.2 (Set.mem_univ (x + a • y)) (Set.mem_univ (x + b • y)) hμ hν hμν
    simp only [smul_eq_mul, hg_def]
    convert this using 2
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hμν, one_smul, smul_smul, smul_smul,
      add_smul]
  have hderiv := hg.hasDerivWithinAt_rightDeriv_of_mem_interior (x := 0) (by simp)
  set L := derivWithin g (Set.Ioi 0) 0 with hL_def
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hderiv
  have hq : ∀ t, slope g 0 t = (f (x + t • y) - f x) / t := by
    intro t
    simp [slope_def_field, hg_def]
  have hE : Filter.Tendsto (fun t => differenceQuotient (liftRealtoEReal f) x y t) (𝓝[>] 0)
      (𝓝 (L : EReal)) := by
    have : (fun t => differenceQuotient (liftRealtoEReal f) x y t)
        = fun t => ((slope g 0 t : ℝ) : EReal) := by
      funext t
      rw [hq]
      rfl
    rw [this]
    exact (continuous_coe_real_ereal.tendsto L).comp hderiv
  show directionalDeriv (liftRealtoEReal f) x y ≤ 0
  unfold directionalDeriv
  rw [hE.limUnder_eq]
  suffices L ≤ 0 by exact_mod_cast this
  obtain ⟨K, U, hU, hK⟩ := hf.locallyLipschitz x
  have hnear : ∀ v : E, ∀ᶠ s in 𝓝[>] (0:ℝ), x + s • v ∈ U := by
    intro v
    have : Filter.Tendsto (fun s : ℝ => x + s • v) (𝓝 0) (𝓝 x) := by
      have := ((continuous_const.add (continuous_id.smul continuous_const)).tendsto (0:ℝ) :
        Filter.Tendsto (fun s : ℝ => x + s • v) (𝓝 0) (𝓝 (x + (0:ℝ) • v)))
      simpa using this
    exact (this.mono_left nhdsWithin_le_nhds) hU
  have key : ∀ e : E, (∀ᶠ s in 𝓝[>] (0:ℝ), f (x + s • e) ≤ f x) → L ≤ K * ‖y - e‖ := by
    intro e he
    have h3 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s := self_mem_nhdsWithin
    refine le_of_tendsto hderiv ?_
    filter_upwards [hnear y, hnear e, h3, he] with s hs1 hs2 hs3 hs4
    rw [hq, div_le_iff₀ hs3]
    have h5 := hK.dist_le_mul _ hs1 _ hs2
    rw [Real.dist_eq, dist_eq_norm] at h5
    have h6 : ‖(x + s • y) - (x + s • e)‖ = s * ‖y - e‖ := by
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hs3.le]
    rw [h6] at h5
    have h7 := (abs_sub_le_iff.mp h5).1
    nlinarith
  have h4 : ∀ᶠ n in l, L ≤ K * ‖y - c n • d n‖ := by
    filter_upwards [hds] with n hn
    apply key
    have hn' : f (x + d n) ≤ f x := by
      exact EReal.coe_le_coe_iff.mp hn
    have h7 : ∀ᶠ s in 𝓝[>] (0:ℝ), s * (c n : ℝ) < 1 := by
      have : Filter.Tendsto (fun s : ℝ => s * (c n : ℝ)) (𝓝 0) (𝓝 0) := by
        have := ((continuous_id.mul continuous_const).tendsto (0:ℝ) :
          Filter.Tendsto (fun s : ℝ => s * (c n : ℝ)) (𝓝 0) (𝓝 ((0:ℝ) * (c n : ℝ))))
        simpa using this
      exact (this.mono_left nhdsWithin_le_nhds) (gt_mem_nhds zero_lt_one)
    have h8 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s := self_mem_nhdsWithin
    filter_upwards [h7, h8] with s hs7 hs8
    have hcn : (0:ℝ) ≤ c n := (c n).2
    have hconv : f ((1 - s * (c n : ℝ)) • x + (s * (c n : ℝ)) • (x + d n))
        ≤ (1 - s * (c n : ℝ)) • f x + (s * (c n : ℝ)) • f (x + d n) :=
      hf.2 (Set.mem_univ x) (Set.mem_univ (x + d n)) (by linarith) (by positivity) (by ring)
    have heq : x + s • (c n • d n) = (1 - s * (c n : ℝ)) • x + (s * (c n : ℝ)) • (x + d n) := by
      rw [NNReal.smul_def, smul_add, smul_smul, sub_smul, one_smul]
      abel
    rw [heq]
    simp only [smul_eq_mul] at hconv
    nlinarith [mul_nonneg (mul_nonneg hs8.le hcn) (sub_nonneg.mpr hn')]
  have h5 : Filter.Tendsto (fun n => (K : ℝ) * ‖y - c n • d n‖) l (𝓝 0) := by
    have : Filter.Tendsto (fun n => y - c n • d n) l (𝓝 0) := by
      have := (tendsto_const_nhds (x := y)).sub hcd
      simpa using this
    have := (this.norm).const_mul (K : ℝ)
    simpa using this
  exact ge_of_tendsto h5 h4

end FCA_chap_D_1_3_2
