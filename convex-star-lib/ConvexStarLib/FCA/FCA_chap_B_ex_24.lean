import ConvexStarLib.Defs

/-!
# `FCA_chap_B_ex_24`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_ex_24` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_ex_24`, so the main result is `FCA_chap_B_ex_24.FCA_chap_B_ex_24`.
-/

namespace FCA_chap_B_ex_24

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_ex_24
  (k : ℕ)
  (s : ℕ → E)
  (r : ℕ → ℝ)
  (hk : k ≥ 1)
  :
  let f := fun x => sSup (Set.image (fun i => inner ℝ (s i) x + r i) (Finset.range k))
  ∀ (d : E),
  asymptoticFun (liftRealtoEReal f) d =
  sSup (Set.image (fun i => inner ℝ (s i) d) (Finset.range k)) := by
  intro f d
  have hf_def : ∀ x, f x = sSup ((fun i => inner ℝ (s i) x + r i) '' ↑(Finset.range k)) :=
    fun x => rfl
  have hne : (Finset.range k).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨i₀, hi₀, hmax⟩ :=
    Finset.exists_max_image (Finset.range k) (fun i => inner ℝ (s i) d) hne
  obtain ⟨j₀, hj₀, hrmax⟩ := Finset.exists_max_image (Finset.range k) r hne
  have hf_ge : ∀ x, ∀ i ∈ Finset.range k, inner ℝ (s i) x + r i ≤ f x := by
    intro x i hi
    rw [hf_def]
    apply le_csSup
    · exact ((Finset.finite_toSet _).image _).bddAbove
    · exact ⟨i, hi, rfl⟩
  have hf_le : ∀ x c, (∀ i ∈ Finset.range k, inner ℝ (s i) x + r i ≤ c) → f x ≤ c := by
    intro x c hc
    rw [hf_def]
    apply csSup_le
    · exact (Finset.coe_nonempty.mpr hne).image _
    · rintro _ ⟨i, hi, rfl⟩
      exact hc i hi
  set M := inner ℝ (s i₀) d with hM
  -- (A) lower bound
  have hA : ∀ t, (d, t) ∈ horizonCone (epigraph (liftRealtoEReal f)) →
      ∀ i ∈ Finset.range k, inner ℝ (s i) d ≤ t := by
    rintro t ⟨xseq, l, hx, hl, hlim⟩ i hi
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := hl.mono_right nhdsWithin_le_nhds
    have hlpos : ∀ᶠ n in Filter.atTop, l n ∈ Set.Ioi (0:ℝ) := hl.eventually self_mem_nhdsWithin
    have h1 : Filter.Tendsto (fun n => l n • (xseq n).1) Filter.atTop (𝓝 d) :=
      (continuous_fst.tendsto _).comp hlim
    have h2 : Filter.Tendsto (fun n => l n * (xseq n).2) Filter.atTop (𝓝 t) :=
      (continuous_snd.tendsto _).comp hlim
    have h3 : Filter.Tendsto (fun n => inner ℝ (s i) (l n • (xseq n).1) + l n * r i)
        Filter.atTop (𝓝 (inner ℝ (s i) d + 0 * r i)) :=
      (tendsto_const_nhds.inner h1).add (hl0.mul_const _)
    have key : inner ℝ (s i) d + 0 * r i ≤ t := by
      apply le_of_tendsto_of_tendsto h3 h2
      filter_upwards [hlpos] with n hn
      have hn' : (0:ℝ) < l n := hn
      have h' : f (xseq n).1 ≤ (xseq n).2 := by
        have := hx n
        unfold epigraph liftRealtoEReal at this
        exact EReal.coe_le_coe_iff.mp this
      have h'' : inner ℝ (s i) (xseq n).1 + r i ≤ (xseq n).2 := by
        linarith [hf_ge (xseq n).1 i hi]
      rw [real_inner_smul_right]
      nlinarith
    simpa using key
  -- (B) membership
  have hB : (d, M) ∈ horizonCone (epigraph (liftRealtoEReal f)) := by
    refine ⟨fun n => (((n:ℝ)+1) • d, ((n:ℝ)+1) * M + r j₀), fun n => 1 / ((n:ℝ)+1),
      ?_, ?_, ?_⟩
    · intro n
      show ((f (((n:ℝ)+1) • d) : ℝ) : EReal) ≤ ((((n:ℝ)+1) * M + r j₀ : ℝ) : EReal)
      rw [EReal.coe_le_coe_iff]
      apply hf_le
      intro i hi
      rw [real_inner_smul_right]
      have h1 := hmax i hi
      have h2 := hrmax i hi
      have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
      simp only at h1
      nlinarith
    · apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      filter_upwards with n
      simp only [Set.mem_Ioi]
      positivity
    · have : ∀ n : ℕ, (1 / ((n:ℝ)+1)) • (((n:ℝ)+1) • d, ((n:ℝ)+1) * M + r j₀)
          = (d, M + r j₀ * (1 / ((n:ℝ)+1))) := by
        intro n
        have hn : ((n:ℝ)+1) ≠ 0 := by positivity
        ext
        · simp [smul_smul, hn]
        · simp only [Prod.smul_snd, smul_eq_mul]
          field_simp
      simp_rw [this]
      apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (r j₀)
      simpa using this.const_add M
  -- conclude
  have hRHS : sSup ((fun i => inner ℝ (s i) d) '' ↑(Finset.range k)) = M := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨i₀, hi₀, rfl⟩, ?_⟩
    rintro _ ⟨i, hi, rfl⟩
    exact hmax i hi
  rw [hRHS]
  unfold asymptoticFun funFromSet
  apply IsLeast.csInf_eq
  refine ⟨⟨M, hB, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (hA t ht i₀ hi₀)

end FCA_chap_B_ex_24
