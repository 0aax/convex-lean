import ConvexStarLib.Defs

/-!
# `Duchi_Q1_1`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_Q1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_Q1_1`, so the main result is `Duchi_Q1_1.Duchi_Q1_1`.
-/

namespace Duchi_Q1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Duchi_Q1_1 :
  (∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [UniformConvexSpace E] (C : Set E) (x : E),
      IsClosed C → Convex ℝ C → C.Nonempty →
      ∃! y, y ∈ projectionMapping C x) ∧
  (∀ (n : ℕ), 2 ≤ n →
    ∃ (C : Set (PiLp 1 (fun (_ : Fin n) => ℝ)))
      (x y₁ y₂ : PiLp 1 (fun (_ : Fin n) => ℝ)),
      IsClosed C ∧ Convex ℝ C ∧
      y₁ ≠ y₂ ∧ y₁ ∈ projectionMapping C x ∧ y₂ ∈ projectionMapping C x) ∧
  (∀ (n : ℕ), 2 ≤ n →
    ∃ (C : Set (PiLp ⊤ (fun (_ : Fin n) => ℝ)))
      (x y₁ y₂ : PiLp ⊤ (fun (_ : Fin n) => ℝ)),
      IsClosed C ∧ Convex ℝ C ∧
      y₁ ≠ y₂ ∧ y₁ ∈ projectionMapping C x ∧ y₂ ∈ projectionMapping C x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: existence and uniqueness of the projection in a uniformly convex Banach space.
    intro E _ _ _ _ C x hC hconv hne
    -- existence
    obtain ⟨y, hyC, hy⟩ : ∃ y ∈ C, ∀ z ∈ C, ‖y - x‖ ≤ ‖z - x‖ := by
      by_cases hxC : x ∈ C
      · exact ⟨x, hxC, fun z _ => by simp⟩
      set d := Metric.infDist x C with hd
      have hdpos : 0 < d := (hC.notMem_iff_infDist_pos hne).1 hxC
      have hd_le : ∀ z ∈ C, d ≤ ‖z - x‖ := fun z hz => by
        rw [← dist_eq_norm, _root_.dist_comm]; exact Metric.infDist_le_dist_of_mem hz
      have hseq : ∀ n : ℕ, ∃ z ∈ C, ‖z - x‖ < d + 1 / ((n : ℝ) + 1) := by
        intro n
        have h1 : Metric.infDist x C < d + 1 / ((n : ℝ) + 1) := by
          have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
        obtain ⟨z, hz, hdist⟩ := (Metric.infDist_lt_iff hne).1 h1
        exact ⟨z, hz, by rw [← dist_eq_norm, _root_.dist_comm]; exact hdist⟩
      choose u huC hu using hseq
      -- the minimizing sequence is Cauchy, by uniform convexity
      have hcauchy : CauchySeq u := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        obtain ⟨δ, hδ, hδprop⟩ :=
          exists_forall_closed_ball_dist_add_le_two_sub E (ε := ε / (d + 1)) (by positivity)
        set η : ℝ := min 1 (d * δ / 4) with hη_def
        have hη : 0 < η := by positivity
        have hη1 : η ≤ 1 := min_le_left _ _
        have hη2 : η ≤ d * δ / 4 := min_le_right _ _
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
        have hbound : ∀ m ≥ N, ‖u m - x‖ ≤ d + η := by
          intro m hm
          have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
            gcongr
          linarith [hu m]
        refine ⟨N, fun m hm n hn => ?_⟩
        by_contra hcon
        push_neg at hcon
        set R := d + η with hR_def
        have hR : 0 < R := by positivity
        have hum : ‖u m - x‖ ≤ R := hbound m hm
        have hun : ‖u n - x‖ ≤ R := hbound n hn
        set a := R⁻¹ • (u m - x) with ha_def
        set b := R⁻¹ • (u n - x) with hb_def
        have ha : ‖a‖ ≤ 1 := by
          rw [ha_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
          rw [inv_mul_le_iff₀ hR]; linarith
        have hb : ‖b‖ ≤ 1 := by
          rw [hb_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
          rw [inv_mul_le_iff₀ hR]; linarith
        have hab : ε / (d + 1) ≤ ‖a - b‖ := by
          have e1 : a - b = R⁻¹ • (u m - u n) := by
            rw [ha_def, hb_def, ← smul_sub]; congr 1; abel
          rw [e1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, ← dist_eq_norm]
          rw [div_le_iff₀ (by positivity)]
          calc ε ≤ dist (u m) (u n) := hcon
            _ = R⁻¹ * dist (u m) (u n) * R := by field_simp
            _ ≤ R⁻¹ * dist (u m) (u n) * (d + 1) := by
              gcongr
              linarith
        have hsum := hδprop ha hb hab
        have hmidC : (1/2 : ℝ) • u m + (1/2 : ℝ) • u n ∈ C :=
          hconv (huC m) (huC n) (by norm_num) (by norm_num) (by norm_num)
        have hmid := hd_le _ hmidC
        have e2 : (1/2 : ℝ) • u m + (1/2 : ℝ) • u n - x = (R / 2) • (a + b) := by
          rw [ha_def, hb_def, smul_add, smul_smul, smul_smul]
          have : R / 2 * R⁻¹ = 1 / 2 := by field_simp
          rw [this]
          module
        rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hmid
        have h3 : R / 2 * ‖a + b‖ ≤ R / 2 * (2 - δ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        nlinarith [mul_pos hdpos hδ, mul_pos hη hδ]
      obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
      have hyC : y ∈ C := hC.mem_of_tendsto hy (Filter.Eventually.of_forall huC)
      have hlim : Filter.Tendsto (fun n => ‖u n - x‖) Filter.atTop (𝓝 ‖y - x‖) :=
        (hy.sub_const x).norm
      have hlim' : Filter.Tendsto (fun n => ‖u n - x‖) Filter.atTop (𝓝 d) := by
        have h0 : Filter.Tendsto (fun n : ℕ => d + 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 d) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add d
          simpa using this
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
          (fun n => hd_le _ (huC n)) (fun n => (hu n).le)
      have hyd : ‖y - x‖ = d := tendsto_nhds_unique hlim hlim'
      exact ⟨y, hyC, fun z hz => hyd ▸ hd_le z hz⟩
    -- uniqueness, by strict convexity
    refine ⟨y, ⟨hyC, hy⟩, ?_⟩
    rintro w ⟨hwC, hw⟩
    by_contra hne'
    have h2 : ‖y - x‖ ≤ ‖w - x‖ := hy w hwC
    have hmid : (1/2 : ℝ) • w + (1/2 : ℝ) • y ∈ C :=
      hconv hwC hyC (by norm_num) (by norm_num) (by norm_num)
    have h3 := hw _ hmid
    have hne2 : w - x ≠ y - x := by
      intro h; apply hne'; simpa using h
    have h4 : ‖(1/2 : ℝ) • (w - x) + (1/2 : ℝ) • (y - x)‖ < ‖w - x‖ :=
      norm_combo_lt_of_ne le_rfl h2 hne2 (by norm_num) (by norm_num) (by norm_num)
    have h5 : (1/2 : ℝ) • (w - x) + (1/2 : ℝ) • (y - x) =
        ((1/2 : ℝ) • w + (1/2 : ℝ) • y) - x := by
      module
    rw [h5] at h4
    linarith
  · -- Part 2: non-uniqueness in `ℓ¹`; `C = {z | ∑ i, z i = 1}`, `x = 0`, `y₁ = e₀`, `y₂ = e₁`.
    intro n hn
    set i0 : Fin n := ⟨0, by omega⟩ with hi0
    set i1 : Fin n := ⟨1, by omega⟩ with hi1
    have hi : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    let C : Set (PiLp 1 (fun (_ : Fin n) => ℝ)) := {z | ∑ i, z i = 1}
    have key : ∀ z ∈ C, 1 ≤ ‖z‖ := by
      intro z hz
      have hz' : ∑ i, z i = 1 := hz
      rw [PiLp.norm_eq_of_L1]
      calc (1:ℝ) = ‖∑ i, z i‖ := by rw [hz']; simp
        _ ≤ ∑ i, ‖z i‖ := norm_sum_le _ _
    have hsingle : ∀ j : Fin n,
        (WithLp.toLp 1 (Pi.single j (1:ℝ)) : PiLp 1 (fun _ : Fin n => ℝ)) ∈
          projectionMapping C 0 := by
      intro j
      refine ⟨?_, ?_⟩
      · show ∑ i, (WithLp.toLp 1 (Pi.single j (1:ℝ)) : PiLp 1 (fun _ : Fin n => ℝ)) i = 1
        simp
      · intro z hz
        rw [sub_zero, sub_zero, PiLp.norm_toLp_single]
        simpa using key z hz
    refine ⟨C, 0, WithLp.toLp 1 (Pi.single i0 1), WithLp.toLp 1 (Pi.single i1 1), ?_, ?_, ?_,
      hsingle i0, hsingle i1⟩
    · apply isClosed_eq
      · exact continuous_finset_sum _ (fun i _ => PiLp.continuous_apply 1 _ i)
      · exact continuous_const
    · intro u hu v hv a b ha hb hab
      have hu' : ∑ i, u i = 1 := hu
      have hv' : ∑ i, v i = 1 := hv
      show ∑ i, (a • u + b • v) i = 1
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hu', hv']
      linarith
    · intro h
      have := congrArg (fun z : PiLp 1 (fun _ : Fin n => ℝ) => z i0) h
      simp [hi] at this
  · -- Part 3: non-uniqueness in `ℓ^∞`; `C = {z | z 0 = 1}`, `x = 0`, `y₁ = e₀`, `y₂ = 𝟙`.
    intro n hn
    set i0 : Fin n := ⟨0, by omega⟩ with hi0
    set i1 : Fin n := ⟨1, by omega⟩ with hi1
    have hi : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    haveI : Nonempty (Fin n) := ⟨i0⟩
    let C : Set (PiLp ⊤ (fun (_ : Fin n) => ℝ)) := {z | z i0 = 1}
    have key : ∀ z ∈ C, 1 ≤ ‖z‖ := by
      intro z hz
      have h1 := PiLp.norm_apply_le z i0
      have hz' : z i0 = 1 := hz
      rw [hz'] at h1
      simpa using h1
    refine ⟨C, 0, WithLp.toLp ⊤ (Pi.single i0 1), WithLp.toLp ⊤ (fun _ => 1), ?_, ?_, ?_, ?_, ?_⟩
    · exact isClosed_eq (PiLp.continuous_apply ⊤ _ i0) continuous_const
    · intro u hu v hv a b ha hb hab
      have hu' : u i0 = 1 := hu
      have hv' : v i0 = 1 := hv
      show (a • u + b • v) i0 = 1
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hu', hv']
      linarith
    · intro h
      have := congrArg (fun z : PiLp ⊤ (fun _ : Fin n => ℝ) => z i1) h
      simp [hi.symm] at this
    · refine ⟨?_, ?_⟩
      · show (WithLp.toLp ⊤ (Pi.single i0 (1:ℝ)) : PiLp ⊤ (fun _ : Fin n => ℝ)) i0 = 1
        simp
      · intro z hz
        rw [sub_zero, sub_zero, PiLp.norm_toLp_single]
        simpa using key z hz
    · refine ⟨?_, ?_⟩
      · show (WithLp.toLp ⊤ (fun _ => (1:ℝ)) : PiLp ⊤ (fun _ : Fin n => ℝ)) i0 = 1
        simp
      · intro z hz
        rw [sub_zero, sub_zero, PiLp.norm_toLp, pi_norm_const]
        simpa using key z hz

end Duchi_Q1_1
