import ConvexStarLib.Defs

/-!
# `FCA_chap_D_ex18`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_ex18` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_ex18`, so the main result is `FCA_chap_D_ex18.FCA_chap_D_ex18`.
-/

namespace FCA_chap_D_ex18

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_D_ex18
  (f : E → ℝ)
  (hf_convex : InConvRn (liftRealtoEReal f))
  (hf_pa : ∃ (m : ℕ) (a : ℕ → E) (b : ℕ → ℝ),
    (m > 0) ∧
    (∀ x, f x = sSup (Set.image (fun i => inner ℝ (a i) x + b i) (Finset.range m)))) :
  ∀ (x : E),
  ∃ ε > 0, ∀ x', (x' ∈ Metric.ball x ε) →
    directionalSubdifferential (liftRealtoEReal f) x' ⊆ directionalSubdifferential (liftRealtoEReal f) x := by
  obtain ⟨m, a, b, hm, hf⟩ := hf_pa
  have hfin : ∀ y : E,
      (Set.image (fun i => inner ℝ (a i) y + b i) (Finset.range m : Set ℕ)).Finite :=
    fun y => (Finset.finite_toSet _).image _
  have hne : ∀ y : E,
      (Set.image (fun i => inner ℝ (a i) y + b i) (Finset.range m : Set ℕ)).Nonempty :=
    fun y => ⟨_, Set.mem_image_of_mem _ (Finset.mem_range.2 hm)⟩
  have hle : ∀ y, ∀ i ∈ Finset.range m, inner ℝ (a i) y + b i ≤ f y := by
    intro y i hi
    rw [hf y]
    exact le_csSup (hfin y).bddAbove (Set.mem_image_of_mem _ hi)
  have hex : ∀ y, ∃ i ∈ Finset.range m, inner ℝ (a i) y + b i = f y := by
    intro y
    have := (hne y).csSup_mem (hfin y)
    rw [← hf y] at this
    obtain ⟨i, hi, hi'⟩ := this
    exact ⟨i, hi, hi'⟩
  have hub : ∀ y (c : ℝ), (∀ i ∈ Finset.range m, inner ℝ (a i) y + b i ≤ c) → f y ≤ c := by
    intro y c hc
    rw [hf y]
    apply csSup_le (hne y)
    rintro _ ⟨i, hi, rfl⟩
    exact hc i hi
  -- active set
  let I : E → Finset ℕ := fun y =>
    (Finset.range m).filter (fun i => inner ℝ (a i) y + b i = f y)
  have hI : ∀ y, (I y).Nonempty := by
    intro y
    obtain ⟨i, hi, hi'⟩ := hex y
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hi'⟩⟩
  let M : E → E → ℝ := fun y d => (I y).sup' (hI y) (fun i => inner ℝ (a i) d)
  have key : ∀ y d, ∀ᶠ t in 𝓝[>] (0:ℝ), f (y + t • d) = f y + t * M y d := by
    intro y d
    have h1 : ∀ i ∈ Finset.range m, ∀ᶠ t in 𝓝[>] (0:ℝ),
        inner ℝ (a i) (y + t • d) + b i ≤ f y + t * M y d := by
      intro i hi
      by_cases hiI : i ∈ I y
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have e1 : inner ℝ (a i) y + b i = f y := (Finset.mem_filter.1 hiI).2
        have e2 : inner ℝ (a i) d ≤ M y d := Finset.le_sup' (fun i => inner ℝ (a i) d) hiI
        have ht' : (0:ℝ) < t := ht
        have e3 := mul_le_mul_of_nonneg_left e2 ht'.le
        rw [inner_add_right, real_inner_smul_right]
        linarith
      · have hlt : inner ℝ (a i) y + b i < f y :=
          lt_of_le_of_ne (hle y i hi) (fun h => hiI (Finset.mem_filter.2 ⟨hi, h⟩))
        have hc1 : ContinuousAt (fun t : ℝ => inner ℝ (a i) (y + t • d) + b i) 0 := by
          fun_prop
        have hc2 : ContinuousAt (fun t : ℝ => f y + t * M y d) 0 := by
          fun_prop
        have := hc1.eventually_lt hc2 (by simpa using hlt)
        exact (this.filter_mono nhdsWithin_le_nhds).mono (fun t ht => ht.le)
    have h2 := (Finset.eventually_all (Finset.range m)).2 h1
    filter_upwards [h2, self_mem_nhdsWithin] with t ht ht0
    apply le_antisymm
    · exact hub _ _ ht
    · obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_sup' (hI y) (fun i => inner ℝ (a i) d)
      have h3 := hle (y + t • d) j (Finset.mem_filter.1 hj).1
      have e1 : inner ℝ (a j) y + b j = f y := (Finset.mem_filter.1 hj).2
      have e2 : M y d = inner ℝ (a j) d := hj'
      rw [inner_add_right, real_inner_smul_right] at h3
      rw [e2]
      linarith
  have hderiv : ∀ y d, directionalDeriv (liftRealtoEReal f) y d = (M y d : EReal) := by
    intro y d
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [key y d, self_mem_nhdsWithin] with t ht ht0
    have ht' : (0:ℝ) < t := ht0
    simp only [differenceQuotient, liftRealtoEReal]
    rw [← EReal.coe_sub, ← EReal.coe_div, ht]
    congr 1
    field_simp
    ring
  -- I x' ⊆ I x near x
  intro x
  have hloc : ∀ᶠ x' in 𝓝 x, ∀ i ∈ Finset.range m, i ∉ I x → i ∉ I x' := by
    rw [Finset.eventually_all]
    intro i hi
    by_cases hiI : i ∈ I x
    · exact Filter.Eventually.of_forall (fun _ h => absurd hiI h)
    · obtain ⟨j, hj⟩ := hI x
      have e1 : inner ℝ (a j) x + b j = f x := (Finset.mem_filter.1 hj).2
      have hlt : inner ℝ (a i) x + b i < f x :=
          lt_of_le_of_ne (hle x i hi) (fun h => hiI (Finset.mem_filter.2 ⟨hi, h⟩))
      have hc1 : ContinuousAt (fun y : E => inner ℝ (a i) y + b i) x := by fun_prop
      have hc2 : ContinuousAt (fun y : E => inner ℝ (a j) y + b j) x := by fun_prop
      have := hc1.eventually_lt hc2
        (show inner ℝ (a i) x + b i < inner ℝ (a j) x + b j by linarith)
      filter_upwards [this] with x' hx' _ hmem
      have e3 : inner ℝ (a i) x' + b i = f x' := (Finset.mem_filter.1 hmem).2
      have := hle x' j (Finset.mem_filter.1 hj).1
      linarith
  obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.1 hloc
  refine ⟨ε, hε, fun x' hx' s hs => ?_⟩
  have hsub : I x' ⊆ I x := by
    intro i hi
    by_contra hcon
    exact hε' (Metric.mem_ball.1 hx') i (Finset.mem_filter.1 hi).1 hcon hi
  simp only [directionalSubdifferential, Set.mem_setOf_eq] at hs ⊢
  intro d
  have h1 := hs d
  rw [hderiv] at h1 ⊢
  calc ((inner ℝ s d : ℝ) : EReal) ≤ (M x' d : EReal) := h1
    _ ≤ (M x d : EReal) := by
      exact_mod_cast Finset.sup'_mono (fun i => inner ℝ (a i) d) hsub (hI x')

end FCA_chap_D_ex18
