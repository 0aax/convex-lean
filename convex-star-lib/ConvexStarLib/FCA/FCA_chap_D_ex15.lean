import ConvexStarLib.Defs

/-!
# `FCA_chap_D_ex15`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_ex15` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_ex15`, so the main result is `FCA_chap_D_ex15.FCA_chap_D_ex15`.
-/

namespace FCA_chap_D_ex15

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_ex15
  (f : E → ℝ)
  (x : E)
  (r : ℝ)
  (hf_convex : InConvRn (liftRealtoEReal f))
  (hr : r < f x) :
  let epi_f := epigraph (liftRealtoEReal f)
  ∃ (x' : E) (r' : ℝ),
    ((x', r') ∈ epi_f) ∧
    (∀ p ∈ epi_f, ‖x - x'‖ ^ 2 + (r - r') ^ 2 ≤ ‖x - p.1‖ ^ 2 + (r - p.2) ^ 2) ∧
    (f x' = r') ∧
    ((f x' - r)⁻¹ • (x - x') ∈ directionalSubdifferential (liftRealtoEReal f) x') := by
  intro epi_f
  -- membership in the epigraph
  have hmem : ∀ p : E × ℝ, p ∈ epi_f ↔ f p.1 ≤ p.2 := by
    intro p
    show ((f p.1 : EReal) ≤ (p.2 : EReal)) ↔ _
    exact EReal.coe_le_coe_iff
  -- convexity of f
  have hconv : ConvexOn ℝ Set.univ f := by
    rw [convexOn_iff_convex_epigraph]
    have h3 : Convex ℝ epi_f := hf_convex.2.2
    have e : {p : E × ℝ | p.1 ∈ Set.univ ∧ f p.1 ≤ p.2} = epi_f := by
      ext p
      rw [hmem p]
      simp
    rw [e]
    exact h3
  -- continuity of f, closedness of the epigraph
  have hcont : Continuous f := hconv.locallyLipschitz.continuous
  have hclosed : IsClosed epi_f := by
    have e : epi_f = {p : E × ℝ | f p.1 ≤ p.2} := by
      ext p
      exact hmem p
    rw [e]
    exact isClosed_le (hcont.comp continuous_fst) continuous_snd
  -- the objective
  let F : E × ℝ → ℝ := fun p => ‖x - p.1‖ ^ 2 + (r - p.2) ^ 2
  have hFcont : Continuous F := by fun_prop
  -- existence of a minimizer
  let K : Set (E × ℝ) := epi_f ∩ Metric.closedBall (x, r) (f x - r)
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_left hclosed
  have hp0 : (x, f x) ∈ K := by
    refine ⟨(hmem _).2 le_rfl, ?_⟩
    rw [Metric.mem_closedBall, Prod.dist_eq]
    show max (dist x x) (dist (f x) r) ≤ f x - r
    rw [_root_.dist_self, Real.dist_eq, abs_of_pos (by linarith)]
    exact max_le (by linarith) le_rfl
  obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn ⟨_, hp0⟩ hFcont.continuousOn
  have hFp0 : F (x, f x) = (f x - r) ^ 2 := by
    simp only [F, sub_self, norm_zero]
    ring
  have hmin : ∀ q ∈ epi_f, F p ≤ F q := by
    intro q hq
    by_cases hqK : q ∈ Metric.closedBall (x, r) (f x - r)
    · exact hpmin ⟨hq, hqK⟩
    · have h1 : F p ≤ F (x, f x) := hpmin hp0
      have h3 : (f x - r) ^ 2 < F q := by
        rw [Metric.mem_closedBall, not_le, Prod.dist_eq] at hqK
        have hnn1 : 0 ≤ ‖x - q.1‖ ^ 2 := by positivity
        have hnn2 : 0 ≤ (r - q.2) ^ 2 := by positivity
        rcases lt_max_iff.mp hqK with h | h
        · rw [dist_eq_norm, norm_sub_rev] at h
          have : (f x - r) ^ 2 < ‖x - q.1‖ ^ 2 := by nlinarith
          show (f x - r) ^ 2 < ‖x - q.1‖ ^ 2 + (r - q.2) ^ 2
          linarith
        · rw [Real.dist_eq] at h
          have e : (r - q.2) ^ 2 = |q.2 - r| ^ 2 := by
            rw [sq_abs]
            ring
          have : (f x - r) ^ 2 < |q.2 - r| ^ 2 := by nlinarith [abs_nonneg (q.2 - r)]
          show (f x - r) ^ 2 < ‖x - q.1‖ ^ 2 + (r - q.2) ^ 2
          linarith
      linarith
  obtain ⟨x', r'⟩ := p
  have hpmem : f x' ≤ r' := (hmem _).1 hpK.1
  -- variational inequality
  have hvar : ∀ y ρ, f y ≤ ρ →
      inner ℝ (x - x') (y - x') + (r - r') * (ρ - r') ≤ 0 := by
    intro y ρ hyρ
    by_contra hA
    push_neg at hA
    obtain ⟨A, hAdef⟩ : ∃ A, A = inner ℝ (x - x') (y - x') + (r - r') * (ρ - r') := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B, B = ‖y - x'‖ ^ 2 + (ρ - r') ^ 2 := ⟨_, rfl⟩
    rw [← hAdef] at hA
    have hB : 0 ≤ B := by rw [hBdef]; positivity
    have hAB : 0 < A + B := by linarith
    obtain ⟨θ, hθdef⟩ : ∃ θ, θ = A / (A + B) := ⟨_, rfl⟩
    have hθpos : 0 < θ := by rw [hθdef]; exact div_pos hA hAB
    have hθle : θ ≤ 1 := by rw [hθdef, div_le_one hAB]; linarith
    have hθeq : θ * (A + B) = A := by rw [hθdef]; field_simp
    have hmemθ : f (x' + θ • (y - x')) ≤ r' + θ * (ρ - r') := by
      have h := hconv.2 (Set.mem_univ x') (Set.mem_univ y) (by linarith : (0:ℝ) ≤ 1 - θ)
        hθpos.le (by ring)
      have e : (1 - θ) • x' + θ • y = x' + θ • (y - x') := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      rw [e] at h
      simp only [smul_eq_mul] at h
      nlinarith
    have hle := hmin (x' + θ • (y - x'), r' + θ * (ρ - r')) ((hmem _).2 hmemθ)
    simp only [F] at hle
    have e1 : x - (x' + θ • (y - x')) = (x - x') - θ • (y - x') := by abel
    have e2 : ‖(x - x') - θ • (y - x')‖ ^ 2 =
        ‖x - x'‖ ^ 2 - 2 * θ * inner ℝ (x - x') (y - x') + θ ^ 2 * ‖y - x'‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [e1, e2] at hle
    have h1 : 0 ≤ -2 * θ * A + θ ^ 2 * B := by
      rw [hAdef, hBdef]
      nlinarith [hle]
    have h2 : θ ^ 2 * B = θ * A - θ ^ 2 * A := by linear_combination θ * hθeq
    have h3 : 0 < θ * A := mul_pos hθpos hA
    have h4 : 0 < θ ^ 2 * A := mul_pos (pow_pos hθpos 2) hA
    linarith
  -- r < r'
  have hrr' : r < r' := by
    have h := hvar x' (r' + 1) (by linarith)
    simp only [sub_self, inner_zero_right, zero_add, add_sub_cancel_left, mul_one] at h
    rcases lt_or_eq_of_le (show r ≤ r' by linarith) with h' | h'
    · exact h'
    · exfalso
      have h2 := hvar x (f x) le_rfl
      rw [real_inner_self_eq_norm_sq, h', sub_self, zero_mul, add_zero] at h2
      have h3 : ‖x - x'‖ = 0 := by
        have := sq_nonneg ‖x - x'‖
        have h4 : ‖x - x'‖ ^ 2 = 0 := le_antisymm h2 this
        exact pow_eq_zero_iff (two_ne_zero) |>.1 h4
      have h5 : x = x' := sub_eq_zero.1 (norm_eq_zero.1 h3)
      rw [← h5] at hpmem
      linarith
  -- f x' = r'
  have hfx' : f x' = r' := by
    have h := hvar x' (f x') le_rfl
    simp only [sub_self, inner_zero_right, zero_add] at h
    by_contra hne
    have hlt : f x' < r' := lt_of_le_of_ne hpmem hne
    have : 0 < (r - r') * (f x' - r') := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    linarith
  -- subgradient inequality
  set s : E := (f x' - r)⁻¹ • (x - x') with hs
  have hpos : 0 < f x' - r := by rw [hfx']; linarith
  have hsub : ∀ y, inner ℝ s (y - x') ≤ f y - f x' := by
    intro y
    have h := hvar y (f y) le_rfl
    rw [hs, real_inner_smul_left, inv_mul_le_iff₀ hpos]
    rw [← hfx'] at h
    nlinarith
  refine ⟨x', r', hpK.1, fun q hq => hmin q hq, hfx', ?_⟩
  -- directional subdifferential
  intro d
  -- the real difference quotient
  let g : ℝ → ℝ := fun t => (f (x' + t • d) - f x') / t
  have hg_lb : ∀ t, 0 < t → inner ℝ s d ≤ g t := by
    intro t ht
    have h := hsub (x' + t • d)
    rw [add_sub_cancel_left, real_inner_smul_right] at h
    show inner ℝ s d ≤ (f (x' + t • d) - f x') / t
    rw [le_div_iff₀ ht]
    linarith
  have hg_mono : MonotoneOn g (Set.Ioi 0) := by
    intro t1 ht1 t2 ht2 h12
    simp only [Set.mem_Ioi] at ht1 ht2
    obtain ⟨a, hadef⟩ : ∃ a, a = t1 / t2 := ⟨_, rfl⟩
    have ha0 : 0 ≤ a := by rw [hadef]; positivity
    have ha1 : a ≤ 1 := by rw [hadef, div_le_one ht2]; exact h12
    have hat : a * t2 = t1 := by rw [hadef]; field_simp
    have h := hconv.2 (Set.mem_univ x') (Set.mem_univ (x' + t2 • d))
      (by linarith : (0:ℝ) ≤ 1 - a) ha0 (by ring)
    have e : (1 - a) • x' + a • (x' + t2 • d) = x' + t1 • d := by
      rw [← hat, mul_smul]
      simp only [sub_smul, one_smul, smul_add]
      abel
    rw [e] at h
    simp only [smul_eq_mul] at h
    show (f (x' + t1 • d) - f x') / t1 ≤ (f (x' + t2 • d) - f x') / t2
    rw [div_le_div_iff₀ ht1 ht2]
    have h' := mul_le_mul_of_nonneg_left h ht2.le
    have e2 : t2 * ((1 - a) * f x' + a * f (x' + t2 • d)) =
        (t2 - t1) * f x' + t1 * f (x' + t2 • d) := by
      rw [← hat]
      ring
    rw [e2] at h'
    nlinarith
  have hg_bdd : BddBelow (g '' Set.Ioi 0) := by
    refine ⟨inner ℝ s d, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hg_lb t ht
  have hg_tendsto := MonotoneOn.tendsto_nhdsGT hg_mono hg_bdd
  have hL : inner ℝ s d ≤ sInf (g '' Set.Ioi 0) := by
    apply le_csInf
    · exact ⟨g 1, 1, by norm_num, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hg_lb t ht
  have hT : Filter.Tendsto (fun t => differenceQuotient (liftRealtoEReal f) x' d t)
      (𝓝[>] 0) (𝓝 ((sInf (g '' Set.Ioi 0) : ℝ) : EReal)) := by
    have := EReal.tendsto_coe.2 hg_tendsto
    exact this
  show ((inner ℝ s d : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal f) x' d
  unfold directionalDeriv
  rw [hT.limUnder_eq]
  exact EReal.coe_le_coe_iff.2 hL

end FCA_chap_D_ex15
