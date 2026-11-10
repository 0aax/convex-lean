import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_2_6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_2_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_2_6`, so the main result is `FCA_chap_B_1_2_6.FCA_chap_B_1_2_6`.
-/

namespace FCA_chap_B_1_2_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_B_1_2_6
  (f : E → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let cl_f := lscHull f
  InConvRn cl_f ∧
    ∀ x ∈ intrinsicInterior ℝ (effDom f), cl_f x = f x := by
  intro cl_f
  obtain ⟨hbot, ⟨x₀, hx₀⟩, hconv⟩ := hf_convex
  have hconv' : Convex ℝ (epigraph f) := hconv
  -- convexity in usable form
  have hconvf : ∀ (x y : E) (a b s t : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      f x ≤ s → f y ≤ t → f (a • x + b • y) ≤ ((a * s + b * t : ℝ) : EReal) := by
    intro x y a b s t ha hb hab hx hy
    have := hconv' (show (x, s) ∈ epigraph f from hx) (show (y, t) ∈ epigraph f from hy) ha hb hab
    simpa [epigraph] using this
  -- finite values on the effective domain
  have hfin : ∀ x ∈ effDom f, f x = ((f x).toReal : EReal) := by
    intro x hx
    exact (EReal.coe_toReal (ne_of_lt hx) (ne_of_gt (hbot x))).symm
  have htop : ∀ x, x ∉ effDom f → f x = ⊤ := by
    intro x hx
    simpa [effDom] using hx
  -- cl_f ≤ f
  have hle : ∀ x, cl_f x ≤ f x := by
    intro x
    exact Filter.liminf_le_of_frequently_le'
      (Filter.frequently_iff.2 fun hU => ⟨x, mem_of_mem_nhds hU, le_rfl⟩)
  -- epigraph of cl_f is the closure of the epigraph of f
  have hepi : epigraph cl_f = closure (epigraph f) := by
    ext ⟨x, r⟩
    constructor
    · intro hx
      rw [Metric.mem_closure_iff]
      intro ε hε
      have h1 : cl_f x < ((r + ε / 2 : ℝ) : EReal) := by
        have : (r : EReal) < ((r + ε / 2 : ℝ) : EReal) := by
          exact_mod_cast (by linarith : r < r + ε / 2)
        exact lt_of_le_of_lt hx this
      have h2 : ∃ᶠ y in 𝓝 x, f y < ((r + ε / 2 : ℝ) : EReal) :=
        Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) h1
      obtain ⟨y, hy1, hy2⟩ := (h2.and_eventually (Metric.ball_mem_nhds x hε)).exists
      refine ⟨(y, r + ε / 2), le_of_lt hy1, ?_⟩
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · rw [_root_.dist_comm]; exact hy2
      · simp only
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
    · intro hx
      show cl_f x ≤ (r : EReal)
      by_contra hcon
      push_neg at hcon
      obtain ⟨r', hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      have h1 : ∀ᶠ y in 𝓝 x, (r' : EReal) < f y :=
        Filter.eventually_lt_of_lt_liminf hr2
      have h2 : ∀ᶠ s in 𝓝 r, s < r' := eventually_lt_nhds (by exact_mod_cast hr1)
      have h3 := h1.prod_nhds h2
      rw [mem_closure_iff_frequently] at hx
      obtain ⟨⟨y, s⟩, hys, hy, hs⟩ := (hx.and_eventually h3).exists
      have hys' : f y ≤ (s : EReal) := hys
      have hs' : (s : EReal) < r' := by exact_mod_cast hs
      exact lt_irrefl _ (hy.trans_le (hys'.trans hs'.le))
  have hcl_conv : ConvexEReal cl_f := by
    unfold ConvexEReal
    rw [hepi]
    exact hconv'.closure
  set D := effDom f with hD
  set A := affineSpan ℝ D with hA
  -- convexity of D
  have hDconv : Convex ℝ D := by
    intro x hx y hy a b ha hb hab
    have := hconvf x y a b (f x).toReal (f y).toReal ha hb hab (hfin x hx).le (hfin y hy).le
    show f (a • x + b • y) < ⊤
    exact lt_of_le_of_lt this (EReal.coe_lt_top _)
  have key : ∀ z ∈ intrinsicInterior ℝ D, ∀ ε > 0, ∃ δ > 0, ∀ w ∈ A, dist w z < δ →
      w ∈ D ∧ |(f w).toReal - (f z).toReal| < ε := by
    intro z hz ε hε
    have hzD : z ∈ D := intrinsicInterior_subset hz
    have hzA : z ∈ A := subset_affineSpan ℝ D hzD
    -- Step 1: a ball around z within A is in D
    obtain ⟨ε₀, hε₀, hball⟩ : ∃ ε₀ > 0, ∀ w ∈ A, dist w z < ε₀ → w ∈ D := by
      rw [mem_intrinsicInterior] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
      obtain ⟨ε₀, hε₀, hsub⟩ := hy
      refine ⟨ε₀, hε₀, fun w hw hdist => ?_⟩
      have : (⟨w, hw⟩ : A) ∈ Metric.ball y ε₀ := by
        rw [Metric.mem_ball, Subtype.dist_eq]; exact hdist
      exact hsub this
    -- Step 2: the function on the direction
    let V := A.direction
    let C : Set V := {v | (v : E) + z ∈ D}
    let g : V → ℝ := fun v => (f ((v : E) + z)).toReal
    have hCconv : Convex ℝ C := by
      intro v hv u hu a b ha hb hab
      show ((a • v + b • u : V) : E) + z ∈ D
      have := hDconv hv hu ha hb hab
      convert this using 1
      simp only [Submodule.coe_add, Submodule.coe_smul]
      rw [smul_add, smul_add]
      have : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
      nth_rewrite 1 [this]
      abel
    have hg : ConvexOn ℝ C g := by
      refine ⟨hCconv, ?_⟩
      intro v hv u hu a b ha hb hab
      have hvD : (v : E) + z ∈ D := hv
      have huD : (u : E) + z ∈ D := hu
      have h1 := hconvf _ _ a b _ _ ha hb hab (hfin _ hvD).le (hfin _ huD).le
      have h2 : ((a • v + b • u : V) : E) + z = a • ((v : E) + z) + b • ((u : E) + z) := by
        simp only [Submodule.coe_add, Submodule.coe_smul]
        rw [smul_add, smul_add]
        have : z = a • z + b • z := by rw [← add_smul, hab, one_smul]
        nth_rewrite 1 [this]
        abel
      have h3 : ((a • v + b • u : V) : E) + z ∈ D := hCconv hv hu ha hb hab
      show (f (((a • v + b • u : V) : E) + z)).toReal ≤ a • g v + b • g u
      rw [h2] at h3 ⊢
      rw [hfin _ h3] at h1
      simp only [smul_eq_mul, g]
      exact_mod_cast h1
    have h0C : C ∈ 𝓝 (0 : V) := by
      rw [Metric.mem_nhds_iff]
      refine ⟨ε₀, hε₀, fun v hv => ?_⟩
      show (v : E) + z ∈ D
      apply hball
      · exact AffineSubspace.vadd_mem_of_mem_direction v.2 hzA
      · rw [dist_eq_norm, add_sub_cancel_right]
        rw [Metric.mem_ball, _root_.dist_zero_right] at hv
        exact hv
    have hcont : ContinuousAt g 0 :=
      hg.continuousOn_interior.continuousAt (interior_mem_nhds.2 h0C)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ₁, hδ₁, hδ⟩ := hcont ε hε
    refine ⟨min δ₁ ε₀, lt_min hδ₁ hε₀, fun w hw hdist => ?_⟩
    have hwD : w ∈ D := hball w hw (lt_of_lt_of_le hdist (min_le_right _ _))
    refine ⟨hwD, ?_⟩
    have hv : w - z ∈ V := by
      have := AffineSubspace.vsub_mem_direction hw hzA
      simpa using this
    have := hδ (x := ⟨w - z, hv⟩) (by
      rw [_root_.dist_zero_right]
      show ‖w - z‖ < δ₁
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le hdist (min_le_left _ _))
    simp only [g, Real.dist_eq] at this
    simpa using this
  -- a point in the relative interior and an upper bound near it
  obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior hDconv ⟨x₀, hx₀⟩
  have hzD : z ∈ D := intrinsicInterior_subset hz
  have hzA : z ∈ A := subset_affineSpan ℝ D hzD
  obtain ⟨δ, hδ, hbd⟩ := key z hz 1 one_pos
  set rz := (f z).toReal with hrz
  have hfz : f z = rz := hfin z hzD
  have hM : ∀ w ∈ A, dist w z < δ → f w ≤ ((rz + 1 : ℝ) : EReal) := by
    intro w hw hd
    obtain ⟨hwD, habs⟩ := hbd w hw hd
    rw [hfin w hwD]
    exact_mod_cast (by linarith [(abs_lt.1 habs).2] : (f w).toReal ≤ rz + 1)
  have hbot_cl : ∀ x, ⊥ < cl_f x := by
    intro x
    set R := dist x z + 1 with hR
    have hRpos : 0 < R := by positivity
    set l := δ / (2 * R) with hl
    have hlpos : 0 < l := by positivity
    set t := l / (1 + l) with ht
    have htpos : 0 < t := by positivity
    have ht1 : t < 1 := by
      rw [ht, div_lt_one (by positivity)]; linarith
    have h1t : (1 - t) * l = t := by
      rw [ht]; field_simp; ring
    set c := (rz - (1 - t) * (rz + 1)) / t with hc
    have hev : ∀ᶠ y in 𝓝 x, (c : EReal) ≤ f y := by
      filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
      by_cases hyD : y ∈ D
      · have hyA : y ∈ A := subset_affineSpan ℝ D hyD
        set w := l • (z - y) + z with hw
        have hzy : z - y ∈ A.direction := by
          simpa using AffineSubspace.vsub_mem_direction hzA hyA
        have hwA : w ∈ A :=
          AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ _ hzy) hzA
        have hwd : dist w z < δ := by
          rw [hw, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos hlpos]
          have h1 : ‖z - y‖ < R := by
            rw [← dist_eq_norm]
            have := dist_triangle z x y
            rw [Metric.mem_ball] at hy
            rw [_root_.dist_comm z x, _root_.dist_comm x y] at this
            linarith
          calc l * ‖z - y‖ < l * R := by gcongr
            _ = δ / 2 := by rw [hl]; field_simp
            _ < δ := by linarith
        have hfw := hM w hwA hwd
        have hcomb : t • y + (1 - t) • w = z := by
          rw [hw, smul_add, smul_smul, h1t, smul_sub, sub_smul, one_smul]
          abel
        have h3 := hconvf y w t (1 - t) (f y).toReal (rz + 1) htpos.le (by linarith) (by ring)
          (hfin y hyD).le hfw
        rw [hcomb, hfz] at h3
        have h2 : rz ≤ t * (f y).toReal + (1 - t) * (rz + 1) := by exact_mod_cast h3
        rw [hfin y hyD]
        have : c ≤ (f y).toReal := by
          rw [hc, div_le_iff₀ htpos]
          linarith
        exact_mod_cast this
      · rw [htop y hyD]; exact le_top
    calc (⊥ : EReal) < c := EReal.bot_lt_coe c
      _ ≤ cl_f x := Filter.le_liminf_of_le (by isBoundedDefault) hev
  have hri : ∀ x ∈ intrinsicInterior ℝ D, cl_f x = f x := by
    intro x hx
    refine le_antisymm (hle x) ?_
    have hxD : x ∈ D := intrinsicInterior_subset hx
    rw [hfin x hxD]
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hc' : c < (f x).toReal := by exact_mod_cast hc2
    obtain ⟨δ', hδ', hball⟩ := key x hx ((f x).toReal - c) (by linarith)
    have hev : ∀ᶠ y in 𝓝 x, (c : EReal) ≤ f y := by
      filter_upwards [Metric.ball_mem_nhds x hδ'] with y hy
      by_cases hyD : y ∈ D
      · obtain ⟨-, habs⟩ := hball y (subset_affineSpan ℝ D hyD) hy
        rw [hfin y hyD]
        have := (abs_lt.1 habs).1
        exact_mod_cast (by linarith : c ≤ (f y).toReal)
      · rw [htop y hyD]; exact le_top
    have : (c : EReal) ≤ cl_f x := Filter.le_liminf_of_le (by isBoundedDefault) hev
    exact lt_irrefl _ (this.trans_lt hc1)
  exact ⟨⟨hbot_cl, ⟨x₀, lt_of_le_of_lt (hle x₀) hx₀⟩, hcl_conv⟩, hri⟩

end FCA_chap_B_1_2_6
