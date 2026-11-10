import ConvexStarLib.Defs

/-!
# `subgradient_strongly_convex_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/subgradient_strongly_convex_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace subgradient_strongly_convex_bound`, so the main result is `subgradient_strongly_convex_bound.subgradient_strongly_convex_bound`.
-/

namespace subgradient_strongly_convex_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem subgradient_strongly_convex_bound {n t : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n)) (g : ℕ → EuclideanSpace ℝ (Fin n))
  (α R L : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hx_init : x 0 ∈ 𝓧)

  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_contained : 𝓧 ⊆ Metric.ball (x 0) R)
  (hα : α > 0)
  (hR : R > 0) (hL : L > 0) (ht : t > 0)

  (hf_strongly_convex : StrongConvexOn 𝓧 α f)
  (hf_subgradients : ∀ x ∈ 𝓧, ∃ g, InDomIsSubgradientAt 𝓧 f x g)
  (hg_bounded : ∀ s, ‖g s‖ ≤ L)
  (h_ps_seq : IsProjectedSubgradientSequence 𝓧 f x g (fun s => 2 / (α * (s + 2)))
                                             h𝓧_nonempty h𝓧_compact h𝓧_convex)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  f (∑ i ∈ Finset.range t, ((2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) • x i) - f x_star
  ≤ (2 * L^2) / (α * (t + 1)) := by
  classical
  obtain ⟨h_step, h_sub⟩ := h_ps_seq
  -- basic facts about the projection
  have hpC_spec : ∀ y : EuclideanSpace ℝ (Fin n),
      pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty ∈ 𝓧 ∧
      ∀ w ∈ 𝓧, inner ℝ (y - pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty)
        (w - pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty) ≤ 0 := by
    intro y
    have hspec := Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex h𝓧_nonempty h𝓧_compact.isClosed.isComplete
        h𝓧_convex y)
    exact ⟨hspec.1, (norm_eq_iInf_iff_real_inner_le_zero h𝓧_convex hspec.1).1 hspec.2⟩
  have hproj : ∀ y : EuclideanSpace ℝ (Fin n), ∀ w ∈ 𝓧,
      ‖pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty - w‖ ^ 2 ≤ ‖y - w‖ ^ 2 := by
    intro y w hw
    have h1 := (hpC_spec y).2 w hw
    set p := pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty
    have h2 : y - w = (y - p) + (p - w) := by abel
    have h3 : inner ℝ (y - p) (p - w) = - inner ℝ (y - p) (w - p) := by
      rw [← inner_neg_right, neg_sub]
    rw [h2, norm_add_sq_real, h3]
    nlinarith [sq_nonneg ‖y - p‖]
  -- all iterates lie in 𝓧
  have hx_mem : ∀ s, x s ∈ 𝓧 := by
    intro s
    cases s with
    | zero => exact hx_init
    | succ s => rw [h_step s]; exact (hpC_spec _).1
  -- strong convexity subgradient inequality
  have hsc_sub : ∀ s, ∀ y ∈ 𝓧,
      f y ≥ f (x s) + inner ℝ (y - x s) (g s) + α / 2 * ‖y - x s‖ ^ 2 := by
    intro s y hy
    have hxs := hx_mem s
    have key : ∀ l : ℝ, 0 < l → l ≤ 1 →
        (1 - l) * (α / 2 * ‖y - x s‖ ^ 2) ≤ f y - f (x s) - inner ℝ (y - x s) (g s) := by
      intro l hl0 hl1
      have hz : (1 - l) • x s + l • y ∈ 𝓧 :=
        h𝓧_convex hxs hy (by linarith) hl0.le (by ring)
      have hconv := hf_strongly_convex.2 hxs hy (by linarith : (0:ℝ) ≤ 1 - l) hl0.le (by ring)
      have hsub := h_sub s _ hz
      have hz' : (1 - l) • x s + l • y - x s = l • (y - x s) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [hz', real_inner_smul_left] at hsub
      simp only [smul_eq_mul] at hconv
      rw [norm_sub_rev (x s) y] at hconv
      have : l * ((1 - l) * (α / 2 * ‖y - x s‖ ^ 2)) ≤
          l * (f y - f (x s) - inner ℝ (y - x s) (g s)) := by
        nlinarith
      exact le_of_mul_le_mul_left this hl0
    by_contra hcon
    push_neg at hcon
    set A := f y - f (x s) - inner ℝ (y - x s) (g s) with hA
    set c := α / 2 * ‖y - x s‖ ^ 2 with hc
    have hAc : A < c := by rw [hA]; linarith
    have hA0 : 0 ≤ A := by have := key 1 one_pos le_rfl; simpa using this
    have hc0 : 0 < c := lt_of_le_of_lt hA0 hAc
    have hl0 : 0 < (c - A) / (2 * c) := div_pos (by linarith) (by linarith)
    have hl1 : (c - A) / (2 * c) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h := key _ hl0 hl1
    have : (1 - (c - A) / (2 * c)) * c = (c + A) / 2 := by field_simp; ring
    rw [this] at h
    linarith
  -- one-step inequality
  have hstep : ∀ s : ℕ, ((s:ℝ) + 1) * (f (x s) - f x_star) +
      α / 4 * ((s:ℝ) + 1) * ((s:ℝ) + 2) * ‖x (s + 1) - x_star‖ ^ 2
      ≤ α / 4 * (s:ℝ) * ((s:ℝ) + 1) * ‖x s - x_star‖ ^ 2 + L ^ 2 / α := by
    intro s
    have h1 := hsc_sub s x_star hx_star_mem
    have h2 := hproj (x s - (2 / (α * ((s:ℝ) + 2))) • g s) x_star hx_star_mem
    have hx1 : x (s + 1) = pC (x s - (2 / (α * ((s:ℝ) + 2))) • g s) 𝓧
        h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty := h_step s
    rw [← hx1] at h2
    set η := 2 / (α * ((s:ℝ) + 2)) with hη
    have hexp : ‖x s - η • g s - x_star‖ ^ 2 =
        ‖x s - x_star‖ ^ 2 - 2 * η * inner ℝ (x s - x_star) (g s) + η ^ 2 * ‖g s‖ ^ 2 := by
      have : x s - η • g s - x_star = (x s - x_star) - η • g s := by abel
      rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    rw [hexp] at h2
    have hi1 : inner ℝ (x_star - x s) (g s) = - inner ℝ (x s - x_star) (g s) := by
      rw [← inner_neg_left, neg_sub]
    rw [norm_sub_rev x_star (x s), hi1] at h1
    have hg2 : ‖g s‖ ^ 2 ≤ L ^ 2 := by
      have := hg_bounded s
      have h0 : 0 ≤ ‖g s‖ := norm_nonneg _
      nlinarith
    set P := inner ℝ (x s - x_star) (g s)
    set D0 := ‖x s - x_star‖ ^ 2
    set D1 := ‖x (s + 1) - x_star‖ ^ 2
    set G := ‖g s‖ ^ 2
    have hs2 : (0:ℝ) < (s:ℝ) + 2 := by positivity
    have hc0 : 0 ≤ α / 4 * ((s:ℝ) + 1) * ((s:ℝ) + 2) := by positivity
    have e1 : 2 * (α / 4 * ((s:ℝ) + 1) * ((s:ℝ) + 2)) * η = (s:ℝ) + 1 := by
      rw [hη]; field_simp; ring
    have e2 : α / 4 * ((s:ℝ) + 1) * ((s:ℝ) + 2) * η ^ 2 = ((s:ℝ) + 1) / (α * ((s:ℝ) + 2)) := by
      rw [hη]; field_simp; ring
    have h2c := mul_le_mul_of_nonneg_left h2 hc0
    have h3 : ((s:ℝ) + 1) / (α * ((s:ℝ) + 2)) * G ≤ L ^ 2 / α := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hα]
      have hG0 : 0 ≤ G := sq_nonneg _
      have hGα : 0 ≤ G * α := mul_nonneg hG0 hα.le
      have hk : 0 ≤ ((s:ℝ) + 2) * α := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hg2 hk]
    have expand : α / 4 * ((s:ℝ) + 1) * ((s:ℝ) + 2) * (D0 - 2 * η * P + η ^ 2 * G) =
        α / 4 * ((s:ℝ) + 1) * ((s:ℝ) + 2) * D0
          - (2 * (α / 4 * ((s:ℝ) + 1) * ((s:ℝ) + 2)) * η) * P
          + (α / 4 * ((s:ℝ) + 1) * ((s:ℝ) + 2) * η ^ 2) * G := by ring
    rw [expand, e1, e2] at h2c
    have h1' : ((s:ℝ) + 1) * (f (x s) - f x_star) ≤ ((s:ℝ) + 1) * (P - α / 2 * D0) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linear_combination h1' + h2c + h3
  -- telescoping
  have hsum : ∀ T : ℕ, ∑ i ∈ Finset.range T, ((i:ℝ) + 1) * (f (x i) - f x_star) +
      α / 4 * (T:ℝ) * ((T:ℝ) + 1) * ‖x T - x_star‖ ^ 2 ≤ T * (L ^ 2 / α) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have := hstep T
      push_cast
      linarith
  -- Jensen
  have hconvex : ConvexOn ℝ 𝓧 f :=
    UniformConvexOn.convexOn hf_strongly_convex (by intro r; simp only [Pi.zero_apply]; positivity)
  have ht' : (0:ℝ) < t := by exact_mod_cast ht
  have hw0 : ∀ i ∈ Finset.range t, 0 ≤ (2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1)) :=
    fun i _ => by positivity
  have hgauss : ∀ T : ℕ, ∑ i ∈ Finset.range T, ((i:ℝ) + 1) = (T:ℝ) * ((T:ℝ) + 1) / 2 := by
    intro T
    induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hw1 : ∑ i ∈ Finset.range t, (2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1)) = 1 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, hgauss t]
    field_simp
  have hjensen : f (∑ i ∈ Finset.range t, ((2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) • x i) ≤
      ∑ i ∈ Finset.range t, ((2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) • f (x i) :=
    hconvex.map_sum_le hw0 hw1 (fun i _ => hx_mem i)
  have hrewrite : ∑ i ∈ Finset.range t, ((2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) • f (x i)
      - f x_star = 2 / ((t:ℝ) * ((t:ℝ) + 1)) *
        ∑ i ∈ Finset.range t, ((i:ℝ) + 1) * (f (x i) - f x_star) := by
    calc ∑ i ∈ Finset.range t, ((2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) • f (x i) - f x_star
        = ∑ i ∈ Finset.range t, ((2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) • f (x i)
          - (∑ i ∈ Finset.range t, (2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) * f x_star := by
          rw [hw1, one_mul]
      _ = ∑ i ∈ Finset.range t,
            (2 / ((t:ℝ) * ((t:ℝ) + 1))) * (((i:ℝ) + 1) * (f (x i) - f x_star)) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          simp only [smul_eq_mul]
          ring
      _ = _ := by rw [Finset.mul_sum]
  have hS : ∑ i ∈ Finset.range t, ((i:ℝ) + 1) * (f (x i) - f x_star) ≤ t * (L ^ 2 / α) := by
    have := hsum t
    have hD : 0 ≤ α / 4 * (t:ℝ) * ((t:ℝ) + 1) * ‖x t - x_star‖ ^ 2 := by positivity
    linarith
  have hcoef : 0 ≤ 2 / ((t:ℝ) * ((t:ℝ) + 1)) := by positivity
  calc f (∑ i ∈ Finset.range t, ((2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) • x i) - f x_star
      ≤ ∑ i ∈ Finset.range t, ((2 * ((↑i : ℝ) + 1)) / (↑t * (↑t + 1))) • f (x i) - f x_star := by
        linarith [hjensen]
    _ = 2 / ((t:ℝ) * ((t:ℝ) + 1)) *
          ∑ i ∈ Finset.range t, ((i:ℝ) + 1) * (f (x i) - f x_star) := hrewrite
    _ ≤ 2 / ((t:ℝ) * ((t:ℝ) + 1)) * (t * (L ^ 2 / α)) := mul_le_mul_of_nonneg_left hS hcoef
    _ = (2 * L ^ 2) / (α * (t + 1)) := by field_simp

end subgradient_strongly_convex_bound
