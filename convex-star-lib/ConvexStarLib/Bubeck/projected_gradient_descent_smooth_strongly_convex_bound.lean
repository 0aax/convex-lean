import ConvexStarLib.Defs

/-!
# `projected_gradient_descent_smooth_strongly_convex_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/projected_gradient_descent_smooth_strongly_convex_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace projected_gradient_descent_smooth_strongly_convex_bound`, so the main result is `projected_gradient_descent_smooth_strongly_convex_bound.projected_gradient_descent_smooth_strongly_convex_bound`.
-/

namespace projected_gradient_descent_smooth_strongly_convex_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem aux_hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {f : F → ℝ} {x d G : F} {s : ℝ} (hG : HasGradientAt f G (x + s • d)) :
    HasDerivAt (fun t : ℝ => f (x + t • d)) (inner ℝ G d) s := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have := hG.hasFDerivAt.comp_hasDerivAt s h1
  simpa [Function.comp_def] using this

theorem aux_strong_convex_first_order {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {s : Set F} {f : F → ℝ} {α : ℝ} {x y G : F}
    (hf : StrongConvexOn s α f) (hx : x ∈ s) (hy : y ∈ s) (hG : HasGradientAt f G x) :
    f x + inner ℝ G (y - x) + α / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hφ : HasDerivAt (fun t : ℝ => f (x + t • (y - x))) (inner ℝ G (y - x)) 0 :=
    aux_hasDerivAt_line (by simpa using hG)
  have hlim := hφ.tendsto_slope_zero_right
  have hlim2 : Filter.Tendsto (fun t : ℝ => f y - f x - (1 - t) * (α / 2 * ‖y - x‖ ^ 2))
      (𝓝[>] 0) (𝓝 (f y - f x - (1 - 0) * (α / 2 * ‖y - x‖ ^ 2))) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Continuous.tendsto
    fun_prop
  have hle : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (f (x + (0 + t) • (y - x)) - f (x + (0:ℝ) • (y - x)))
      ≤ f y - f x - (1 - t) * (α / 2 * ‖y - x‖ ^ 2) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have key := hf.2 hx hy (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring : (1 - t) + t = 1)
    have hxe : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [hxe, norm_sub_rev x y] at key
    simp only [smul_eq_mul, zero_add, zero_smul, add_zero] at key ⊢
    rw [inv_mul_le_iff₀ ht0]
    nlinarith [key]
  have := le_of_tendsto_of_tendsto hlim hlim2 hle
  linarith

theorem aux_descent {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {s : Set F} {f : F → ℝ} {g : F → F} {β : ℝ} {x z : F}
    (hs : Convex ℝ s) (hx : x ∈ s) (hz : z ∈ s)
    (hg : ∀ p ∈ s, HasGradientAt f (g p) p)
    (hL : ∀ p ∈ s, ∀ q ∈ s, ‖g p - g q‖ ≤ β * ‖p - q‖) :
    f z ≤ f x + inner ℝ (g x) (z - x) + β / 2 * ‖z - x‖ ^ 2 := by
  set d := z - x with hd
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • d ∈ s := fun t ht => hs.add_smul_sub_mem hx hz ht
  let ψ : ℝ → ℝ := fun t => f (x + t • d) - t * inner ℝ (g x) d - β / 2 * t ^ 2 * ‖d‖ ^ 2
  have hφd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ
      (inner ℝ (g (x + t • d)) d - inner ℝ (g x) d - β * t * ‖d‖ ^ 2) t := by
    intro t ht
    have h1 := aux_hasDerivAt_line (f := f) (x := x) (d := d) (s := t) (hg _ (hmem t ht))
    have h2 : HasDerivAt (fun t : ℝ => t * inner ℝ (g x) d) (inner ℝ (g x) d) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (g x) d)
    have h3 : HasDerivAt (fun t : ℝ => β / 2 * t ^ 2 * ‖d‖ ^ 2) (β * t * ‖d‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖d‖ ^ 2)
      convert this using 1; push_cast; ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro t ht
      exact (hφd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hφd t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      have hb := hL _ (hmem t ht') x hx
      have hc : inner ℝ (g (x + t • d) - g x) d ≤ ‖g (x + t • d) - g x‖ * ‖d‖ :=
        real_inner_le_norm _ _
      rw [inner_sub_left] at hc
      have : ‖x + t • d - x‖ = t * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      rw [this] at hb
      have := mul_le_mul_of_nonneg_right hb (norm_nonneg d)
      nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [ψ, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  rw [hd, add_sub_cancel] at this
  linarith

theorem aux_alg {A B P Q R fxs fxn fxstar α β : ℝ} (hβ : 0 < β)
    (hA : fxn ≤ fxs + R + β / 2 * B) (hB : fxs - Q + α / 2 * A ≤ fxstar) (hC : fxstar ≤ fxn)
    (hP : P + B + (1 / β) * (Q + R) ≤ 0) : A + 2 * P + B ≤ (1 - α / β) * A := by
  have h1 : β * P + β * B + (Q + R) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hP hβ.le
    rw [mul_zero, mul_add, mul_add, ← mul_assoc, mul_one_div_cancel hβ.ne', one_mul] at this
    linarith
  have h2 : α * A ≤ -2 * β * P - β * B := by linarith
  have h3 : α / β * A ≤ -2 * P - B := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hβ]; linarith
  have h4 : (1 - α / β) * A = A - α / β * A := by ring
  linarith


set_option linter.unusedVariables false in
theorem projected_gradient_descent_smooth_strongly_convex_bound {n t : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (α β : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (hα_pos : α > 0)
  (hx_init : x 0 ∈ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (hf_strongly_convex : StrongConvexOn 𝓧 α f)
  (hf_subgradients : ∀ x ∈ 𝓧, ∃ g, InDomIsSubgradientAt 𝓧 f x g)
  (hf_differentiable : DifferentiableOn ℝ f 𝓧)
  (hf_beta_smooth : LipschitzOnWith (Real.toNNReal β) (gradient f) 𝓧)
  (h_gd_seq : IsProjectedGradientDescentSequence 𝓧 f g x (fun s => 1 / β)
              h𝓧_nonempty h𝓧_compact h𝓧_convex)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  let κ := β / α
  ‖(x t) - x_star‖ ^ 2 ≤ Real.exp (- t / κ) * ‖(x 0) - x_star‖ ^ 2 := by
  intro κ
  obtain ⟨hgrad, hstep⟩ := h_gd_seq
  have hβ' : ((Real.toNNReal β : NNReal) : ℝ) = β := Real.coe_toNNReal β hβ_pos.le
  have hL : ∀ p ∈ 𝓧, ∀ q ∈ 𝓧, ‖g p - g q‖ ≤ β * ‖p - q‖ := by
    intro p hp q hq
    have := hf_beta_smooth.dist_le_mul p hp q hq
    rw [(hgrad p hp).gradient, (hgrad q hq).gradient, hβ', dist_eq_norm, dist_eq_norm] at this
    exact this
  have hproj : ∀ u : EuclideanSpace ℝ (Fin n),
      pC u 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty ∈ 𝓧 ∧
      ∀ w ∈ 𝓧, inner ℝ (u - pC u 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty)
        (w - pC u 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty) ≤ 0 := by
    intro u
    have hspec := Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex h𝓧_nonempty
      h𝓧_compact.isClosed.isComplete h𝓧_convex u)
    exact ⟨hspec.1, (norm_eq_iInf_iff_real_inner_le_zero h𝓧_convex hspec.1).1 hspec.2⟩
  have hstep' : ∀ s, x (s + 1) = pC (x s - (1 / β) • g (x s)) 𝓧 h𝓧_compact.isClosed
      h𝓧_convex h𝓧_nonempty := by
    intro s
    rw [hstep s]
    rfl
  have hmem : ∀ s, x s ∈ 𝓧 := by
    intro s
    induction s with
    | zero => exact hx_init
    | succ k _ => rw [hstep' k]; exact (hproj _).1
  have hcontr : ∀ s, ‖x (s + 1) - x_star‖ ^ 2 ≤ (1 - α / β) * ‖x s - x_star‖ ^ 2 := by
    intro s
    have hxs := hmem s
    have hxn := hmem (s + 1)
    have hP := (hproj (x s - (1 / β) • g (x s))).2 x_star hx_star_mem
    rw [← hstep' s] at hP
    have hA := aux_descent h𝓧_convex hxs hxn hgrad hL
    have hB := aux_strong_convex_first_order hf_strongly_convex hxs hx_star_mem (hgrad _ hxs)
    have hC : f x_star ≤ f (x (s + 1)) := isMinOn_iff.1 hx_star _ hxn
    have e1 : x (s + 1) - x_star = (x s - x_star) + (x (s + 1) - x s) := by abel
    have e2 : x_star - x s = -(x s - x_star) := by abel
    have e3 : x s - (1 / β) • g (x s) - x (s + 1) =
        -((x (s + 1) - x s) + (1 / β) • g (x s)) := by abel
    have e4 : x_star - x (s + 1) = -((x s - x_star) + (x (s + 1) - x s)) := by abel
    rw [e3, e4] at hP
    rw [e2] at hB
    rw [e1]
    set a := x s - x_star
    set b := x (s + 1) - x s
    set G := g (x s)
    rw [inner_neg_neg, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm a b] at hP
    rw [inner_neg_right, norm_neg] at hB
    rw [norm_add_sq_real]
    exact aux_alg hβ_pos hA hB hC (by linarith)
  have hr : 1 - α / β ≤ Real.exp (-(α / β)) := by
    have := Real.add_one_le_exp (-(α / β)); linarith
  have hind : ∀ s : ℕ, ‖x s - x_star‖ ^ 2 ≤ Real.exp (-(α / β)) ^ s * ‖x 0 - x_star‖ ^ 2 := by
    intro s
    induction s with
    | zero => simp
    | succ k ih =>
      calc ‖x (k + 1) - x_star‖ ^ 2 ≤ (1 - α / β) * ‖x k - x_star‖ ^ 2 := hcontr k
        _ ≤ Real.exp (-(α / β)) * ‖x k - x_star‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hr (by positivity)
        _ ≤ Real.exp (-(α / β)) * (Real.exp (-(α / β)) ^ k * ‖x 0 - x_star‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = Real.exp (-(α / β)) ^ (k + 1) * ‖x 0 - x_star‖ ^ 2 := by ring
  have hα0 : α ≠ 0 := hα_pos.ne'
  have hβ0 : β ≠ 0 := hβ_pos.ne'
  have hexp : Real.exp (-↑t / κ) = Real.exp (-(α / β)) ^ t := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [κ]
    field_simp
  rw [hexp]
  exact hind t

end projected_gradient_descent_smooth_strongly_convex_bound
