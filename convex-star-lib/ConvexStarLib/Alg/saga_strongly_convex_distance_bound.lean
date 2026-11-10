import ConvexStarLib.Defs

/-!
# `saga_strongly_convex_distance_bound`

Source: Defazio, Bach & Lacoste-Julien, 'SAGA: A Fast Incremental Gradient Method With Support for Non-Strongly Convex Composite Objectives' (NIPS 2014).

Statement from the `convex-eval-v28-2h/saga_strongly_convex_distance_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace saga_strongly_convex_distance_bound`, so the main result is `saga_strongly_convex_distance_bound.saga_strongly_convex_distance_bound`.
-/

namespace saga_strongly_convex_distance_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma saga_aux_descent (f : E → ℝ) (G : E → E) (hG : ∀ x, HasGradientAt f (G x) x) (L : ℝ)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    |f y - f x - inner ℝ (G x) (y - x)| ≤ L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd
  let ψ : ℝ → ℝ := fun t => f (x + t • d) - t * inner ℝ (G x) d - f x
  have hderiv : ∀ t : ℝ, HasDerivAt ψ (inner ℝ (G (x + t • d)) d - inner ℝ (G x) d) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => x + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h2 : HasFDerivAt f (InnerProductSpace.toDual ℝ E (G (x + t • d))) (x + t • d) :=
      (hG (x + t • d)).hasFDerivAt
    have h3 : HasDerivAt (fun s : ℝ => f (x + s • d))
        (InnerProductSpace.toDual ℝ E (G (x + t • d)) d) t :=
      h2.comp_hasDerivAt t h1
    have h4 : HasDerivAt (fun s : ℝ => s * inner ℝ (G x) d) (inner ℝ (G x) d) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (G x) d)
    have h5 := (h3.sub h4).sub_const (f x)
    rw [InnerProductSpace.toDual_apply_apply] at h5
    exact h5
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
    intro t
    have h6 := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
    convert h6 using 1
    push_cast
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := ψ)
    (f' := fun t => inner ℝ (G (x + t • d)) d - inner ℝ (G x) d)
    (B := fun t : ℝ => L / 2 * t ^ 2 * ‖d‖ ^ 2) (B' := fun t => L * t * ‖d‖ ^ 2)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (by simp [ψ])
    hB
    (by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      show ‖inner ℝ (G (x + t • d)) d - inner ℝ (G x) d‖ ≤ L * t * ‖d‖ ^ 2
      rw [Real.norm_eq_abs, ← inner_sub_left]
      calc |inner ℝ (G (x + t • d) - G x) d| ≤ ‖G (x + t • d) - G x‖ * ‖d‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ L * ‖(x + t • d) - x‖ * ‖d‖ :=
            mul_le_mul_of_nonneg_right (hLip _ _) (norm_nonneg _)
        _ = L * t * ‖d‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
          ring)
  have h1 := key (x := 1) ⟨zero_le_one, le_rfl⟩
  have hxy : x + d = y := by rw [hd]; abel
  simp only [ψ, one_smul, one_mul, one_pow, mul_one, Real.norm_eq_abs, hxy] at h1
  calc |f y - f x - inner ℝ (G x) d| = |f y - inner ℝ (G x) d - f x| := by ring_nf
    _ ≤ L / 2 * ‖d‖ ^ 2 := h1

lemma saga_aux_limit {a b : ℝ} (h : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ a + b * t) : 0 ≤ a := by
  by_contra hneg
  push_neg at hneg
  have hb1 : 0 < |b| + 1 := by positivity
  set t := min (1 / 2 : ℝ) (-a / (2 * (|b| + 1))) with ht
  have ht_pos : 0 < t := by
    apply lt_min
    · norm_num
    · apply _root_.div_pos
      · linarith
      · positivity
  have ht_lt : t < 1 := by
    have : t ≤ 1 / 2 := min_le_left _ _
    linarith
  have ht_le : t ≤ -a / (2 * (|b| + 1)) := min_le_right _ _
  have h1 := h t ht_pos ht_lt
  have h2 : b * t ≤ |b| * t := mul_le_mul_of_nonneg_right (le_abs_self b) ht_pos.le
  have h3 : (|b| + 1) * t ≤ -a / 2 := by
    calc (|b| + 1) * t ≤ (|b| + 1) * (-a / (2 * (|b| + 1))) :=
          mul_le_mul_of_nonneg_left ht_le hb1.le
      _ = -a / 2 := by field_simp
  linarith

lemma saga_aux_strong (f : E → ℝ) (G : E → E) (L μ : ℝ)
    (hdesc : ∀ x y, f x + inner ℝ (G x) (y - x) - L / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hsc : StrongConvexOn Set.univ μ f) (x y : E) :
    f x + inner ℝ (G x) (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      0 ≤ (f y - f x - inner ℝ (G x) (y - x) - μ / 2 * ‖y - x‖ ^ 2)
        + (μ / 2 + L / 2) * ‖y - x‖ ^ 2 * t := by
    intro t ht0 ht1
    have h1 := hsc.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
      (by ring : (1 - t) + t = 1)
    have h2 := hdesc x (x + t • (y - x))
    have heq : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq] at h1
    have h3 : x + t • (y - x) - x = t • (y - x) := by abel
    rw [h3, real_inner_smul_right, norm_smul, mul_pow] at h2
    simp only [smul_eq_mul] at h1
    rw [norm_sub_rev x y] at h1
    have hn : ‖t‖ = t := by rw [Real.norm_eq_abs, abs_of_pos ht0]
    rw [hn] at h2
    have h4 : 0 ≤ t * ((f y - f x - inner ℝ (G x) (y - x) - μ / 2 * ‖y - x‖ ^ 2)
        + (μ / 2 + L / 2) * ‖y - x‖ ^ 2 * t) := by
      linarith
    exact (mul_nonneg_iff_of_pos_left ht0).mp h4
  have := saga_aux_limit key
  linarith

lemma saga_aux_cocoercive (ψ : E → ℝ) (G : E → E) (L : ℝ) (hL : 0 ≤ L)
    (hlow : ∀ y z, ψ y + inner ℝ (G y) (z - y) ≤ ψ z)
    (hup : ∀ y z, ψ z ≤ ψ y + inner ℝ (G y) (z - y) + L / 2 * ‖z - y‖ ^ 2) (x y : E) :
    ‖G y - G x‖ ^ 2 ≤ 2 * L * (ψ y - ψ x - inner ℝ (G x) (y - x)) := by
  set u := G y - G x with hu
  set Δ := ψ y - ψ x - inner ℝ (G x) (y - x) with hΔ
  have key : ∀ s : ℝ, 0 ≤ s → s * ‖u‖ ^ 2 - L / 2 * s ^ 2 * ‖u‖ ^ 2 ≤ Δ := by
    intro s hs
    have h1 := hup y (y - s • u)
    have h2 := hlow x (y - s • u)
    have e1 : y - s • u - y = -(s • u) := by abel
    rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, mul_pow] at h1
    have e2 : y - s • u - x = (y - x) - s • u := by abel
    rw [e2, inner_sub_right, real_inner_smul_right] at h2
    have hn : ‖s‖ = s := by rw [Real.norm_eq_abs, abs_of_nonneg hs]
    rw [hn] at h1
    have h3 : inner ℝ (G y) u - inner ℝ (G x) u = ‖u‖ ^ 2 := by
      rw [← inner_sub_left, ← hu, real_inner_self_eq_norm_sq]
    have h4 : s * inner ℝ (G y) u - s * inner ℝ (G x) u = s * ‖u‖ ^ 2 := by
      rw [← mul_sub, h3]
    rw [hΔ]
    linarith
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · rw [← hL0]
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < ‖u‖ ^ 2 := by linarith
    have := key ((|Δ| + 1) / ‖u‖ ^ 2) (by positivity)
    rw [← hL0] at this
    have e : (|Δ| + 1) / ‖u‖ ^ 2 * ‖u‖ ^ 2 = |Δ| + 1 := div_mul_cancel₀ _ hpos.ne'
    rw [e] at this
    have := le_abs_self Δ
    linarith
  · have := key (1 / L) (by positivity)
    have e : 1 / L * ‖u‖ ^ 2 - L / 2 * (1 / L) ^ 2 * ‖u‖ ^ 2 = ‖u‖ ^ 2 / (2 * L) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)] at this
    linarith

lemma saga_aux_fi (f : E → ℝ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≤ β)
    (hdiff : Differentiable ℝ f) (hsmooth : LipschitzWith (Real.toNNReal β) (gradient f))
    (hsc : StrongConvexOn Set.univ α f) :
    (∀ x y, f y ≤ f x + inner ℝ (gradient f x) (y - x) + β / 2 * ‖y - x‖ ^ 2) ∧
    (∀ x y, f x + inner ℝ (gradient f x) (y - x) + α / 2 * ‖y - x‖ ^ 2 ≤ f y) ∧
    (∀ x y, ‖gradient f y - gradient f x‖ ^ 2 ≤
        2 * β * (f y - f x - inner ℝ (gradient f x) (y - x))) ∧
    (∀ u v, (β - α) * (f u - f v - inner ℝ (gradient f v) (u - v)) + α * β / 2 * ‖u - v‖ ^ 2
        + ‖gradient f u - gradient f v‖ ^ 2 / 2
        ≤ β * inner ℝ (gradient f u - gradient f v) (u - v)) := by
  have hG : ∀ x, HasGradientAt f (gradient f x) x := fun x => (hdiff x).hasGradientAt
  have hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖ := by
    intro x y
    have := hsmooth.dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hβ.le] at this
    exact this
  have hdesc := saga_aux_descent f (gradient f) hG β hLip
  have h1 : ∀ x y, f y ≤ f x + inner ℝ (gradient f x) (y - x) + β / 2 * ‖y - x‖ ^ 2 := by
    intro x y
    have := (abs_le.mp (hdesc x y)).2
    linarith
  have h2 : ∀ x y, f x + inner ℝ (gradient f x) (y - x) + α / 2 * ‖y - x‖ ^ 2 ≤ f y := by
    intro x y
    refine saga_aux_strong f (gradient f) β α (fun x y => ?_) hsc x y
    have := (abs_le.mp (hdesc x y)).1
    linarith
  have h3 : ∀ x y, ‖gradient f y - gradient f x‖ ^ 2 ≤
      2 * β * (f y - f x - inner ℝ (gradient f x) (y - x)) := by
    intro x y
    refine saga_aux_cocoercive f (gradient f) β hβ.le (fun y z => ?_) h1 x y
    have := h2 y z
    have : 0 ≤ α / 2 * ‖z - y‖ ^ 2 := by positivity
    linarith
  refine ⟨h1, h2, h3, ?_⟩
  intro u v
  have hid : ∀ y z : E, α / 2 * ‖z‖ ^ 2 - α / 2 * ‖y‖ ^ 2 - α * inner ℝ y (z - y)
      = α / 2 * ‖z - y‖ ^ 2 := by
    intro y z
    rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm z y]
    ring
  have hlow' : ∀ y z, (f y - α / 2 * ‖y‖ ^ 2) + inner ℝ (gradient f y - α • y) (z - y)
      ≤ f z - α / 2 * ‖z‖ ^ 2 := by
    intro y z
    have h := h2 y z
    have hi := hid y z
    rw [inner_sub_left, real_inner_smul_left]
    linarith
  have hup' : ∀ y z, f z - α / 2 * ‖z‖ ^ 2 ≤ (f y - α / 2 * ‖y‖ ^ 2)
      + inner ℝ (gradient f y - α • y) (z - y) + (β - α) / 2 * ‖z - y‖ ^ 2 := by
    intro y z
    have h := h1 y z
    have hi := hid y z
    rw [inner_sub_left, real_inner_smul_left]
    linarith
  have hcoc : ‖(gradient f v - α • v) - (gradient f u - α • u)‖ ^ 2 ≤
      2 * (β - α) * ((f v - α / 2 * ‖v‖ ^ 2) - (f u - α / 2 * ‖u‖ ^ 2)
        - inner ℝ (gradient f u - α • u) (v - u)) :=
    saga_aux_cocoercive (fun z => f z - α / 2 * ‖z‖ ^ 2) (fun z => gradient f z - α • z)
      (β - α) (by linarith) hlow' hup' u v
  have hX : (f v - α / 2 * ‖v‖ ^ 2) - (f u - α / 2 * ‖u‖ ^ 2)
        - inner ℝ (gradient f u - α • u) (v - u)
      = (f v - f u + inner ℝ (gradient f u) (u - v)) - α / 2 * ‖u - v‖ ^ 2 := by
    have hi := hid u v
    have e1 : inner ℝ (gradient f u) (v - u) = - inner ℝ (gradient f u) (u - v) := by
      rw [← inner_neg_right, neg_sub]
    rw [inner_sub_left, real_inner_smul_left, e1, norm_sub_rev u v]
    linarith
  have hY : ‖(gradient f v - α • v) - (gradient f u - α • u)‖ ^ 2 =
      ‖gradient f u - gradient f v‖ ^ 2
        - 2 * α * inner ℝ (gradient f u - gradient f v) (u - v) + α ^ 2 * ‖u - v‖ ^ 2 := by
    have e : (gradient f v - α • v) - (gradient f u - α • u)
        = -((gradient f u - gradient f v) - α • (u - v)) := by
      rw [smul_sub]; abel
    rw [e, norm_neg, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [hX, hY] at hcoc
  have hP : inner ℝ (gradient f u - gradient f v) (u - v)
      = inner ℝ (gradient f u) (u - v) - inner ℝ (gradient f v) (u - v) := inner_sub_left _ _ _
  rw [hP] at hcoc ⊢
  linarith

lemma saga_aux_prox_real (h : E → ℝ) (γ : ℝ) (w p : E)
    (hp : p ∈ proximalMapping (liftRealtoEReal h) γ w) (z : E) :
    h p + (2 * γ)⁻¹ * ‖p - w‖ ^ 2 ≤ h z + (2 * γ)⁻¹ * ‖z - w‖ ^ 2 := by
  have h1 := hp.2 z
  unfold liftRealtoEReal at h1
  exact_mod_cast h1

lemma saga_aux_prox_subgrad (h : E → ℝ) (hh : ConvexOn ℝ Set.univ h) (γ : ℝ)
    (w p : E) (hp : ∀ z, h p + (2 * γ)⁻¹ * ‖p - w‖ ^ 2 ≤ h z + (2 * γ)⁻¹ * ‖z - w‖ ^ 2)
    (z : E) :
    h p + γ⁻¹ * inner ℝ (w - p) (z - p) ≤ h z := by
  rw [← sub_nonneg]
  apply saga_aux_limit (b := (2 * γ)⁻¹ * ‖z - p‖ ^ 2)
  intro t ht0 ht1
  have hconv : h ((1 - t) • p + t • z) ≤ (1 - t) • h p + t • h z :=
    hh.2 (Set.mem_univ p) (Set.mem_univ z) (by linarith) ht0.le (by ring)
  have hzt : (1 - t) • p + t • z = p + t • (z - p) := by
    rw [sub_smul, one_smul, smul_sub]; abel
  rw [hzt, smul_eq_mul, smul_eq_mul] at hconv
  have hq := hp (p + t • (z - p))
  have hnorm : ‖p + t • (z - p) - w‖ ^ 2
      = ‖p - w‖ ^ 2 + 2 * (t * inner ℝ (p - w) (z - p)) + t ^ 2 * ‖z - p‖ ^ 2 := by
    have : p + t • (z - p) - w = (p - w) + t • (z - p) := by abel
    rw [this, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
  have hinner : inner ℝ (p - w) (z - p) = - inner ℝ (w - p) (z - p) := by
    rw [← inner_neg_left, neg_sub]
  rw [hnorm, hinner] at hq
  have key : 0 ≤ t * (h z - (h p + γ⁻¹ * inner ℝ (w - p) (z - p))
      + (2 * γ)⁻¹ * ‖z - p‖ ^ 2 * t) := by
    have e : (2 * γ)⁻¹ = 2⁻¹ * γ⁻¹ := mul_inv 2 γ
    rw [e] at hq ⊢
    linarith
  exact (mul_nonneg_iff_of_pos_left ht0).mp key

lemma saga_aux_prox_unique (h : E → ℝ) (γ : ℝ) (hγ : 0 < γ) (w p q : E)
    (hp : ∀ z, h p + γ⁻¹ * inner ℝ (w - p) (z - p) ≤ h z)
    (hq : ∀ z, h q + γ⁻¹ * inner ℝ (w - q) (z - q) ≤ h z) : p = q := by
  have h1 := hp q
  have h2 := hq p
  have hinner : inner ℝ (w - p) (q - p) + inner ℝ (w - q) (p - q) = ‖q - p‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← neg_sub q p, inner_neg_right, ← sub_eq_add_neg,
      ← inner_sub_left]
    congr 1
    abel
  have hg : 0 < γ⁻¹ := inv_pos.mpr hγ
  have hsq : γ⁻¹ * ‖q - p‖ ^ 2 ≤ 0 := by
    rw [← hinner, mul_add]; linarith
  have hsq' : ‖q - p‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos hg hcon
    linarith
  have h0 : ‖q - p‖ = 0 := by
    have := sq_nonneg ‖q - p‖
    have h00 : ‖q - p‖ ^ 2 = 0 := le_antisymm hsq' this
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h00
  rw [norm_eq_zero, sub_eq_zero] at h0
  exact h0.symm

lemma saga_aux_prox_nonexp (h : E → ℝ) (γ : ℝ) (hγ : 0 < γ) (w p xs s : E)
    (hp : ∀ z, h p + γ⁻¹ * inner ℝ (w - p) (z - p) ≤ h z)
    (hxs : ∀ z, h xs - inner ℝ s (z - xs) ≤ h z) :
    ‖p - xs‖ ^ 2 ≤ ‖w - (xs - γ • s)‖ ^ 2 := by
  have h1 := hp xs
  have h2 := hxs p
  have hg : 0 < γ⁻¹ := inv_pos.mpr hγ
  have key : inner ℝ (w - p) (xs - p) - γ * inner ℝ s (p - xs) ≤ 0 := by
    have h3 : γ⁻¹ * (inner ℝ (w - p) (xs - p) - γ * inner ℝ s (p - xs)) ≤ 0 := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul]; linarith
    by_contra hcon
    push_neg at hcon
    have := mul_pos hg hcon
    linarith
  have hur : p - xs - (w - (xs - γ • s)) = (p - w) - γ • s := by abel
  have hwp : inner ℝ (w - p) (xs - p) = inner ℝ (p - w) (p - xs) := by
    rw [← inner_neg_neg, neg_sub, neg_sub]
  have ha : inner ℝ (p - xs - (w - (xs - γ • s))) (p - xs) ≤ 0 := by
    rw [hur, inner_sub_left, real_inner_smul_left, ← hwp]; linarith [key]
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ha
  have hb := norm_sub_sq_real (w - (xs - γ • s)) (p - xs)
  have hc := sq_nonneg ‖w - (xs - γ • s) - (p - xs)‖
  linarith

omit [FiniteDimensional ℝ E] in
lemma saga_al_young (a b : E) (ε : ℝ) (hε : 0 < ε) :
    ‖a - b‖ ^ 2 ≤ (1 + ε) * ‖a‖ ^ 2 + (1 + 1 / ε) * ‖b‖ ^ 2 := by
  have hεne : ε ≠ 0 := hε.ne'
  have h1 : 0 ≤ ‖ε • a + b‖ ^ 2 := by positivity
  rw [norm_add_sq_real, norm_smul, real_inner_smul_left, mul_pow, Real.norm_eq_abs,
    sq_abs] at h1
  rw [norm_sub_sq_real]
  have key : -(2 * inner ℝ a b) ≤ ε * ‖a‖ ^ 2 + ‖b‖ ^ 2 / ε := by
    rw [← sub_nonneg]
    have e : ε * ‖a‖ ^ 2 + ‖b‖ ^ 2 / ε - -(2 * inner ℝ a b)
        = (ε ^ 2 * ‖a‖ ^ 2 + 2 * (ε * inner ℝ a b) + ‖b‖ ^ 2) / ε := by
      field_simp
      ring
    rw [e]
    exact div_nonneg h1 hε.le
  have e2 : (1 + 1 / ε) * ‖b‖ ^ 2 = ‖b‖ ^ 2 + ‖b‖ ^ 2 / ε := by ring
  rw [e2]
  linarith [key]

omit [FiniteDimensional ℝ E] in
lemma saga_al_mean_decomp {m : ℕ} (hm : 0 < m) (U : Fin m → E) (c : E)
    (hc : c = (1 / (m : ℝ)) • ∑ i, U i) :
    ∑ j, ‖U j‖ ^ 2 = ∑ j, ‖U j - c‖ ^ 2 + (m : ℝ) * ‖c‖ ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hsum : ∑ j, (U j - c) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hc,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel hm', one_smul, sub_self]
  have h : ∀ j, ‖U j‖ ^ 2 = ‖U j - c‖ ^ 2 + 2 * inner ℝ (U j - c) c + ‖c‖ ^ 2 := by
    intro j
    rw [← norm_add_sq_real, sub_add_cancel]
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner, hsum,
    inner_zero_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma saga_aux_variance {m : ℕ} (hm : 0 < m) (Y X : Fin m → E) (ε : ℝ) (hε : 0 < ε) :
    (1 / (m : ℝ)) * ∑ j, ‖Y j - X j + (1 / (m : ℝ)) • ∑ i, X i‖ ^ 2 ≤
      (1 + ε) * ((1 / (m : ℝ)) * ∑ j, ‖Y j‖ ^ 2) - ε * ‖(1 / (m : ℝ)) • ∑ j, Y j‖ ^ 2
        + (1 + 1 / ε) * ((1 / (m : ℝ)) * ∑ j, ‖X j‖ ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := hm'.ne'
  have hεne : ε ≠ 0 := hε.ne'
  obtain ⟨Ybar, hYbar⟩ : ∃ Ybar : E, Ybar = (1 / (m : ℝ)) • ∑ j, Y j := ⟨_, rfl⟩
  obtain ⟨Xbar, hXbar⟩ : ∃ Xbar : E, Xbar = (1 / (m : ℝ)) • ∑ j, X j := ⟨_, rfl⟩
  rw [← hYbar, ← hXbar]
  have hZbar : Ybar = (1 / (m : ℝ)) • ∑ i, (Y i - X i + Xbar) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_add, smul_sub, smul_smul,
      one_div_mul_cancel hmne, one_smul, ← hYbar, ← hXbar, sub_add_cancel]
  have hZ := saga_al_mean_decomp hm (fun j => Y j - X j + Xbar) Ybar hZbar
  have hY := saga_al_mean_decomp hm Y Ybar hYbar
  have hX := saga_al_mean_decomp hm X Xbar hXbar
  simp only at hZ
  have hYoung : ∀ j, ‖Y j - X j + Xbar - Ybar‖ ^ 2 ≤
      (1 + ε) * ‖Y j - Ybar‖ ^ 2 + (1 + 1 / ε) * ‖X j - Xbar‖ ^ 2 := by
    intro j
    have e : Y j - X j + Xbar - Ybar = (Y j - Ybar) - (X j - Xbar) := by abel
    rw [e]
    exact saga_al_young _ _ ε hε
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hYoung j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hpos : 0 ≤ (1 + 1 / ε) * ((m : ℝ) * ‖Xbar‖ ^ 2) := by positivity
  have main : ∑ j, ‖Y j - X j + Xbar‖ ^ 2 ≤
      (1 + ε) * ∑ j, ‖Y j‖ ^ 2 - ε * ((m : ℝ) * ‖Ybar‖ ^ 2)
        + (1 + 1 / ε) * ∑ j, ‖X j‖ ^ 2 := by
    rw [hZ, hY, hX]
    linarith [hsum, hpos]
  have h1m : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  calc (1 / (m : ℝ)) * ∑ j, ‖Y j - X j + Xbar‖ ^ 2
      ≤ (1 / (m : ℝ)) * ((1 + ε) * ∑ j, ‖Y j‖ ^ 2 - ε * ((m : ℝ) * ‖Ybar‖ ^ 2)
          + (1 + 1 / ε) * ∑ j, ‖X j‖ ^ 2) := mul_le_mul_of_nonneg_left main h1m
    _ = (1 + ε) * ((1 / (m : ℝ)) * ∑ j, ‖Y j‖ ^ 2) - ε * ‖Ybar‖ ^ 2
        + (1 + 1 / ε) * ((1 / (m : ℝ)) * ∑ j, ‖X j‖ ^ 2) := by
      field_simp

lemma saga_aux_combine (m α β F Dbar R Q P N S Vz : ℝ) (hm : 1 ≤ m) (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α ≤ β) (hF : 0 ≤ F) (hR : R ≤ 2 * β * F)
    (hP : (β - α) * Dbar + α * β / 2 * N + Q / 2 ≤ β * P)
    (hS : 2 * α * Dbar ≤ S)
    (hV : Vz ≤ (1 + (2 * α * m + β) / β) * Q - (2 * α * m + β) / β * S
        + (1 + 1 / ((2 * α * m + β) / β)) * R) :
    (1 - 1 / m) * F + (1 / m) * Dbar
      + (2 * (α * m + β) ^ 2 / ((2 * (α * m + β) - α) * m)) *
        (N - 2 * (1 / (2 * (α * m + β))) * P + (1 / (2 * (α * m + β))) ^ 2 * Vz)
    ≤ (1 - 1 / (2 * (α * m + β)) * α) *
        (F + (2 * (α * m + β) ^ 2 / ((2 * (α * m + β) - α) * m)) * N) := by
  have hm0 : (0:ℝ) < m := by linarith
  have hA : 0 < α * m + β := by positivity
  have hB : 0 < 2 * (α * m + β) - α := by nlinarith
  have hD : 0 < 2 * α * m + β := by positivity
  have hmne : m ≠ 0 := hm0.ne'
  have hAne : α * m + β ≠ 0 := hA.ne'
  have hBne : 2 * (α * m + β) - α ≠ 0 := hB.ne'
  have hDne : 2 * α * m + β ≠ 0 := hD.ne'
  have hβne : β ≠ 0 := hβ.ne'
  have hV' : β * (2 * α * m + β) * Vz ≤ 2 * (α * m + β) * (2 * α * m + β) * Q
      - (2 * α * m + β) ^ 2 * S + 2 * (α * m + β) * β * R := by
    have h1 : β * (2 * α * m + β) * ((1 + (2 * α * m + β) / β) * Q - (2 * α * m + β) / β * S
        + (1 + 1 / ((2 * α * m + β) / β)) * R) = 2 * (α * m + β) * (2 * α * m + β) * Q
          - (2 * α * m + β) ^ 2 * S + 2 * (α * m + β) * β * R := by
      field_simp
      ring
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hV (by positivity)
  have hKF : 0 ≤ (2 * (α * m + β) - α) * (2 * α * m + β) * (α * m + 2 * β)
      - 4 * (α * m + β) ^ 2 * β := by
    have hx : 0 < α * m := by positivity
    have hB' : α * m + 2 * β ≤ 2 * (α * m + β) - α := by nlinarith
    have hE : 0 < α * m + 2 * β := by positivity
    have h2 : (α * m + 2 * β) * (2 * α * m + β) * (α * m + 2 * β)
        ≤ (2 * (α * m + β) - α) * (2 * α * m + β) * (α * m + 2 * β) := by
      have := mul_le_mul_of_nonneg_right hB' (le_of_lt (mul_pos hD hE))
      nlinarith [this]
    have h3 : 0 ≤ (α * m + 2 * β) * (2 * α * m + β) * (α * m + 2 * β)
        - 4 * (α * m + β) ^ 2 * β := by
      have e : (α * m + 2 * β) * (2 * α * m + β) * (α * m + 2 * β) - 4 * (α * m + β) ^ 2 * β
          = 2 * (α * m) ^ 3 + 5 * (α * m) ^ 2 * β + 4 * (α * m) * β ^ 2 := by ring
      rw [e]
      positivity
    linarith
  have t1 : 0 ≤ β * ((2 * (α * m + β) - α) * (2 * α * m + β) * (α * m + 2 * β)
      - 4 * (α * m + β) ^ 2 * β) * F := mul_nonneg (mul_nonneg hβ.le hKF) hF
  have t2 : 0 ≤ (α * m + β) * (2 * (α * m + β) * (2 * α * m + β) * Q
      - (2 * α * m + β) ^ 2 * S + 2 * (α * m + β) * β * R - β * (2 * α * m + β) * Vz) :=
    mul_nonneg hA.le (by linarith)
  have t3 : 0 ≤ 2 * (α * m + β) ^ 2 * β * (2 * β * F - R) :=
    mul_nonneg (by positivity) (by linarith)
  have t4 : 0 ≤ 4 * (α * m + β) ^ 2 * (2 * α * m + β)
      * (β * P - (β - α) * Dbar - α * β / 2 * N - Q / 2) :=
    mul_nonneg (by positivity) (by linarith)
  have t5 : 0 ≤ (α * m + β) * (2 * α * m + β) ^ 2 * (S - 2 * α * Dbar) :=
    mul_nonneg (by positivity) (by linarith)
  rw [← sub_nonneg]
  have key : (1 - 1 / (2 * (α * m + β)) * α) *
        (F + (2 * (α * m + β) ^ 2 / ((2 * (α * m + β) - α) * m)) * N)
      - ((1 - 1 / m) * F + (1 / m) * Dbar
        + (2 * (α * m + β) ^ 2 / ((2 * (α * m + β) - α) * m)) *
          (N - 2 * (1 / (2 * (α * m + β))) * P + (1 / (2 * (α * m + β))) ^ 2 * Vz))
      = (β * ((2 * (α * m + β) - α) * (2 * α * m + β) * (α * m + 2 * β)
          - 4 * (α * m + β) ^ 2 * β) * F
        + (α * m + β) * (2 * (α * m + β) * (2 * α * m + β) * Q
          - (2 * α * m + β) ^ 2 * S + 2 * (α * m + β) * β * R - β * (2 * α * m + β) * Vz)
        + 2 * (α * m + β) ^ 2 * β * (2 * β * F - R)
        + 4 * (α * m + β) ^ 2 * (2 * α * m + β)
          * (β * P - (β - α) * Dbar - α * β / 2 * N - Q / 2)
        + (α * m + β) * (2 * α * m + β) ^ 2 * (S - 2 * α * Dbar))
        / (β * (2 * α * m + β) * (2 * (α * m + β) * (2 * (α * m + β) - α) * m)) := by
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  linarith [t1, t2, t3, t4, t5]

lemma saga_st_avg {m : ℕ} (hm : 0 < m) (a b C W : Fin m → ℝ) (F c γ N : ℝ)
    (hF : F = (1 / (m : ℝ)) * ∑ j, b j) :
    (1 / (m : ℝ)) * ∑ j, (F + (1 / (m : ℝ)) * (a j - b j) + c * (N - 2 * γ * C j + γ ^ 2 * W j))
      = (1 - 1 / (m : ℝ)) * F + (1 / (m : ℝ)) * ((1 / (m : ℝ)) * ∑ j, a j)
        + c * (N - 2 * γ * ((1 / (m : ℝ)) * ∑ j, C j) + γ ^ 2 * ((1 / (m : ℝ)) * ∑ j, W j)) := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have h1 : ∀ j, (F + (1 / (m : ℝ)) * (a j - b j) + c * (N - 2 * γ * C j + γ ^ 2 * W j))
      = (F + c * N) + ((1 / (m : ℝ)) * a j + ((-(1 / (m : ℝ))) * b j
        + ((-(2 * c * γ)) * C j + (c * γ ^ 2) * W j))) := fun j => by ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [hF]
  field_simp
  ring

lemma saga_st_avg_le {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) (h : ∀ j, a j ≤ b j) :
    (1 / (m : ℝ)) * ∑ j, a j ≤ (1 / (m : ℝ)) * ∑ j, b j := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => h j)) (by positivity)

lemma saga_st_lin {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) (p q : ℝ) :
    (1 / (m : ℝ)) * ∑ j, (p * a j + q + b j / 2)
      = p * ((1 / (m : ℝ)) * ∑ j, a j) + q + ((1 / (m : ℝ)) * ∑ j, b j) / 2 := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma saga_st_lin2 {m : ℕ} (a : Fin m → ℝ) (p : ℝ) :
    (1 / (m : ℝ)) * ∑ j, p * a j = p * ((1 / (m : ℝ)) * ∑ j, a j) := by
  rw [← Finset.mul_sum]; ring

lemma saga_st_lin3 {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (q : ℝ) :
    (1 / (m : ℝ)) * ∑ j, (a j - q) = (1 / (m : ℝ)) * ∑ j, a j - q := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

lemma saga_aux_step {m : ℕ} (hm : 0 < m) (f : Fin m → E → ℝ) (α β : ℝ) (hα : 0 < α)
    (hβ : 0 < β) (hαβ : α ≤ β)
    (hf_diff : ∀ i, Differentiable ℝ (f i))
    (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
    (hf_sc : ∀ i, StrongConvexOn Set.univ α (f i))
    (xs x : E) (ph : Fin m → E) :
    (1 / (m : ℝ)) * ∑ j, ((1 / (m : ℝ)) * ∑ i, (f i (ph i) - f i xs
          - inner ℝ (gradient (f i) xs) (ph i - xs))
        + (1 / (m : ℝ)) * ((f j x - f j xs - inner ℝ (gradient (f j) xs) (x - xs))
          - (f j (ph j) - f j xs - inner ℝ (gradient (f j) xs) (ph j - xs)))
        + (2 * (α * m + β) ^ 2 / ((2 * (α * m + β) - α) * m)) *
          ‖x - (1 / (2 * (α * m + β))) • (gradient (f j) x - gradient (f j) (ph j)
            + (1 / (m : ℝ)) • ∑ i, gradient (f i) (ph i))
            - (xs - (1 / (2 * (α * m + β))) • ((1 / (m : ℝ)) • ∑ i, gradient (f i) xs))‖ ^ 2)
      ≤ (1 - 1 / (2 * (α * m + β)) * α) *
        ((1 / (m : ℝ)) * ∑ i, (f i (ph i) - f i xs - inner ℝ (gradient (f i) xs) (ph i - xs))
          + (2 * (α * m + β) ^ 2 / ((2 * (α * m + β) - α) * m)) * ‖x - xs‖ ^ 2) := by
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmpos
  have hfi := fun i => saga_aux_fi (f i) α β hα hβ hαβ (hf_diff i) (hf_smooth i) (hf_sc i)
  obtain ⟨Y, hY⟩ : ∃ Y : Fin m → E, ∀ j, Y j = gradient (f j) x - gradient (f j) xs :=
    ⟨fun j => gradient (f j) x - gradient (f j) xs, fun j => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Fin m → E, ∀ j, X j = gradient (f j) (ph j) - gradient (f j) xs :=
    ⟨fun j => gradient (f j) (ph j) - gradient (f j) xs, fun j => rfl⟩
  have hvec : ∀ j, x - (1 / (2 * (α * m + β))) • (gradient (f j) x - gradient (f j) (ph j)
            + (1 / (m : ℝ)) • ∑ i, gradient (f i) (ph i))
            - (xs - (1 / (2 * (α * m + β))) • ((1 / (m : ℝ)) • ∑ i, gradient (f i) xs))
      = (x - xs) - (1 / (2 * (α * m + β))) • (Y j - X j + (1 / (m : ℝ)) • ∑ i, X i) := by
    intro j
    simp only [hY, hX, Finset.sum_sub_distrib]
    module
  have hnorm : ∀ (r : ℝ) (v w : E),
      ‖v - r • w‖ ^ 2 = ‖v‖ ^ 2 - 2 * r * inner ℝ w v + r ^ 2 * ‖w‖ ^ 2 := by
    intro r v w
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm w v]
    ring
  simp_rw [hvec, hnorm]
  rw [saga_st_avg hm _ _ _ _ _ _ _ _ rfl]
  have hCsum : ∑ j, inner ℝ (Y j - X j + (1 / (m:ℝ)) • ∑ i, X i) (x - xs)
      = ∑ j, inner ℝ (Y j) (x - xs) := by
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, sum_inner,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [hCsum]
  have hF : 0 ≤ (1 / (m:ℝ)) * ∑ i, (f i (ph i) - f i xs
      - inner ℝ (gradient (f i) xs) (ph i - xs)) := by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    have h := (hfi i).2.1 xs (ph i)
    have : 0 ≤ α / 2 * ‖ph i - xs‖ ^ 2 := by positivity
    linarith
  have hR : (1 / (m:ℝ)) * ∑ j, ‖X j‖ ^ 2 ≤ 2 * β * ((1 / (m:ℝ)) * ∑ i, (f i (ph i) - f i xs
      - inner ℝ (gradient (f i) xs) (ph i - xs))) := by
    rw [← saga_st_lin2]
    apply saga_st_avg_le hm
    intro j
    rw [hX]
    exact (hfi j).2.2.1 xs (ph j)
  have hP : (β - α) * ((1 / (m:ℝ)) * ∑ j, (f j x - f j xs - inner ℝ (gradient (f j) xs) (x - xs)))
      + α * β / 2 * ‖x - xs‖ ^ 2 + ((1 / (m:ℝ)) * ∑ j, ‖Y j‖ ^ 2) / 2
      ≤ β * ((1 / (m:ℝ)) * ∑ j, inner ℝ (Y j) (x - xs)) := by
    rw [← saga_st_lin hm, ← saga_st_lin2]
    apply saga_st_avg_le hm
    intro j
    rw [hY]
    exact (hfi j).2.2.2 x xs
  have hS : 2 * α * ((1 / (m:ℝ)) * ∑ j, (f j x - f j xs - inner ℝ (gradient (f j) xs) (x - xs)))
      ≤ ‖(1 / (m:ℝ)) • ∑ j, Y j‖ ^ 2 := by
    have h1 : ∀ j, f j x - f j xs - inner ℝ (gradient (f j) xs) (x - xs)
        ≤ inner ℝ (Y j) (x - xs) - α / 2 * ‖x - xs‖ ^ 2 := by
      intro j
      have h := (hfi j).2.1 x xs
      have e1 : inner ℝ (gradient (f j) x) (xs - x) = - inner ℝ (gradient (f j) x) (x - xs) := by
        rw [← inner_neg_right, neg_sub]
      rw [e1, norm_sub_rev] at h
      rw [hY, inner_sub_left]
      linarith
    have h2 := saga_st_avg_le hm _ _ h1
    rw [saga_st_lin3 hm] at h2
    have h3 : 0 ≤ ‖(1 / (m:ℝ)) • ∑ j, Y j - α • (x - xs)‖ ^ 2 := by positivity
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul α (x - xs), mul_pow, Real.norm_eq_abs,
      sq_abs, real_inner_smul_left, sum_inner] at h3
    nlinarith [mul_le_mul_of_nonneg_left h2 hα.le]
  have hε : 0 < (2 * α * m + β) / β := by positivity
  have hV := saga_aux_variance hm Y X ((2 * α * m + β) / β) hε
  exact saga_aux_combine (m:ℝ) α β _ _ _ _ _ _ _ _ hm1 hα hβ hαβ hF hR hP hS hV

lemma saga_pr_factor {Ω : Type*} {m : ℕ} (I : ℕ → Ω → Fin m)
    (t : ℕ) (Y : Ω → ℝ) (hY : ∀ ω ω', (∀ s < t, I s ω = I s ω') → Y ω = Y ω') :
    ∃ K : (Finset.range t → Fin m) → ℝ, ∀ ω, Y ω = K (fun i => I i ω) := by
  classical
  refine ⟨Function.extend (fun ω (i : Finset.range t) => I i ω) Y 0, fun ω => ?_⟩
  have hF : Function.FactorsThrough Y (fun ω (i : Finset.range t) => I i ω) := by
    intro a b hab
    apply hY
    intro s hs
    exact congrFun hab ⟨s, Finset.mem_range.mpr hs⟩
  exact (hF.extend_apply 0 ω).symm

lemma saga_aux_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {m : ℕ} (I : ℕ → Ω → Fin m) (hI_meas : ∀ t, Measurable (I t))
    (t : ℕ) (Y : Ω → ℝ) (hY : ∀ ω ω', (∀ s < t, I s ω = I s ω') → Y ω = Y ω') :
    Integrable Y μ := by
  obtain ⟨K, hK⟩ := saga_pr_factor I t Y hY
  have hJ : Measurable (fun ω (i : Finset.range t) => I i ω) :=
    measurable_pi_lambda _ (fun i => hI_meas i)
  have hYK : Y = K ∘ (fun ω (i : Finset.range t) => I i ω) := funext hK
  rw [hYK]
  exact (Integrable.of_finite).comp_measurable hJ

lemma saga_aux_indep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {m : ℕ} (I : ℕ → Ω → Fin m) (hI_meas : ∀ t, Measurable (I t))
    (hI_ind : ProbabilityTheory.iIndepFun I μ)
    (hI_unif : ∀ t i, μ ((I t) ⁻¹' {i}) = (m : ENNReal)⁻¹) (t : ℕ)
    (Y : Ω → ℝ) (hY : ∀ ω ω', (∀ s < t, I s ω = I s ω') → Y ω = Y ω') (j : Fin m) :
    ∫ ω, (if I t ω = j then Y ω else 0) ∂μ = (1 / (m : ℝ)) * ∫ ω, Y ω ∂μ := by
  classical
  obtain ⟨K, hK⟩ := saga_pr_factor I t Y hY
  have hJ : Measurable (fun ω (i : Finset.range t) => I i ω) :=
    measurable_pi_lambda _ (fun i => hI_meas i)
  have hind0 := ProbabilityTheory.iIndepFun.indepFun_finset {t} (Finset.range t)
    (by simp) hI_ind hI_meas
  have hev : Measurable (fun g : (({t} : Finset ℕ) → Fin m) => g ⟨t, Finset.mem_singleton_self t⟩) :=
    measurable_pi_apply _
  have hind : ProbabilityTheory.IndepFun (I t) (fun ω (i : Finset.range t) => I i ω) μ :=
    hind0.comp hev measurable_id
  have hfun : ∀ ω, (if I t ω = j then Y ω else 0)
      = (fun i => if i = j then (1:ℝ) else 0) (I t ω) * K (fun (i : Finset.range t) => I i ω) := by
    intro ω
    by_cases h : I t ω = j <;> simp [h, hK ω]
  have key := hind.integral_fun_comp_mul_comp (f := fun i => if i = j then (1:ℝ) else 0) (g := K)
    (hI_meas t).aemeasurable hJ.aemeasurable
    (Measurable.of_discrete).aestronglyMeasurable (Measurable.of_discrete).aestronglyMeasurable
  have h1 : ∫ ω, (fun i => if i = j then (1:ℝ) else 0) (I t ω) ∂μ = 1 / (m : ℝ) := by
    have hs : MeasurableSet ((I t) ⁻¹' {j}) := hI_meas t (measurableSet_singleton j)
    have : (fun ω => (fun i => if i = j then (1:ℝ) else 0) (I t ω))
        = ((I t) ⁻¹' {j}).indicator (1 : Ω → ℝ) := by
      funext ω
      simp [Set.indicator]
    rw [this, integral_indicator_one hs, measureReal_def, hI_unif t j, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, one_div]
  have h2 : ∫ ω, K (fun (i : Finset.range t) => I i ω) ∂μ = ∫ ω, Y ω ∂μ := by
    congr 1
    funext ω
    exact (hK ω).symm
  calc ∫ ω, (if I t ω = j then Y ω else 0) ∂μ
      = ∫ ω, (fun i => if i = j then (1:ℝ) else 0) (I t ω)
          * K (fun (i : Finset.range t) => I i ω) ∂μ := by
        congr 1
        funext ω
        exact hfun ω
    _ = (∫ ω, (fun i => if i = j then (1:ℝ) else 0) (I t ω) ∂μ)
          * ∫ ω, K (fun (i : Finset.range t) => I i ω) ∂μ := key
    _ = (1 / (m : ℝ)) * ∫ ω, Y ω ∂μ := by rw [h1, h2]

noncomputable def sagaPhi {Ω F ι : Type*} [DecidableEq ι] (x : ℕ → Ω → F) (I : ℕ → Ω → ι) :
    ℕ → ι → Ω → F
  | 0, _, ω => x 0 ω
  | t + 1, i, ω => if i = I t ω then x t ω else sagaPhi x I t i ω

lemma saga_aux_grad_sum {m : ℕ} (f : Fin m → E → ℝ) (hf : ∀ i, Differentiable ℝ (f i)) (xs : E) :
    HasGradientAt (fun z => (1 / (m : ℝ)) * ∑ i, f i z)
      ((1 / (m : ℝ)) • ∑ i, gradient (f i) xs) xs := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun z => ∑ i, f i z) (∑ i, fderiv ℝ (f i) xs) xs :=
    HasFDerivAt.fun_sum (fun i _ => (hf i xs).hasFDerivAt)
  have h2 := h1.const_mul (1 / (m : ℝ))
  convert h2 using 1
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [gradient]

lemma saga_aux_opt (F h : E → ℝ) (s xs : E) (L : ℝ)
    (hdesc : ∀ y, F y ≤ F xs + inner ℝ s (y - xs) + L / 2 * ‖y - xs‖ ^ 2)
    (hh : ConvexOn ℝ Set.univ h) (hmin : IsMinOn (fun z => F z + h z) Set.univ xs) (z : E) :
    h xs - inner ℝ s (z - xs) ≤ h z := by
  have key := saga_aux_limit (a := h z - h xs + inner ℝ s (z - xs))
    (b := L / 2 * ‖z - xs‖ ^ 2) ?_
  · linarith
  intro t ht0 ht1
  have hy : xs + t • (z - xs) = (1 - t) • xs + t • z := by
    rw [smul_sub, sub_smul, one_smul]; abel
  have hmin' := isMinOn_iff.mp hmin (xs + t • (z - xs)) (Set.mem_univ _)
  simp only at hmin'
  have hconv := hh.2 (Set.mem_univ xs) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
    (by ring : (1 - t) + t = 1)
  rw [← hy] at hconv
  simp only [smul_eq_mul] at hconv
  have hd := hdesc (xs + t • (z - xs))
  have e1 : xs + t • (z - xs) - xs = t • (z - xs) := by abel
  rw [e1, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hd
  have h2 : 0 ≤ t * (inner ℝ s (z - xs) + (h z - h xs) + t * (L / 2 * ‖z - xs‖ ^ 2)) := by
    nlinarith
  have h4 := (mul_nonneg_iff_of_pos_left ht0).mp h2
  linarith [h4]

set_option linter.unusedVariables false in
theorem saga_strongly_convex_distance_bound
  {k m n : ℕ}
  {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω)
  [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (h : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (α β : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hβ_pos : β > 0)
  (hα_pos : α > 0)
  (hα_le_β : α ≤ β)
  (hm_pos : m > 0)
  (h_saga_seq :
    IsSAGASequence μ f h x g I (1 / (2 * (α * (m : ℝ) + β))))
  (hf_differentiable : ∀ i, Differentiable ℝ (f i))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
  (hf_each_strongly_convex :
    ∀ i, StrongConvexOn Set.univ α (f i))
  (hh_convex : ConvexOn ℝ Set.univ h)
  (hx_star : IsMinOn (fun z => finiteSumObjective f z + h z) Set.univ x_star)
  (hf_sum_x_int :
    ∀ t, Integrable (fun ω => finiteSumObjective f (x t ω)) μ)
  (hx_dist_int :
    ∀ t, Integrable (fun ω => ‖x t ω - x_star‖ ^ 2) μ) :
  let f_sum := finiteSumObjective f
  ∫ ω, ‖x k ω - x_star‖ ^ 2 ∂μ ≤
    (1 - α / (2 * (α * (m : ℝ) + β))) ^ k *
      (‖x0 - x_star‖ ^ 2 +
        ((m : ℝ) / (α * (m : ℝ) + β)) *
          (f_sum x0 -
            inner ℝ (gradient f_sum x_star) (x0 - x_star) -
            f_sum x_star)) := by
  intro f_sum
  obtain ⟨-, -, hI_meas, ⟨hg0, hg_upd, hg_keep, hx_upd⟩, hI_ind, -, hI_unif⟩ := h_saga_seq
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
  have hA : 0 < α * (m : ℝ) + β := by positivity
  have hγ : 0 < 1 / (2 * (α * (m : ℝ) + β)) := by positivity
  have hfi := fun i => saga_aux_fi (f i) α β hα_pos hβ_pos hα_le_β (hf_differentiable i)
    (hf_smooth i) (hf_each_strongly_convex i)
  -- gradient of the average
  have hgrad : gradient f_sum x_star = (1 / (m : ℝ)) • ∑ i, gradient (f i) x_star :=
    (saga_aux_grad_sum f hf_differentiable x_star).gradient
  have hdesc_sum : ∀ y, f_sum y ≤ f_sum x_star + inner ℝ (gradient f_sum x_star) (y - x_star)
      + β / 2 * ‖y - x_star‖ ^ 2 := by
    intro y
    rw [hgrad, real_inner_smul_left, sum_inner]
    have h1 : ∑ i, f i y ≤ ∑ i, (f i x_star + inner ℝ (gradient (f i) x_star) (y - x_star)
        + β / 2 * ‖y - x_star‖ ^ 2) := Finset.sum_le_sum (fun i _ => (hfi i).1 x_star y)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / m)
    simp only [f_sum, finiteSumObjective]
    have h3 : 1 / (m : ℝ) * (m * (β / 2 * ‖y - x_star‖ ^ 2)) = β / 2 * ‖y - x_star‖ ^ 2 := by
      field_simp
    nlinarith [h2, h3]
  have hopt := saga_aux_opt f_sum h (gradient f_sum x_star) x_star β hdesc_sum hh_convex hx_star
  rw [hgrad] at hopt
  set γ : ℝ := 1 / (2 * (α * (m : ℝ) + β)) with hγ_def
  set c : ℝ := 2 * (α * m + β) ^ 2 / ((2 * (α * m + β) - α) * m) with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    have : 0 < 2 * (α * m + β) - α := by nlinarith
    positivity
  -- stored gradients are gradients at the points `sagaPhi`
  have hg_ph : ∀ t i ω, g t i ω = gradient (f i) (sagaPhi x I t i ω) := by
    intro t
    induction t with
    | zero => intro i ω; simp only [sagaPhi]; exact hg0 i ω
    | succ t ih =>
      intro i ω
      simp only [sagaPhi]
      by_cases hi : i = I t ω
      · rw [if_pos hi]; subst hi; exact hg_upd t ω
      · rw [if_neg hi, hg_keep t i ω hi]; exact ih i ω
  let W : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun t ω => x t ω - γ • (gradient (f (I t ω)) (x t ω)
    - gradient (f (I t ω)) (sagaPhi x I t (I t ω) ω)
    + (1 / (m : ℝ)) • ∑ i, gradient (f i) (sagaPhi x I t i ω))
  have hprox : ∀ t ω z, h (x (t + 1) ω) + γ⁻¹ * inner ℝ (W t ω - x (t + 1) ω) (z - x (t + 1) ω)
      ≤ h z := by
    intro t ω
    have h1 := hx_upd t ω
    simp only at h1
    rw [hg_upd t ω] at h1
    simp only [hg_ph t] at h1
    exact saga_aux_prox_subgrad h hh_convex γ (W t ω) (x (t + 1) ω)
      (saga_aux_prox_real h γ _ _ h1)
  have hfact : ∀ t ω ω', (∀ s < t, I s ω = I s ω') →
      x t ω = x t ω' ∧ ∀ i, sagaPhi x I t i ω = sagaPhi x I t i ω' := by
    intro t
    induction t with
    | zero =>
      intro ω ω' _
      exact ⟨by rw [hx0, hx0], fun i => by simp only [sagaPhi]; rw [hx0, hx0]⟩
    | succ t ih =>
      intro ω ω' hag
      have hag' : ∀ s < t, I s ω = I s ω' := fun s hs => hag s (by omega)
      have hIt : I t ω = I t ω' := hag t (by omega)
      obtain ⟨hxt, hph⟩ := ih ω ω' hag'
      have hph' : ∀ i, sagaPhi x I (t + 1) i ω = sagaPhi x I (t + 1) i ω' := by
        intro i; simp only [sagaPhi]; rw [hIt, hxt, hph i]
      refine ⟨?_, hph'⟩
      have hW : W t ω = W t ω' := by
        simp only [W]; rw [hIt, hxt]; simp only [hph]
      exact saga_aux_prox_unique h γ hγ (W t ω) (x (t + 1) ω) (x (t + 1) ω') (hprox t ω)
        (by rw [hW]; exact hprox t ω')
  -- Lyapunov function
  let D : Fin m → EuclideanSpace ℝ (Fin n) → ℝ := fun i z =>
    f i z - f i x_star - inner ℝ (gradient (f i) x_star) (z - x_star)
  let F : ℕ → Ω → ℝ := fun t ω => (1 / (m : ℝ)) * ∑ i, D i (sagaPhi x I t i ω)
  let T : ℕ → Ω → ℝ := fun t ω => F t ω + c * ‖x t ω - x_star‖ ^ 2
  have hD_nonneg : ∀ i z, 0 ≤ D i z := by
    intro i z
    have h1 := (hfi i).2.1 x_star z
    have h2 : 0 ≤ α / 2 * ‖z - x_star‖ ^ 2 := by positivity
    simp only [D]; linarith
  have hF_nonneg : ∀ t ω, 0 ≤ F t ω := by
    intro t ω
    simp only [F]
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hD_nonneg i (sagaPhi x I t i ω))
    positivity
  have hT_dep : ∀ t ω ω', (∀ s < t, I s ω = I s ω') → T t ω = T t ω' := by
    intro t ω ω' hag
    obtain ⟨hxt, hph⟩ := hfact t ω ω' hag
    simp only [T, F, hxt, hph]
  have hT_int : ∀ t, Integrable (T t) μ := fun t =>
    saga_aux_integrable μ I hI_meas t (T t) (hT_dep t)
  -- one step of the recursion
  have hstep : ∀ t, ∫ ω, T (t + 1) ω ∂μ ≤ (1 - γ * α) * ∫ ω, T t ω ∂μ := by
    intro t
    let Φ : Fin m → Ω → ℝ := fun j ω => F t ω + (1 / (m : ℝ)) * (D j (x t ω)
      - D j (sagaPhi x I t j ω)) + c * ‖x t ω - γ • (gradient (f j) (x t ω)
        - gradient (f j) (sagaPhi x I t j ω) + (1 / (m : ℝ)) • ∑ i, gradient (f i) (sagaPhi x I t i ω))
        - (x_star - γ • ((1 / (m : ℝ)) • ∑ i, gradient (f i) x_star))‖ ^ 2
    have hΦ_dep : ∀ j ω ω', (∀ s < t, I s ω = I s ω') → Φ j ω = Φ j ω' := by
      intro j ω ω' hag
      obtain ⟨hxt, hph⟩ := hfact t ω ω' hag
      simp only [Φ, F, hxt, hph]
    have hΦ_int : ∀ j, Integrable (Φ j) μ := fun j =>
      saga_aux_integrable μ I hI_meas t (Φ j) (hΦ_dep j)
    have hΨ_int : ∀ j, Integrable (fun ω => if I t ω = j then Φ j ω else 0) μ := by
      intro j
      refine saga_aux_integrable μ I hI_meas (t + 1) _ ?_
      intro ω ω' hag
      have hIt : I t ω = I t ω' := hag t (by omega)
      rw [hIt, hΦ_dep j ω ω' (fun s hs => hag s (by omega))]
    -- pointwise bound
    have hpt : ∀ ω, T (t + 1) ω ≤ ∑ j, (if I t ω = j then Φ j ω else 0) := by
      intro ω
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      set j := I t ω with hj
      have hF1 : F (t + 1) ω = F t ω + (1 / (m : ℝ)) * (D j (x t ω) - D j (sagaPhi x I t j ω)) := by
        have e : ∀ i, D i (sagaPhi x I (t + 1) i ω) = D i (sagaPhi x I t i ω)
            + (if j = i then D i (x t ω) - D i (sagaPhi x I t i ω) else 0) := by
          intro i
          simp only [sagaPhi]
          by_cases hi : i = I t ω
          · rw [if_pos hi, if_pos (by rw [hj, hi])]; ring
          · rw [if_neg hi, if_neg (by rw [hj]; exact fun h' => hi h'.symm)]; ring
        simp only [F]
        rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        ring
      have hnx : ‖x (t + 1) ω - x_star‖ ^ 2 ≤ ‖W t ω - (x_star - γ • ((1 / (m : ℝ)) •
          ∑ i, gradient (f i) x_star))‖ ^ 2 :=
        saga_aux_prox_nonexp h γ hγ (W t ω) (x (t + 1) ω) x_star _ (hprox t ω) hopt
      show F (t + 1) ω + c * ‖x (t + 1) ω - x_star‖ ^ 2 ≤ Φ j ω
      simp only [Φ]
      rw [hF1]
      have := mul_le_mul_of_nonneg_left hnx hc_pos.le
      simp only [W] at this
      rw [← hj] at this
      linarith
    have hdet : ∀ ω, (1 / (m : ℝ)) * ∑ j, Φ j ω ≤ (1 - γ * α) * T t ω := by
      intro ω
      exact saga_aux_step hm_pos f α β hα_pos hβ_pos hα_le_β hf_differentiable hf_smooth
        hf_each_strongly_convex x_star (x t ω) (fun i => sagaPhi x I t i ω)
    calc ∫ ω, T (t + 1) ω ∂μ ≤ ∫ ω, ∑ j, (if I t ω = j then Φ j ω else 0) ∂μ :=
          integral_mono (hT_int (t + 1)) (integrable_finset_sum _ (fun j _ => hΨ_int j)) hpt
      _ = ∑ j, ∫ ω, (if I t ω = j then Φ j ω else 0) ∂μ :=
          integral_finset_sum _ (fun j _ => hΨ_int j)
      _ = ∑ j, (1 / (m : ℝ)) * ∫ ω, Φ j ω ∂μ := by
          apply Finset.sum_congr rfl
          intro j _
          exact saga_aux_indep μ I hI_meas hI_ind hI_unif t (Φ j) (hΦ_dep j) j
      _ = ∫ ω, (1 / (m : ℝ)) * ∑ j, Φ j ω ∂μ := by
          rw [integral_const_mul, integral_finset_sum _ (fun j _ => hΦ_int j), Finset.mul_sum]
      _ ≤ ∫ ω, (1 - γ * α) * T t ω ∂μ :=
          integral_mono ((integrable_finset_sum _ (fun j _ => hΦ_int j)).const_mul _)
            ((hT_int t).const_mul _) hdet
      _ = (1 - γ * α) * ∫ ω, T t ω ∂μ := integral_const_mul _ _
  have hρ : 0 ≤ 1 - γ * α := by
    rw [hγ_def]
    have : 1 / (2 * (α * (m : ℝ) + β)) * α ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      nlinarith
    linarith
  have hiter : ∀ t, ∫ ω, T t ω ∂μ ≤ (1 - γ * α) ^ t * ∫ ω, T 0 ω ∂μ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc ∫ ω, T (t + 1) ω ∂μ ≤ (1 - γ * α) * ∫ ω, T t ω ∂μ := hstep t
        _ ≤ (1 - γ * α) * ((1 - γ * α) ^ t * ∫ ω, T 0 ω ∂μ) :=
          mul_le_mul_of_nonneg_left ih hρ
        _ = (1 - γ * α) ^ (t + 1) * ∫ ω, T 0 ω ∂μ := by ring
  -- the initial value
  set D0 : ℝ := f_sum x0 - inner ℝ ((1 / (m : ℝ)) • ∑ i, gradient (f i) x_star) (x0 - x_star)
    - f_sum x_star with hD0_def
  have hT0 : ∀ ω, T 0 ω = D0 + c * ‖x0 - x_star‖ ^ 2 := by
    intro ω
    simp only [T, F, D, sagaPhi, hx0, hD0_def, f_sum, finiteSumObjective]
    rw [real_inner_smul_left, sum_inner, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hD0_nonneg : 0 ≤ D0 := by
    have := hF_nonneg 0 (Classical.arbitrary Ω)
    have h2 := hT0 (Classical.arbitrary Ω)
    simp only [T] at h2
    rw [hx0] at h2
    linarith
  have hint0 : ∫ ω, T 0 ω ∂μ = D0 + c * ‖x0 - x_star‖ ^ 2 := by
    simp only [hT0, integral_const, probReal_univ, one_smul]
  have hlow : c * ∫ ω, ‖x k ω - x_star‖ ^ 2 ∂μ ≤ ∫ ω, T k ω ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono ((hx_dist_int k).const_mul c) (hT_int k)
    intro ω
    simp only [T]
    linarith [hF_nonneg k ω]
  have hfinal := hlow.trans ((hiter k).trans_eq (by rw [hint0]))
  -- rearrange
  rw [hgrad]
  have hρ' : (1 - α / (2 * (α * (m : ℝ) + β))) = 1 - γ * α := by rw [hγ_def]; ring
  rw [hρ', ← hD0_def]
  have hpow : 0 ≤ (1 - γ * α) ^ k := pow_nonneg hρ k
  have hcm : 1 / c ≤ (m : ℝ) / (α * m + β) := by
    rw [hc_def, one_div_div, div_le_div_iff₀ (by nlinarith) hA]
    nlinarith [mul_pos hα_pos (mul_pos hmR hA)]
  have hfinal' : ∫ ω, ‖x k ω - x_star‖ ^ 2 ∂μ ≤
      (1 - γ * α) ^ k * (‖x0 - x_star‖ ^ 2 + (1 / c) * D0) := by
    rw [← mul_le_mul_iff_of_pos_left hc_pos]
    calc c * ∫ ω, ‖x k ω - x_star‖ ^ 2 ∂μ ≤ (1 - γ * α) ^ k * (D0 + c * ‖x0 - x_star‖ ^ 2) :=
          hfinal
      _ = c * ((1 - γ * α) ^ k * (‖x0 - x_star‖ ^ 2 + (1 / c) * D0)) := by
          field_simp
          ring
  calc ∫ ω, ‖x k ω - x_star‖ ^ 2 ∂μ ≤ (1 - γ * α) ^ k * (‖x0 - x_star‖ ^ 2 + (1 / c) * D0) :=
        hfinal'
    _ ≤ (1 - γ * α) ^ k * (‖x0 - x_star‖ ^ 2 + (m : ℝ) / (α * m + β) * D0) := by
        apply mul_le_mul_of_nonneg_left _ hpow
        have := mul_le_mul_of_nonneg_right hcm hD0_nonneg
        linarith

end saga_strongly_convex_distance_bound
