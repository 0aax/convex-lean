import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_2_8`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_2_8` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_2_8`, so the main result is `FCA_chap_D_6_2_8.FCA_chap_D_6_2_8`.
-/

namespace FCA_chap_D_6_2_8

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Filter Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Gradient inequality for differentiable convex functions. -/
lemma FCA_aux_grad_le {h : E → ℝ} (hc : ConvexOn ℝ Set.univ h) (hd : Differentiable ℝ h)
    (y u : E) {t : ℝ} (ht : 0 < t) :
    inner ℝ (gradient h y) u ≤ (h (y + t • u) - h y) / t := by
  set ψ : ℝ → ℝ := fun s => h (y + s • u) with hψ
  have hψc : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, fun a _ b _ p q hp hq hpq => ?_⟩
    have key : y + (p • a + q • b) • u = p • (y + a • u) + q • (y + b • u) := by
      have : q = 1 - p := by linarith
      subst this
      simp only [smul_eq_mul]
      module
    simp only [hψ, key]
    exact hc.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
  have hψd : HasDerivAt ψ (fderiv ℝ h y u) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => y + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add y
    have h2 := (hd (y + (0:ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
    simpa [Function.comp_def] using h2
  have := hψc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ t) ht hψd
  rw [inner_gradient_left (hd y)]
  simpa [slope_def_field, hψ] using this

lemma FCA_aux_val_tendsto (g : ℕ → E → ℝ) (g0 : E → ℝ) (hg : ∀ k, ConvexOn ℝ Set.univ (g k))
    (hg0 : Continuous g0) (hlim : ∀ v, Tendsto (fun k => g k v) atTop (𝓝 (g0 v))) (x : E) :
    Tendsto (fun q : ℕ × E => g q.1 q.2) (atTop ×ˢ 𝓝 x) (𝓝 (g0 x)) := by
  -- upper bound
  have upper : ∀ x : E, ∀ b > g0 x, ∀ᶠ q : ℕ × E in atTop ×ˢ 𝓝 x, g q.1 q.2 < b := by
    intro x b hb
    have hs : {z | g0 z < b} ∈ 𝓝 x := (hg0.isOpen_preimage _ isOpen_Iio).mem_nhds hb
    obtain ⟨bs, hxb, hbs⟩ := exists_mem_interior_convexHull_affineBasis hs
    have h1 : ∀ᶠ k in atTop, ∀ i, g k (bs i) < b := by
      rw [Filter.eventually_all]
      intro i
      have : g0 (bs i) < b := hbs (subset_convexHull ℝ _ (Set.mem_range_self i))
      exact (hlim (bs i)).eventually (eventually_lt_nhds this)
    have h2 : ∀ᶠ y in 𝓝 x, y ∈ convexHull ℝ (Set.range bs) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hxb) interior_subset
    filter_upwards [h1.prod_mk h2] with q hq
    obtain ⟨z, hz, hzq⟩ := (hg q.1).exists_ge_of_mem_convexHull (Set.subset_univ _) hq.2
    obtain ⟨i, rfl⟩ := hz
    exact hzq.trans_lt (hq.1 i)
  refine tendsto_order.2 ⟨fun a ha => ?_, upper x⟩
  -- lower bound
  set δ := (g0 x - a) / 3 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hrefl : Tendsto (fun q : ℕ × E => (q.1, (2:ℝ) • x - q.2)) (atTop ×ˢ 𝓝 x)
      (atTop ×ˢ 𝓝 x) := by
    refine tendsto_fst.prodMk (Tendsto.comp ?_ tendsto_snd)
    have h2x : (2:ℝ) • x - x = x := by rw [two_smul, add_sub_cancel_right]
    have : Tendsto (fun y : E => (2:ℝ) • x - y) (𝓝 x) (𝓝 ((2:ℝ) • x - x)) :=
      (continuous_const.sub continuous_id).tendsto x
    rw [h2x] at this
    exact this
  have e1 : ∀ᶠ q : ℕ × E in atTop ×ˢ 𝓝 x, g q.1 ((2:ℝ) • x - q.2) < g0 x + δ :=
    hrefl.eventually (upper x _ (by linarith))
  have e2 : ∀ᶠ q : ℕ × E in atTop ×ˢ 𝓝 x, g0 x - δ < g q.1 x :=
    tendsto_fst.eventually ((hlim x).eventually (eventually_gt_nhds (by linarith)))
  filter_upwards [e1, e2] with q h1 h2
  have hmid := (hg q.1).2 (Set.mem_univ q.2) (Set.mem_univ ((2:ℝ) • x - q.2))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hpt : (1/2:ℝ) • q.2 + (1/2:ℝ) • ((2:ℝ) • x - q.2) = x := by module
  rw [hpt, smul_eq_mul, smul_eq_mul] at hmid
  linarith

lemma FCA_aux_inner_tendsto (g : ℕ → E → ℝ) (g0 : E → ℝ) (hg : ∀ k, ConvexOn ℝ Set.univ (g k))
    (hgd : ∀ k, Differentiable ℝ (g k)) (hg0 : Differentiable ℝ g0)
    (hlim : ∀ v, Tendsto (fun k => g k v) atTop (𝓝 (g0 v))) (x u : E) :
    Tendsto (fun q : ℕ × E => inner ℝ (gradient (g q.1) q.2) u) (atTop ×ˢ 𝓝 x)
      (𝓝 (inner ℝ (gradient g0 x) u)) := by
  have hval := FCA_aux_val_tendsto g g0 hg hg0.continuous hlim
  have upper : ∀ u : E, ∀ b > inner ℝ (gradient g0 x) u,
      ∀ᶠ q : ℕ × E in atTop ×ˢ 𝓝 x, inner ℝ (gradient (g q.1) q.2) u < b := by
    intro u b hb
    have hψd : HasDerivAt (fun s : ℝ => g0 (x + s • u)) (inner ℝ (gradient g0 x) u) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => x + s • u) u 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add x
      have h2 := (hg0 (x + (0:ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
      rw [inner_gradient_left (hg0 x)]
      simpa [Function.comp_def] using h2
    have hsl := hψd.tendsto_slope_zero_right
    obtain ⟨t, hbt, ht⟩ :=
      ((hsl.eventually (eventually_lt_nhds hb)).and self_mem_nhdsWithin).exists
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hbt
    have ht' : (0:ℝ) < t := ht
    have hshift : Tendsto (fun q : ℕ × E => (q.1, q.2 + t • u)) (atTop ×ˢ 𝓝 x)
        (atTop ×ˢ 𝓝 (x + t • u)) :=
      tendsto_fst.prodMk (((continuous_id.add continuous_const).tendsto x).comp tendsto_snd)
    have hq : Tendsto (fun q : ℕ × E => (g q.1 (q.2 + t • u) - g q.1 q.2) / t) (atTop ×ˢ 𝓝 x)
        (𝓝 ((g0 (x + t • u) - g0 x) / t)) :=
      (((hval (x + t • u)).comp hshift).sub (hval x)).div_const t
    have hlt : (g0 (x + t • u) - g0 x) / t < b := by rwa [div_eq_inv_mul]
    filter_upwards [hq.eventually (eventually_lt_nhds hlt)] with q hq'
    exact (FCA_aux_grad_le (hg q.1) (hgd q.1) q.2 u ht').trans_lt hq'
  refine tendsto_order.2 ⟨fun a ha => ?_, upper u⟩
  have := upper (-u) (-a) (by rw [inner_neg_right]; linarith)
  filter_upwards [this] with q hq
  rw [inner_neg_right] at hq
  linarith

lemma FCA_aux_grad_tendsto (g : ℕ → E → ℝ) (g0 : E → ℝ) (hg : ∀ k, ConvexOn ℝ Set.univ (g k))
    (hgd : ∀ k, Differentiable ℝ (g k)) (hg0 : Differentiable ℝ g0)
    (hlim : ∀ v, Tendsto (fun k => g k v) atTop (𝓝 (g0 v))) (x : E) :
    Tendsto (fun q : ℕ × E => gradient (g q.1) q.2) (atTop ×ˢ 𝓝 x) (𝓝 (gradient g0 x)) := by
  set b := stdOrthonormalBasis ℝ E
  have key : ∀ w : E, ∑ i, inner ℝ w (b i) • b i = w := by
    intro w
    conv_rhs => rw [← b.sum_repr' w]
    simp_rw [real_inner_comm]
  have h : Tendsto (fun q : ℕ × E => ∑ i, inner ℝ (gradient (g q.1) q.2) (b i) • b i)
      (atTop ×ˢ 𝓝 x) (𝓝 (∑ i, inner ℝ (gradient g0 x) (b i) • b i)) :=
    tendsto_finset_sum _ (fun i _ =>
      (FCA_aux_inner_tendsto g g0 hg hgd hg0 hlim x (b i)).smul_const (b i))
  simpa only [key] using h

theorem FCA_chap_D_6_2_8
    (fk : ℕ → (E → ℝ))
    (f : E → ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (fk i))
    (hf_seq_diff : ∀ i, Differentiable ℝ (fk i))
    (hf_diff : Differentiable ℝ f)
    (hf_pointwise : ∀ v, Filter.Tendsto (fun k => fk k v) Filter.atTop (𝓝 (f v))) :
    ∀ (K : Set E), IsCompact K →
    TendstoUniformlyOn (fun k => (fun x => gradient (fk k) x))
    (fun x => gradient f x) Filter.atTop K := by
  intro K hK
  have hfc : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    exact le_of_tendsto_of_tendsto' (hf_pointwise _)
      (((hf_pointwise x).const_smul a).add ((hf_pointwise y).const_smul b))
      (fun k => (hf_convex k).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab)
  have h1 := FCA_aux_grad_tendsto fk f hf_convex hf_seq_diff hf_diff hf_pointwise
  have h2 := FCA_aux_grad_tendsto (fun _ => f) f (fun _ => hfc) (fun _ => hf_diff) hf_diff
    (fun v => tendsto_const_nhds)
  have hloc : TendstoLocallyUniformly (fun k => (fun x => gradient (fk k) x))
      (fun x => gradient f x) atTop := by
    rw [tendstoLocallyUniformly_iff_filter]
    intro x
    rw [tendstoUniformlyOnFilter_iff_tendsto]
    exact ((h2 x).prodMk_nhds (h1 x)).mono_right (nhds_le_uniformity _)
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
    hloc.tendstoLocallyUniformlyOn

end FCA_chap_D_6_2_8
