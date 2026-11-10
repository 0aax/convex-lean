import ConvexStarLib.Defs

/-!
# `saddle_point_mirror_descent_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/saddle_point_mirror_descent_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace saddle_point_mirror_descent_bound`, so the main result is `saddle_point_mirror_descent_bound.saddle_point_mirror_descent_bound`.
-/

namespace saddle_point_mirror_descent_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma fo_opt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {f' : V →L[ℝ] ℝ} {S : Set V} {x : V}
    (hS : Convex ℝ S) (hx : x ∈ S) (hmin : IsMinOn f S x) (hf : HasFDerivAt f f' x) :
    ∀ y ∈ S, 0 ≤ f' (y - x) := by
  intro y hy
  exact hmin.localize.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hS.segment_subset hx hy))

lemma strong_bregman {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : V → ℝ} {Φ' : V →L[ℝ] ℝ} {S : Set V} {m : ℝ} {x y : V}
    (hstrong : StrongConvexOn S m Φ) (hx : x ∈ S) (hy : y ∈ S) (hΦ : HasFDerivAt Φ Φ' x) :
    Φ x + Φ' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ Φ y := by
  set c := m / 2 * ‖y - x‖ ^ 2 with hc
  let q : ℝ → ℝ := fun ε => ε * (Φ y - Φ x) - ε * (1 - ε) * c - (Φ (x + ε • (y - x)) - Φ x)
  have hq0 : q 0 = 0 := by simp [q]
  have hqmin : IsMinOn q (Set.Icc 0 1) 0 := by
    rw [isMinOn_iff]
    intro ε hε
    rw [hq0]
    have := hstrong.2 hx hy (show (0:ℝ) ≤ 1 - ε by linarith [hε.2]) hε.1 (by ring : 1 - ε + ε = 1)
    have hxy : (1 - ε) • x + ε • y = x + ε • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hxy, smul_eq_mul, smul_eq_mul, norm_sub_rev] at this
    simp only [q, c]
    nlinarith [this]
  have hqderiv : HasDerivAt q ((Φ y - Φ x) - c - Φ' (y - x)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => x + ε • (y - x)) (y - x) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
    have h2 : HasDerivAt (fun ε : ℝ => Φ (x + ε • (y - x))) (Φ' (y - x)) 0 := by
      have hΦ' : HasFDerivAt Φ Φ' (x + (0:ℝ) • (y - x)) := by simpa using hΦ
      exact hΦ'.comp_hasDerivAt 0 h1
    have h3 : HasDerivAt (fun ε : ℝ => ε * (Φ y - Φ x) - ε * (1 - ε) * c) ((Φ y - Φ x) - c) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).mul_const (Φ y - Φ x)).sub
        (((hasDerivAt_id (0:ℝ)).mul ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ)))).mul_const c)
      simpa using this
    exact h3.sub (h2.sub_const (Φ x))
  have := fo_opt (convex_Icc 0 1) (by simp) hqmin hqderiv.hasFDerivAt 1 (by simp)
  simp at this
  rw [map_sub]
  linarith

lemma subset_closure_inter_of_convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X D : Set V} (hX : Convex ℝ X) (hD : Convex ℝ D) (hDo : IsOpen D) (hXD : X ⊆ closure D)
    (hne : (X ∩ D).Nonempty) : X ⊆ closure (X ∩ D) := by
  obtain ⟨x0, hx0X, hx0D⟩ := hne
  intro x hx
  have h1 : openSegment ℝ x0 x ⊆ X ∩ D := by
    intro z hz
    refine ⟨hX.segment_subset hx0X hx (openSegment_subset_segment _ _ _ hz), ?_⟩
    have := hD.openSegment_interior_closure_subset_interior (hDo.interior_eq.symm ▸ hx0D) (hXD hx) hz
    rwa [hDo.interior_eq] at this
  exact closure_mono h1 (segment_subset_closure_openSegment (right_mem_segment _ _ _))

lemma md_component {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K D : Set V) (Φ : V → ℝ) (x : ℕ → V) (g : ℕ → V →L[ℝ] ℝ)
    (η m L C : ℝ) (T : ℕ)
    (hKD : K ⊆ D) (hD : IsOpen D)
    (hΦ : DifferentiableOn ℝ Φ D)
    (hstrong : StrongConvexOn K m Φ)
    (hm : 0 < m) (hη : 0 < η)
    (hx0min : IsMinOn Φ K (x 0))
    (hxK : ∀ s, x s ∈ K)
    (hstep : ∀ s, IsMinOn (fun z => η * g s z + bregmanDivergence Φ z (x s)) K (x (s+1)))
    (hg : ∀ s, ‖g s‖ ≤ L)
    (hC : ∀ z ∈ K, Φ z - Φ (x 0) ≤ C) :
    ∀ z ∈ K, η * ∑ s ∈ Finset.range T, g s (x s - z) ≤ C + T * (η ^ 2 * L ^ 2 / (2 * m)) := by
  intro z hz
  have hK : Convex ℝ K := hstrong.1
  have hdiff : ∀ v ∈ K, HasFDerivAt Φ (fderiv ℝ Φ v) v := fun v hv =>
    ((hΦ v (hKD hv)).differentiableAt (hD.mem_nhds (hKD hv))).hasFDerivAt
  have hbreg : ∀ u ∈ K, ∀ v ∈ K, m / 2 * ‖u - v‖ ^ 2 ≤ bregmanDivergence Φ u v := by
    intro u hu v hv
    have := strong_bregman hstrong hv hu (hdiff v hv)
    unfold bregmanDivergence
    linarith
  have hstep_ineq : ∀ s, η * g s (x s - z) ≤ η ^ 2 * L ^ 2 / (2 * m)
      + bregmanDivergence Φ z (x s) - bregmanDivergence Φ z (x (s+1)) := by
    intro s
    have hderiv : HasFDerivAt (fun w => η * g s w + bregmanDivergence Φ w (x s))
        (η • g s + (fderiv ℝ Φ (x (s+1)) - fderiv ℝ Φ (x s))) (x (s+1)) := by
      unfold bregmanDivergence
      have h1 : HasFDerivAt (fun w => η * g s w) (η • g s) (x (s+1)) :=
        (g s).hasFDerivAt.const_mul η
      have h2 : HasFDerivAt (fun w => Φ w - Φ (x s) - fderiv ℝ Φ (x s) (w - x s))
          (fderiv ℝ Φ (x (s+1)) - fderiv ℝ Φ (x s)) (x (s+1)) := by
        have h3 : HasFDerivAt (fun w => fderiv ℝ Φ (x s) (w - x s)) (fderiv ℝ Φ (x s)) (x (s+1)) := by
          have := (fderiv ℝ Φ (x s)).hasFDerivAt.sub_const (x := x (s+1)) ((fderiv ℝ Φ (x s)) (x s))
          convert this using 1
          funext w
          exact map_sub _ _ _
        exact ((hdiff (x (s+1)) (hxK _)).sub_const (Φ (x s))).sub h3
      exact h1.add h2
    have hopt := fo_opt hK (hxK (s+1)) (hstep s) hderiv z hz
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul] at hopt
    have hb := hbreg (x (s+1)) (hxK _) (x s) (hxK s)
    have hgle : g s (x s - x (s+1)) ≤ L * ‖x s - x (s+1)‖ := by
      have h1 := (g s).le_opNorm (x s - x (s+1))
      have h2 := le_abs_self (g s (x s - x (s+1)))
      rw [Real.norm_eq_abs] at h1
      nlinarith [hg s, norm_nonneg (x s - x (s+1))]
    unfold bregmanDivergence at hb ⊢
    rw [norm_sub_rev] at hb
    have hd := norm_nonneg (x s - x (s+1))
    have hsq : 0 ≤ (m * ‖x s - x (s+1)‖ - η * L) ^ 2 := sq_nonneg _
    have key : η * (L * ‖x s - x (s+1)‖) - m / 2 * ‖x s - x (s+1)‖ ^ 2 ≤ η ^ 2 * L ^ 2 / (2 * m) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    simp only [map_sub] at hopt hb hgle ⊢
    nlinarith [mul_le_mul_of_nonneg_left hgle hη.le]
  have hsum : ∀ T : ℕ, η * ∑ s ∈ Finset.range T, g s (x s - z) ≤ T * (η ^ 2 * L ^ 2 / (2 * m))
      + bregmanDivergence Φ z (x 0) - bregmanDivergence Φ z (x T) := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hstep_ineq n
      push_cast
      linarith
  have h0 : bregmanDivergence Φ z (x 0) ≤ C := by
    have hopt0 := fo_opt hK (hxK 0) hx0min (hdiff (x 0) (hxK 0)) z hz
    unfold bregmanDivergence
    linarith [hC z hz]
  have hT : 0 ≤ bregmanDivergence Φ z (x T) := by
    have := hbreg z hz (x T) (hxK T)
    have : 0 ≤ m / 2 * ‖z - x T‖ ^ 2 := by positivity
    linarith
  linarith [hsum T]

set_option linter.unusedVariables false in
theorem saddle_point_mirror_descent_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {t : ℕ}
  (𝓧 : Set E)
  (𝓓x : Set E)
  (𝓨 : Set F)
  (𝓓y : Set F)
  (phi : E → F → ℝ)
  (phix : E → ℝ)
  (phiy : F → ℝ)
  (x_seq : ℕ → E)
  (gx_seq : ℕ → E →L[ℝ] ℝ)
  (y_seq : ℕ → F)
  (gy_seq : ℕ → F →L[ℝ] ℝ)
  (a b Rx Lx Ry Ly : ℝ)
  (hRx_sq : Rx ^ 2 = sSup {v | ∃ z ∈ 𝓧 ∩ 𝓓x, phix z - phix (x_seq 0) = v})
  (hRy_sq : Ry ^ 2 = sSup {v | ∃ z ∈ 𝓨 ∩ 𝓓y, phiy z - phiy (y_seq 0) = v})
  (ha_pos : a > 0) (hb_pos : b > 0)
  (hRx_pos : Rx > 0) (hRy_pos : Ry > 0)
  (hLx_pos : Lx > 0) (hLy_pos : Ly > 0)
  (ht : t ≥ 1)
  (hx_0 : x_seq 0 ∈ 𝓧 ∩ 𝓓x)
  (hy_0 : y_seq 0 ∈ 𝓨 ∩ 𝓓y)
  (h_spmd_seq :
    IsSPMDSequence 𝓧 𝓓x 𝓨 𝓓y phi phix phiy a b (Real.sqrt (2 / (t : ℝ)))
      x_seq gx_seq y_seq gy_seq)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓓x_convex : Convex ℝ 𝓓x)
  (h𝓓x_open : IsOpen 𝓓x)
  (h𝓓x_contains : 𝓧 ⊆ closure 𝓓x)
  (h_interx_nonempty : Set.Nonempty (𝓧 ∩ 𝓓x))
  (h𝓨_compact : IsCompact 𝓨)
  (h𝓨_convex : Convex ℝ 𝓨)
  (h𝓨_nonempty : Set.Nonempty 𝓨)
  (h𝓓y_convex : Convex ℝ 𝓓y)
  (h𝓓y_open : IsOpen 𝓓y)
  (h𝓓y_contains : 𝓨 ⊆ closure 𝓓y)
  (h_intery_nonempty : Set.Nonempty (𝓨 ∩ 𝓓y))
  (hphix_diff : DifferentiableOn ℝ (fun v => a * phix v) 𝓓x)
  (hphix_mirror : IsMirrorMap 𝓓x (fun v => a * phix v))
  (hphix_strong : StrongConvexOn (𝓧 ∩ 𝓓x) 1 phix)
  (hphiy_diff : DifferentiableOn ℝ (fun v => b * phiy v) 𝓓y)
  (hphiy_mirror : IsMirrorMap 𝓓y (fun v => b * phiy v))
  (hphiy_strong : StrongConvexOn (𝓨 ∩ 𝓓y) 1 phiy)
  (hphi_convex_x : ∀ y ∈ 𝓨, ConvexOn ℝ 𝓧 (fun x => phi x y))
  (hphi_concave_y : ∀ x ∈ 𝓧, ConcaveOn ℝ 𝓨 (fun y => phi x y))
  (hgx_bound : ∀ s, ‖gx_seq s‖ ≤ Lx)
  (hgy_bound : ∀ s, ‖gy_seq s‖ ≤ Ly)
  (ha_val : a = Lx / Rx) (hb_val : b = Ly / Ry) :
  sSup ((fun y => phi ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x_seq s) y) '' 𝓨) -
  sInf ((fun x => phi x ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, y_seq s)) '' 𝓧) ≤
  (Rx * Lx + Ry * Ly) * Real.sqrt (2 / t) := by
  obtain ⟨⟨_, h0min⟩, hsubx, hsuby, hmem, hstep⟩ := h_spmd_seq
  set η := Real.sqrt (2 / (t : ℝ)) with hη_def
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hη_pos : 0 < η := Real.sqrt_pos.mpr (by positivity)
  have hη_sq : η ^ 2 = 2 / t := Real.sq_sqrt (by positivity)
  have htη : (t : ℝ) * η ^ 2 = 2 := by rw [hη_sq]; field_simp
  have hxK : ∀ s, x_seq s ∈ 𝓧 ∩ 𝓓x := fun s => (hmem s).1
  have hyK : ∀ s, y_seq s ∈ 𝓨 ∩ 𝓓y := fun s => (hmem s).2
  -- bounds from the definitions of `Rx`, `Ry`
  have hRx_bound : ∀ z ∈ 𝓧 ∩ 𝓓x, phix z - phix (x_seq 0) ≤ Rx ^ 2 := by
    have hbdd : BddAbove {v | ∃ z ∈ 𝓧 ∩ 𝓓x, phix z - phix (x_seq 0) = v} := by
      by_contra hnot
      rw [Real.sSup_of_not_bddAbove hnot] at hRx_sq
      have : Rx ^ 2 > 0 := by positivity
      linarith
    intro z hz
    rw [hRx_sq]
    exact le_csSup hbdd ⟨z, hz, rfl⟩
  have hRy_bound : ∀ z ∈ 𝓨 ∩ 𝓓y, phiy z - phiy (y_seq 0) ≤ Ry ^ 2 := by
    have hbdd : BddAbove {v | ∃ z ∈ 𝓨 ∩ 𝓓y, phiy z - phiy (y_seq 0) = v} := by
      by_contra hnot
      rw [Real.sSup_of_not_bddAbove hnot] at hRy_sq
      have : Ry ^ 2 > 0 := by positivity
      linarith
    intro z hz
    rw [hRy_sq]
    exact le_csSup hbdd ⟨z, hz, rfl⟩
  -- scaled strong convexity
  have hstrong_x : StrongConvexOn (𝓧 ∩ 𝓓x) a (fun v => a * phix v) := by
    refine ⟨hphix_strong.1, ?_⟩
    intro u hu v hv α β hα hβ hαβ
    have := hphix_strong.2 hu hv hα hβ hαβ
    simp only [smul_eq_mul] at this ⊢
    have := mul_le_mul_of_nonneg_left this ha_pos.le
    nlinarith
  have hstrong_y : StrongConvexOn (𝓨 ∩ 𝓓y) b (fun v => b * phiy v) := by
    refine ⟨hphiy_strong.1, ?_⟩
    intro u hu v hv α β hα hβ hαβ
    have := hphiy_strong.2 hu hv hα hβ hαβ
    simp only [smul_eq_mul] at this ⊢
    have := mul_le_mul_of_nonneg_left this hb_pos.le
    nlinarith
  -- the initial points minimize the mirror maps
  have hx0min : IsMinOn (fun v => a * phix v) (𝓧 ∩ 𝓓x) (x_seq 0) := by
    rw [isMinOn_iff]
    intro z hz
    have := isMinOn_iff.mp h0min (z, y_seq 0) ⟨hz, hy_0⟩
    simp only at this
    linarith
  have hy0min : IsMinOn (fun v => b * phiy v) (𝓨 ∩ 𝓓y) (y_seq 0) := by
    rw [isMinOn_iff]
    intro z hz
    have := isMinOn_iff.mp h0min (x_seq 0, z) ⟨hx_0, hz⟩
    simp only at this
    linarith
  -- each step decouples
  have hstepx : ∀ s, IsMinOn (fun z => η * gx_seq s z
      + bregmanDivergence (fun v => a * phix v) z (x_seq s)) (𝓧 ∩ 𝓓x) (x_seq (s+1)) := by
    intro s
    rw [isMinOn_iff]
    intro z hz
    have := isMinOn_iff.mp (hstep s) (z, y_seq (s+1)) ⟨hz, hyK (s+1)⟩
    simp only [prodBregmanDivergence] at this
    linarith
  have hstepy : ∀ s, IsMinOn (fun z => η * gy_seq s z
      + bregmanDivergence (fun v => b * phiy v) z (y_seq s)) (𝓨 ∩ 𝓓y) (y_seq (s+1)) := by
    intro s
    rw [isMinOn_iff]
    intro z hz
    have := isMinOn_iff.mp (hstep s) (x_seq (s+1), z) ⟨hxK (s+1), hz⟩
    simp only [prodBregmanDivergence] at this
    linarith
  have hcompx := md_component (𝓧 ∩ 𝓓x) 𝓓x (fun v => a * phix v) x_seq gx_seq η a Lx (a * Rx ^ 2) t
    Set.inter_subset_right h𝓓x_open hphix_diff hstrong_x ha_pos hη_pos hx0min hxK hstepx hgx_bound
    (fun z hz => by
      have := hRx_bound z hz
      have := mul_le_mul_of_nonneg_left this ha_pos.le
      simp only
      linarith)
  have hcompy := md_component (𝓨 ∩ 𝓓y) 𝓓y (fun v => b * phiy v) y_seq gy_seq η b Ly (b * Ry ^ 2) t
    Set.inter_subset_right h𝓓y_open hphiy_diff hstrong_y hb_pos hη_pos hy0min hyK hstepy hgy_bound
    (fun z hz => by
      have := hRy_bound z hz
      have := mul_le_mul_of_nonneg_left this hb_pos.le
      simp only
      linarith)
  -- extend the bounds to all of `𝓧` and `𝓨`
  have hcompx' : ∀ z ∈ 𝓧, η * ∑ s ∈ Finset.range t, gx_seq s (x_seq s - z)
      ≤ a * Rx ^ 2 + t * (η ^ 2 * Lx ^ 2 / (2 * a)) := by
    have hcl := subset_closure_inter_of_convex h𝓧_convex h𝓓x_convex h𝓓x_open h𝓓x_contains
      h_interx_nonempty
    have hclosed : IsClosed {z | η * ∑ s ∈ Finset.range t, gx_seq s (x_seq s - z)
        ≤ a * Rx ^ 2 + t * (η ^ 2 * Lx ^ 2 / (2 * a))} :=
      isClosed_le (by fun_prop) continuous_const
    intro z hz
    exact closure_minimal hcompx hclosed (hcl hz)
  have hcompy' : ∀ z ∈ 𝓨, η * ∑ s ∈ Finset.range t, gy_seq s (y_seq s - z)
      ≤ b * Ry ^ 2 + t * (η ^ 2 * Ly ^ 2 / (2 * b)) := by
    have hcl := subset_closure_inter_of_convex h𝓨_convex h𝓓y_convex h𝓓y_open h𝓓y_contains
      h_intery_nonempty
    have hclosed : IsClosed {z | η * ∑ s ∈ Finset.range t, gy_seq s (y_seq s - z)
        ≤ b * Ry ^ 2 + t * (η ^ 2 * Ly ^ 2 / (2 * b))} :=
      isClosed_le (by fun_prop) continuous_const
    intro z hz
    exact closure_minimal hcompy hclosed (hcl hz)
  have hRHSx : a * Rx ^ 2 + t * (η ^ 2 * Lx ^ 2 / (2 * a)) = 2 * (Rx * Lx) := by
    rw [ha_val]
    have : (t : ℝ) * (η ^ 2 * Lx ^ 2 / (2 * (Lx / Rx))) = (t * η ^ 2) * (Rx * Lx) / 2 := by
      field_simp
    rw [this, htη]
    field_simp
    ring
  have hRHSy : b * Ry ^ 2 + t * (η ^ 2 * Ly ^ 2 / (2 * b)) = 2 * (Ry * Ly) := by
    rw [hb_val]
    have : (t : ℝ) * (η ^ 2 * Ly ^ 2 / (2 * (Ly / Ry))) = (t * η ^ 2) * (Ry * Ly) / 2 := by
      field_simp
    rw [this, htη]
    field_simp
    ring
  -- the pointwise duality-gap bound
  have key : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨,
      phi ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x_seq s) y
        - phi x ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, y_seq s)
      ≤ (Rx * Lx + Ry * Ly) * η := by
    intro x hx y hy
    have hw0 : ∀ i ∈ Finset.range t, (0:ℝ) ≤ 1 / (t:ℝ) := fun _ _ => by positivity
    have hw1 : ∑ i ∈ Finset.range t, (1 / (t:ℝ)) = 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    have hJx := (hphi_convex_x y hy).map_sum_le hw0 hw1 (fun i _ => (hxK i).1)
    have hJy := (hphi_concave_y x hx).le_map_sum hw0 hw1 (fun i _ => (hyK i).1)
    simp only [smul_eq_mul] at hJx hJy
    rw [← Finset.smul_sum, ← Finset.mul_sum] at hJx hJy
    have hsub : ∀ s, phi (x_seq s) y - phi x (y_seq s)
        ≤ gx_seq s (x_seq s - x) + gy_seq s (y_seq s - y) := by
      intro s
      have h1 := hsubx s x hx
      have h2 := hsuby s y hy
      simp only [map_sub] at h1 h2 ⊢
      linarith
    have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.range t) => hsub s)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    have hx' := hcompx' x hx
    have hy' := hcompy' y hy
    rw [hRHSx] at hx'
    rw [hRHSy] at hy'
    set Sx := ∑ s ∈ Finset.range t, gx_seq s (x_seq s - x)
    set Sy := ∑ s ∈ Finset.range t, gy_seq s (y_seq s - y)
    set P := ∑ s ∈ Finset.range t, phi (x_seq s) y
    set Q := ∑ s ∈ Finset.range t, phi x (y_seq s)
    have h1 : Sx + Sy ≤ t * η * (Rx * Lx + Ry * Ly) := by
      have : η * (Sx + Sy) ≤ η * (t * η * (Rx * Lx + Ry * Ly)) := by
        have e : η * (t * η * (Rx * Lx + Ry * Ly)) = (t * η ^ 2) * (Rx * Lx + Ry * Ly) := by ring
        rw [e, htη]
        linarith
      exact le_of_mul_le_mul_left this hη_pos
    have h2 : (1 / (t : ℝ)) * (P - Q) ≤ (1 / (t : ℝ)) * (Sx + Sy) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h3 : (1 / (t : ℝ)) * (Sx + Sy) ≤ (Rx * Lx + Ry * Ly) * η := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ ht_pos]
      linarith
    have e : (1 / (t : ℝ)) * (P - Q) = (1 / (t : ℝ)) * P - (1 / (t : ℝ)) * Q := by ring
    linarith
  -- pass to `sSup` and `sInf`
  have hne_y : ((fun y => phi ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x_seq s) y) '' 𝓨).Nonempty :=
    h𝓨_nonempty.image _
  have hne_x : ((fun x => phi x ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, y_seq s)) '' 𝓧).Nonempty :=
    h𝓧_nonempty.image _
  have hfinal : sSup ((fun y => phi ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x_seq s) y) '' 𝓨)
      ≤ (Rx * Lx + Ry * Ly) * η
        + sInf ((fun x => phi x ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, y_seq s)) '' 𝓧) := by
    apply csSup_le hne_y
    rintro _ ⟨y, hy, rfl⟩
    have : phi ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x_seq s) y - (Rx * Lx + Ry * Ly) * η
        ≤ sInf ((fun x => phi x ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, y_seq s)) '' 𝓧) := by
      apply le_csInf hne_x
      rintro _ ⟨x, hx, rfl⟩
      have := key x hx y hy
      simp only
      linarith
    linarith
  linarith

end saddle_point_mirror_descent_bound
