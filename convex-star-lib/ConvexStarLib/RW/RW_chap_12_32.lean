import ConvexStarLib.Defs

/-!
# `RW_chap_12_32`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_32` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_32`, so the main result is `RW_chap_12_32.RW_chap_12_32`.
-/

namespace RW_chap_12_32

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Auxiliary lemmas -/

lemma aux_liminf_subset_limsup {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) :
    setLiminf A ⊆ setLimsup A := by
  intro u hu V hV
  exact (hu V hV).frequently

lemma aux_mono_of_lim {Tseq : ℕ → E → Set E} (hmono : ∀ n, IsMonotone (Tseq n))
    {p q : E × E} (hp : p ∈ graphSetLiminf Tseq) (hq : q ∈ graphSetLimsup Tseq) :
    0 ≤ inner ℝ (q.2 - p.2) (q.1 - p.1) := by
  by_contra h
  push_neg at h
  have hcont : Continuous (fun z : (E × E) × (E × E) => inner ℝ (z.2.2 - z.1.2) (z.2.1 - z.1.1)) := by
    fun_prop
  have hev : ∀ᶠ z in 𝓝 (p, q), inner ℝ (z.2.2 - z.1.2) (z.2.1 - z.1.1) < 0 :=
    hcont.continuousAt.eventually (gt_mem_nhds h)
  rw [nhds_prod_eq] at hev
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.mp hev
  have h1 := hp _ hpa
  have h2 := hq _ hpb
  obtain ⟨n, ⟨a, ha, haU⟩, ⟨b, hb, hbV⟩⟩ := (h1.and_frequently h2).exists
  have h3 := hab haU hbV
  have h4 := hmono n a.1 b.1 a.2 b.2 ha hb
  simp only at h3
  linarith

lemma aux_limsup_subset {Tseq : ℕ → E → Set E} {T : E → Set E}
    (hT : IsMaximalMonotone T) (hmono : ∀ n, IsMonotone (Tseq n))
    (hsub : graph T ⊆ graphSetLiminf Tseq) : graphSetLimsup Tseq ⊆ graph T := by
  intro q hq
  by_contra hqT
  obtain ⟨x', v', hv', hlt⟩ := hT.2 q.1 q.2 hqT
  have := aux_mono_of_lim hmono (hsub (show (x', v') ∈ graph T from hv')) hq
  simp only at this
  linarith

lemma aux_mem_resolvent_iff {S : E → Set E} {l : ℝ} {x y : E} :
    x ∈ invMap (addMap idMap (smulMap l S)) y ↔ ∃ w ∈ S x, y = x + l • w := by
  simp only [invMap, addMap, idMap, smulMap, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl, v, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨x, rfl, l • w, ⟨w, hw, rfl⟩, rfl⟩

lemma aux_nonexp {S : E → Set E} (hS : IsMonotone S) {l : ℝ} (hl : 0 ≤ l)
    {x x' w w' : E} (hw : w ∈ S x) (hw' : w' ∈ S x') :
    ‖x - x'‖ ≤ ‖(x + l • w) - (x' + l • w')‖ := by
  have hmon := hS x' x w' w hw' hw
  have e : (x + l • w) - (x' + l • w') = (x - x') + l • (w - w') := by module
  have key : ‖(x - x') + l • (w - w')‖ ^ 2
      = ‖x - x'‖ ^ 2 + 2 * l * inner ℝ (w - w') (x - x') + l ^ 2 * ‖w - w'‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, real_inner_smul_right, real_inner_comm (w - w') (x - x'),
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [e]
  have h2 : ‖x - x'‖ ^ 2 ≤ ‖(x - x') + l • (w - w')‖ ^ 2 := by
    rw [key]
    nlinarith [mul_nonneg hl hmon, mul_nonneg (sq_nonneg l) (sq_nonneg ‖w - w'‖)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h2

lemma aux_unique {S : E → Set E} (hS : IsMonotone S) {l : ℝ} (hl : 0 ≤ l) {y x x' w w' : E}
    (hw : w ∈ S x) (hy : y = x + l • w) (hw' : w' ∈ S x') (hy' : y = x' + l • w') : x = x' := by
  have := aux_nonexp hS hl hw hw'
  rw [← hy, ← hy', sub_self, norm_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

lemma aux_graph_nonempty {S : E → Set E} (hS : IsMaximalMonotone S) : ∃ a b, b ∈ S a := by
  by_cases h : (0:E) ∈ S 0
  · exact ⟨0, 0, h⟩
  · obtain ⟨x, v, hv, -⟩ := hS.2 0 0 h
    exact ⟨x, v, hv⟩


lemma aux_finite_DF {ι : Type*} [Fintype ι] (a b : ι → E)
    (hmono : ∀ i j, 0 ≤ inner ℝ (b i - b j) (a i - a j)) (y : E) :
    ∃ x : E, ∀ i, 0 ≤ inner ℝ (y - x - b i) (x - a i) := by
  classical
  by_cases hι : IsEmpty ι
  · exact ⟨0, fun i => (hι.false i).elim⟩
  rw [not_isEmpty_iff] at hι
  obtain ⟨i₀⟩ := hι
  set A : (ι → ℝ) → E := fun μ => ∑ i, μ i • a i with hAdef
  set B : (ι → ℝ) → E := fun μ => ∑ i, μ i • b i with hBdef
  set c : (ι → ℝ) → ℝ := fun μ => ∑ i, μ i * inner ℝ (b i) (a i) with hcdef
  set Φ : E → (ι → ℝ) → ℝ := fun x μ => inner ℝ (y - x) (x - A μ) - inner ℝ (B μ) x + c μ
    with hPhidef
  set X : (ι → ℝ) → E := fun μ => (1/2 : ℝ) • (y - B μ + A μ) with hXdef
  set h : (ι → ℝ) → ℝ := fun μ => Φ (X μ) μ with hhdef
  have hXm : ∀ μ, y - X μ - B μ = X μ - A μ := by
    intro μ; simp only [hXdef]; module
  -- Φ is maximized at X μ
  have hPhiX : ∀ x μ, Φ x μ ≤ h μ := by
    intro x μ
    simp only [hhdef, hPhidef]
    set m := X μ
    have e1 : y - x = (y - m) - (x - m) := by abel
    have e2 : x - A μ = (m - A μ) + (x - m) := by abel
    have e3 : inner ℝ (B μ) x = inner ℝ (B μ) m + inner ℝ (B μ) (x - m) := by
      rw [← inner_add_right]; congr 1; abel
    rw [e1, e2, e3, inner_sub_left, inner_add_right, inner_add_right]
    have h0 : inner ℝ (y - m) (x - m) - inner ℝ (x - m) (m - A μ) - inner ℝ (B μ) (x - m) = 0 := by
      rw [real_inner_comm (m - A μ) (x - m), ← hXm μ, ← inner_sub_left, ← inner_sub_left]
      have : y - m - (y - m - B μ) - B μ = 0 := by abel
      rw [this, inner_zero_left]
    have := real_inner_self_nonneg (x := x - m)
    linarith
  -- double sum identity
  have hBA : ∀ μ : ι → ℝ, inner ℝ (B μ) (A μ) = ∑ i, ∑ j, μ i * μ j * inner ℝ (b i) (a j) := by
    intro μ
    simp only [hBdef, hAdef]
    rw [sum_inner]
    apply Finset.sum_congr rfl; intro i _
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [real_inner_smul_right]; ring
  have hcBA : ∀ μ ∈ stdSimplex ℝ ι, inner ℝ (B μ) (A μ) ≤ c μ := by
    intro μ hμ
    have hnn : 0 ≤ ∑ i, ∑ j, μ i * μ j * inner ℝ (b i - b j) (a i - a j) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (mul_nonneg (hμ.1 i) (hμ.1 j)) (hmono i j)))
    have S1 : ∑ i, ∑ j, μ i * μ j * inner ℝ (b i) (a i) = c μ := by
      simp only [hcdef]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (∑ j, μ i * μ j * inner ℝ (b i) (a i)) = (∑ j, μ j) * (μ i * inner ℝ (b i) (a i)) by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring]
      rw [hμ.2, one_mul]
    have S4 : ∑ i, ∑ j, μ i * μ j * inner ℝ (b j) (a j) = c μ := by
      simp only [hcdef]
      rw [show (∑ i, ∑ j, μ i * μ j * inner ℝ (b j) (a j))
          = (∑ i, μ i) * ∑ j, μ j * inner ℝ (b j) (a j) by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring]
      rw [hμ.2, one_mul]
    have S3 : ∑ i, ∑ j, μ i * μ j * inner ℝ (b j) (a i)
        = ∑ i, ∑ j, μ i * μ j * inner ℝ (b i) (a j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    have hexp : ∑ i, ∑ j, μ i * μ j * inner ℝ (b i - b j) (a i - a j)
        = ∑ i, ∑ j, μ i * μ j * inner ℝ (b i) (a i) - ∑ i, ∑ j, μ i * μ j * inner ℝ (b i) (a j)
          - (∑ i, ∑ j, μ i * μ j * inner ℝ (b j) (a i)
            - ∑ i, ∑ j, μ i * μ j * inner ℝ (b j) (a j)) := by
      simp only [inner_sub_left, inner_sub_right, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [hexp, S1, S3, S4, ← hBA] at hnn
    linarith
  have hpos : ∀ μ ∈ stdSimplex ℝ ι, 0 ≤ h μ := by
    intro μ hμ
    have hc := hcBA μ hμ
    simp only [hhdef, hPhidef]
    have : inner ℝ (y - X μ) (X μ - A μ) - inner ℝ (B μ) (X μ) + inner ℝ (B μ) (A μ)
        = inner ℝ (X μ - A μ) (X μ - A μ) := by
      calc inner ℝ (y - X μ) (X μ - A μ) - inner ℝ (B μ) (X μ) + inner ℝ (B μ) (A μ)
          = inner ℝ (y - X μ) (X μ - A μ) - inner ℝ (B μ) (X μ - A μ) := by
            rw [inner_sub_right (B μ) (X μ) (A μ)]; ring
        _ = inner ℝ (y - X μ - B μ) (X μ - A μ) := by rw [inner_sub_left (y - X μ) (B μ) (X μ - A μ)]
        _ = inner ℝ (X μ - A μ) (X μ - A μ) := by rw [hXm]
    have := real_inner_self_nonneg (x := X μ - A μ)
    linarith
  -- linearity in μ
  have hA : ∀ μ ν (t : ℝ), A ((1 - t) • μ + t • ν) = (1 - t) • A μ + t • A ν := by
    intro μ ν t
    simp only [hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
  have hB : ∀ μ ν (t : ℝ), B ((1 - t) • μ + t • ν) = (1 - t) • B μ + t • B ν := by
    intro μ ν t
    simp only [hBdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
  have hc : ∀ μ ν (t : ℝ), c ((1 - t) • μ + t • ν) = (1 - t) * c μ + t * c ν := by
    intro μ ν t
    simp only [hcdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
      Finset.sum_add_distrib, Finset.mul_sum]
  have hlin : ∀ x μ ν (t : ℝ), Φ x ((1 - t) • μ + t • ν) = (1 - t) * Φ x μ + t * Φ x ν := by
    intro x μ ν t
    simp only [hPhidef, hA, hB, hc]
    rw [show x - ((1 - t) • A μ + t • A ν) = (1 - t) • (x - A μ) + t • (x - A ν) by module]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_add_left,
      real_inner_smul_left, real_inner_smul_left]
    ring
  -- continuity
  have hAc : Continuous A := by
    simp only [hAdef]; fun_prop
  have hBc : Continuous B := by
    simp only [hBdef]; fun_prop
  have hcc : Continuous c := by
    simp only [hcdef]; fun_prop
  have hXc : Continuous X := by
    simp only [hXdef]; fun_prop
  have hPhic : ∀ ν, Continuous (fun x => Φ x ν) := by
    intro ν; simp only [hPhidef]; fun_prop
  have hcont : Continuous h := by
    simp only [hhdef, hPhidef]; fun_prop
  obtain ⟨μs, hμs, hmin⟩ := (isCompact_stdSimplex ι).exists_isMinOn
    ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩ hcont.continuousOn
  refine ⟨X μs, fun i => ?_⟩
  set ν : ι → ℝ := Pi.single i 1 with hνdef
  have hν : ν ∈ stdSimplex ℝ ι := single_mem_stdSimplex ℝ i
  have hAν : A ν = a i := by simp [hAdef, hνdef]
  have hBν : B ν = b i := by simp [hBdef, hνdef]
  have hcν : c ν = inner ℝ (b i) (a i) := by simp [hcdef, hνdef, Pi.single_apply]
  have hPhinu : Φ (X μs) ν = inner ℝ (y - X μs - b i) (X μs - a i) := by
    simp only [hPhidef, hAν, hBν, hcν]
    rw [inner_sub_left (y - X μs) (b i), inner_sub_right (b i)]
    ring
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → h μs ≤ Φ (X ((1 - t) • μs + t • ν)) ν := by
    intro t ht0 ht1
    have hmem : (1 - t) • μs + t • ν ∈ stdSimplex ℝ ι :=
      convex_stdSimplex ℝ ι hμs hν (by linarith) ht0.le (by ring)
    have h1 : h μs ≤ h ((1 - t) • μs + t • ν) := hmin hmem
    have h2 : h ((1 - t) • μs + t • ν) = (1 - t) * Φ (X ((1 - t) • μs + t • ν)) μs
        + t * Φ (X ((1 - t) • μs + t • ν)) ν := hlin _ _ _ _
    have h3 : Φ (X ((1 - t) • μs + t • ν)) μs ≤ h μs := hPhiX _ _
    have h4 : t * h μs ≤ t * Φ (X ((1 - t) • μs + t • ν)) ν := by nlinarith
    exact le_of_mul_le_mul_left h4 ht0
  have hgc : Continuous (fun t : ℝ => Φ (X ((1 - t) • μs + t • ν)) ν) := by
    apply (hPhic ν).comp
    apply hXc.comp
    fun_prop
  have hlimit : Filter.Tendsto (fun t : ℝ => Φ (X ((1 - t) • μs + t • ν)) ν) (𝓝[>] 0)
      (𝓝 (Φ (X μs) ν)) := by
    have h0 := hgc.tendsto 0
    simp only [sub_zero, one_smul, zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hfin : h μs ≤ Φ (X μs) ν := by
    apply ge_of_tendsto hlimit
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    exact key t ht.1 ht.2.le
  rw [hPhinu] at hfin
  linarith [hpos μs hμs]


lemma aux_minty {S : E → Set E} (hS : IsMaximalMonotone S) {l : ℝ} (hl : 0 < l) (y : E) :
    ∃ x, ∃ w ∈ S x, y = x + l • w := by
  classical
  obtain ⟨a₀, b₀, h₀⟩ := aux_graph_nonempty hS
  let ι := {p : E × E // p.2 ∈ S p.1}
  let C : ι → Set E := fun p => {x | 0 ≤ inner ℝ (y - x - l • p.1.2) (x - p.1.1)}
  let p₀ : ι := ⟨(a₀, b₀), h₀⟩
  have hclosed : ∀ p, IsClosed (C p) := by
    intro p
    exact isClosed_le continuous_const (by fun_prop)
  have hcpt : IsCompact (C p₀) := by
    set m : E := (1/2 : ℝ) • (y - l • b₀ + a₀) with hm
    set d : E := (1/2 : ℝ) • (y - l • b₀ - a₀) with hd
    apply (isCompact_closedBall m ‖d‖).of_isClosed_subset (hclosed p₀)
    intro x hx
    simp only [C, p₀, Set.mem_setOf_eq] at hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e1 : y - x - l • b₀ = d - (x - m) := by rw [hm, hd]; module
    have e2 : x - a₀ = d + (x - m) := by rw [hm, hd]; module
    have key : inner ℝ (y - x - l • b₀) (x - a₀) = ‖d‖ ^ 2 - ‖x - m‖ ^ 2 := by
      rw [e1, e2, inner_sub_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq, real_inner_comm d (x - m)]
      ring
    have h2 : ‖x - m‖ ^ 2 ≤ ‖d‖ ^ 2 := by linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h2
  have hfin : ∀ u : Finset ι, (C p₀ ∩ ⋂ i ∈ u, C i).Nonempty := by
    intro u
    obtain ⟨x, hx⟩ := aux_finite_DF (ι := ↥(insert p₀ u)) (fun p => p.1.1.1) (fun p => l • p.1.1.2)
      (by
        intro i j
        rw [← smul_sub, real_inner_smul_left]
        exact mul_nonneg hl.le (hS.1 j.1.1.1 i.1.1.1 j.1.1.2 i.1.1.2 j.1.2 i.1.2)) y
    refine ⟨x, ?_, ?_⟩
    · exact hx ⟨p₀, Finset.mem_insert_self _ _⟩
    · simp only [Set.mem_iInter]
      intro i hi
      exact hx ⟨i, Finset.mem_insert_of_mem hi⟩
  obtain ⟨x, -, hx⟩ := hcpt.inter_iInter_nonempty C hclosed hfin
  simp only [Set.mem_iInter] at hx
  refine ⟨x, l⁻¹ • (y - x), ?_, ?_⟩
  · by_contra hnot
    obtain ⟨x', v', hv', hlt⟩ := hS.2 x (l⁻¹ • (y - x)) hnot
    have h1 := hx ⟨(x', v'), hv'⟩
    simp only [C, Set.mem_setOf_eq] at h1
    have e : y - x - l • v' = l • (l⁻¹ • (y - x) - v') := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    rw [e, real_inner_smul_left] at h1
    have := (mul_nonneg_iff_of_pos_left hl).mp h1
    linarith
  · rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]; abel


lemma aux_resolvent_tendsto {Tseq : ℕ → E → Set E} {T : E → Set E}
    (hmono : ∀ n, IsMonotone (Tseq n)) (hsub : graph T ⊆ graphSetLiminf Tseq)
    {lamseq : ℕ → ℝ} {lam : ℝ} (hlim : Filter.Tendsto lamseq Filter.atTop (𝓝 lam))
    (hpos : ∀ n, 0 ≤ lamseq n)
    {y j w : E} (hw : w ∈ T j) (hy : y = j + lam • w)
    {jn wn : ℕ → E} (hwn : ∀ n, wn n ∈ Tseq n (jn n)) (hyn : ∀ n, y = jn n + lamseq n • wn n) :
    Filter.Tendsto jn Filter.atTop (𝓝 j) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K := 4 + |lam| + ‖w‖ with hK
  have hKpos : 0 < K := by positivity
  set δ := min 1 (ε / K) with hδ
  have hδpos : 0 < δ := lt_min one_pos (div_pos hε hKpos)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδK : δ * K ≤ ε := by
    calc δ * K ≤ (ε / K) * K := mul_le_mul_of_nonneg_right (min_le_right _ _) hKpos.le
    _ = ε := div_mul_cancel₀ ε hKpos.ne'
  have h1 : ∀ᶠ n in Filter.atTop, dist (lamseq n) lam < δ := Metric.tendsto_nhds.mp hlim δ hδpos
  have h2 : ∀ᶠ n in Filter.atTop, ∃ p ∈ graph (Tseq n), p ∈ Metric.ball (j, w) δ :=
    hsub (show (j, w) ∈ graph T from hw) _ (Metric.ball_mem_nhds _ hδpos)
  filter_upwards [h1, h2] with n hn1 hn2
  obtain ⟨⟨x', w'⟩, hp, hpball⟩ := hn2
  rw [Metric.mem_ball, Prod.dist_eq] at hpball
  have hx' : ‖x' - j‖ < δ := by
    rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_left _ _) hpball
  have hw' : ‖w' - w‖ < δ := by
    rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_right _ _) hpball
  have hlamn : |lamseq n - lam| < δ := by rw [← Real.dist_eq]; exact hn1
  have hne := aux_nonexp (hmono n) (hpos n) (hwn n) hp
  rw [← hyn n] at hne
  have e : y - (x' + lamseq n • w') = (j - x') + lam • (w - w') + (lam - lamseq n) • w' := by
    rw [hy]; module
  have hw'b : ‖w'‖ ≤ ‖w‖ + δ := by
    have := norm_le_insert' w' w
    linarith
  have hb : ‖y - (x' + lamseq n • w')‖ ≤ δ + |lam| * δ + δ * (‖w‖ + δ) := by
    rw [e]
    calc ‖(j - x') + lam • (w - w') + (lam - lamseq n) • w'‖
        ≤ ‖j - x'‖ + ‖lam • (w - w')‖ + ‖(lam - lamseq n) • w'‖ := norm_add₃_le
      _ = ‖j - x'‖ + |lam| * ‖w - w'‖ + |lam - lamseq n| * ‖w'‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ δ + |lam| * δ + δ * (‖w‖ + δ) := by
          gcongr
          · rw [norm_sub_rev]; exact hx'.le
          · rw [norm_sub_rev]; exact hw'.le
          · rw [abs_sub_comm]; exact hlamn.le
  have htri := norm_sub_le_norm_sub_add_norm_sub (jn n) x' j
  rw [dist_eq_norm]
  have habs : 0 ≤ |lam| := abs_nonneg _
  have hnw : 0 ≤ ‖w‖ := norm_nonneg _
  have : δ * (‖w‖ + δ) ≤ δ * (‖w‖ + 1) := by
    apply mul_le_mul_of_nonneg_left _ hδpos.le; linarith
  nlinarith

lemma aux_setLim_of_tendsto {A : ℕ → Set E} {B : Set E} {u : ℕ → E} {j : E}
    (hA : ∀ n, ∀ z ∈ A n, z = u n) (huA : ∀ n, u n ∈ A n) (hB : ∀ z ∈ B, z = j) (hjB : j ∈ B)
    (hu : Filter.Tendsto u Filter.atTop (𝓝 j)) : setLimsup A = B ∧ setLiminf A = B := by
  have hjinf : j ∈ setLiminf A := by
    intro V hV
    filter_upwards [hu hV] with n hn
    exact ⟨u n, huA n, hn⟩
  have hsup : ∀ z ∈ setLimsup A, z = j := by
    intro z hz
    by_contra hne
    have hr : 0 < dist z j / 2 := by
      have := dist_pos.mpr hne
      linarith
    have h1 := hz _ (Metric.ball_mem_nhds z hr)
    have h2 := Metric.tendsto_nhds.mp hu _ hr
    obtain ⟨n, hn2, v, hv, hvz⟩ := (h2.and_frequently h1).exists
    rw [hA n v hv, Metric.mem_ball] at hvz
    have := dist_triangle z (u n) j
    rw [_root_.dist_comm] at hvz
    linarith
  constructor
  · ext z
    constructor
    · intro hz; rw [hsup z hz]; exact hjB
    · intro hz; rw [hB z hz]; exact aux_liminf_subset_limsup A hjinf
  · ext z
    constructor
    · intro hz; rw [hsup z (aux_liminf_subset_limsup A hz)]; exact hjB
    · intro hz; rw [hB z hz]; exact hjinf


lemma aux_part1 {Tseq : ℕ → E → Set E} {T : E → Set E}
    (hconv : GraphicallyConverges Tseq T) (hmono : ∀ i, IsMonotone (Tseq i)) : IsMonotone T := by
  intro x₀ x₁ v₀ v₁ h₀ h₁
  have hp : (x₀, v₀) ∈ graphSetLiminf Tseq := by rw [hconv.2]; exact h₀
  have hq : (x₁, v₁) ∈ graphSetLimsup Tseq := by rw [hconv.1]; exact h₁
  exact aux_mono_of_lim hmono hp hq

lemma aux_part2 {Tseq : ℕ → E → Set E} {T : E → Set E}
    (hconv : GraphicallyConverges Tseq T) (hmax : ∀ i, IsMaximalMonotone (Tseq i))
    (hne : (graph T).Nonempty) : IsMaximalMonotone T := by
  have hmonoT : IsMonotone T := aux_part1 hconv (fun i => (hmax i).1)
  have surj : ∀ y : E, ∃ x, y - x ∈ T x := by
    intro y
    obtain ⟨⟨x₀, v₀⟩, h₀⟩ := hne
    have h₀' : (x₀, v₀) ∈ graphSetLiminf Tseq := by rw [hconv.2]; exact h₀
    have hJ : ∀ n, ∃ x, ∃ w ∈ Tseq n x, y = x + (1:ℝ) • w := fun n => aux_minty (hmax n) one_pos y
    choose j w hw hy using hJ
    have hev := h₀' _ (Metric.ball_mem_nhds (x₀, v₀) one_pos)
    set R := ‖y - (x₀ + v₀)‖ + 3 with hR
    have hbd : ∀ᶠ n in Filter.atTop, j n ∈ Metric.closedBall x₀ R := by
      filter_upwards [hev] with n hn
      obtain ⟨⟨x', v'⟩, hv', hdist⟩ := hn
      rw [Metric.mem_ball, Prod.dist_eq] at hdist
      have hx' : ‖x' - x₀‖ < 1 := by
        rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_left _ _) hdist
      have hv'' : ‖v' - v₀‖ < 1 := by
        rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_right _ _) hdist
      have hne := aux_nonexp (hmax n).1 zero_le_one (hw n) hv'
      rw [← hy n] at hne
      rw [Metric.mem_closedBall, dist_eq_norm]
      have e : y - (x' + (1:ℝ) • v') = (y - (x₀ + v₀)) + (x₀ - x') + (v₀ - v') := by
        rw [one_smul]; abel
      have hb : ‖y - (x' + (1:ℝ) • v')‖ ≤ ‖y - (x₀ + v₀)‖ + ‖x₀ - x'‖ + ‖v₀ - v'‖ := by
        rw [e]; exact norm_add₃_le
      rw [norm_sub_rev x₀ x'] at hb
      rw [norm_sub_rev v₀ v'] at hb
      have htri := norm_sub_le_norm_sub_add_norm_sub (j n) x' x₀
      linarith
    have hle : Filter.map j Filter.atTop ≤ Filter.principal (Metric.closedBall x₀ R) := by
      rw [Filter.le_principal_iff]; exact hbd
    obtain ⟨x, -, hx⟩ := (isCompact_closedBall x₀ R).exists_clusterPt hle
    refine ⟨x, ?_⟩
    have hmem : (x, y - x) ∈ graphSetLimsup Tseq := by
      intro V hV
      have hc : Continuous (fun z : E => (z, y - z)) := by fun_prop
      have hV' : (fun z : E => (z, y - z)) ⁻¹' V ∈ 𝓝 x := hc.continuousAt.preimage_mem_nhds hV
      have hfr := (mapClusterPt_iff_frequently.mp hx) _ hV'
      apply hfr.mono
      intro n hn
      refine ⟨(j n, y - j n), ?_, hn⟩
      show y - j n ∈ Tseq n (j n)
      have : y - j n = w n := by rw [hy n, one_smul]; abel
      rw [this]; exact hw n
    rw [hconv.1] at hmem
    exact hmem
  refine ⟨hmonoT, ?_⟩
  intro xh vh hnot
  obtain ⟨x, hx⟩ := surj (xh + vh)
  refine ⟨x, xh + vh - x, hx, ?_⟩
  have hne : xh ≠ x := by
    rintro rfl
    apply hnot
    simpa using hx
  have e : inner ℝ (vh - (xh + vh - x)) (xh - x) = -‖xh - x‖ ^ 2 := by
    have : vh - (xh + vh - x) = -(xh - x) := by abel
    rw [this, inner_neg_left, real_inner_self_eq_norm_sq]
  rw [e]
  have : 0 < ‖xh - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith

lemma aux_part3 {Tseq : ℕ → E → Set E} {T : E → Set E} {lam : ℝ} (hlam : 0 < lam)
    (hT : IsMaximalMonotone T) (hTn : ∀ i, IsMaximalMonotone (Tseq i)) :
    GraphicallyConverges Tseq T ↔
      PointwiseMapConverges (fun i => invMap (addMap idMap (smulMap lam (Tseq i))))
        (invMap (addMap idMap (smulMap lam T))) := by
  constructor
  · intro hconv
    have hsub : graph T ⊆ graphSetLiminf Tseq := by rw [hconv.2]
    have key : ∀ y, setLimsup (fun n => invMap (addMap idMap (smulMap lam (Tseq n))) y)
          = invMap (addMap idMap (smulMap lam T)) y ∧
        setLiminf (fun n => invMap (addMap idMap (smulMap lam (Tseq n))) y)
          = invMap (addMap idMap (smulMap lam T)) y := by
      intro y
      obtain ⟨j, w, hw, hy⟩ := aux_minty hT hlam y
      have hJn : ∀ n, ∃ x, ∃ w ∈ Tseq n x, y = x + lam • w := fun n => aux_minty (hTn n) hlam y
      choose jn wn hwn hyn using hJn
      have ht := aux_resolvent_tendsto (fun n => (hTn n).1) hsub tendsto_const_nhds
        (fun _ => hlam.le) hw hy hwn hyn
      apply aux_setLim_of_tendsto (u := jn) (j := j)
      · intro n z hz
        obtain ⟨w', hw', hy'⟩ := aux_mem_resolvent_iff.mp hz
        exact aux_unique (hTn n).1 hlam.le hw' hy' (hwn n) (hyn n)
      · intro n
        exact aux_mem_resolvent_iff.mpr ⟨wn n, hwn n, hyn n⟩
      · intro z hz
        obtain ⟨w', hw', hy'⟩ := aux_mem_resolvent_iff.mp hz
        exact aux_unique hT.1 hlam.le hw' hy' hw hy
      · exact aux_mem_resolvent_iff.mpr ⟨w, hw, hy⟩
      · exact ht
    exact ⟨funext fun y => (key y).1, funext fun y => (key y).2⟩
  · intro hpw
    have hsub : graph T ⊆ graphSetLiminf Tseq := by
      rintro ⟨x, w⟩ hxw
      change w ∈ T x at hxw
      set y := x + lam • w with hydef
      have hx : x ∈ invMap (addMap idMap (smulMap lam T)) y :=
        aux_mem_resolvent_iff.mpr ⟨w, hxw, rfl⟩
      have hx' : x ∈ setLiminf (fun n => invMap (addMap idMap (smulMap lam (Tseq n))) y) := by
        have := congrFun hpw.2 y
        simp only [pLiminf] at this
        rw [this]; exact hx
      intro W hW
      have hc : Continuous (fun z : E => (z, lam⁻¹ • (y - z))) := by fun_prop
      have hfx : ((x, lam⁻¹ • (y - x)) : E × E) = (x, w) := by
        simp only [hydef, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      have hW' : (fun z : E => (z, lam⁻¹ • (y - z))) ⁻¹' W ∈ 𝓝 x := by
        apply hc.continuousAt.preimage_mem_nhds
        rw [hfx]; exact hW
      filter_upwards [hx' _ hW'] with n hn
      obtain ⟨z, hz, hzW⟩ := hn
      obtain ⟨w', hw', hy'⟩ := aux_mem_resolvent_iff.mp hz
      refine ⟨(z, lam⁻¹ • (y - z)), ?_, hzW⟩
      show lam⁻¹ • (y - z) ∈ Tseq n z
      have : lam⁻¹ • (y - z) = w' := by
        rw [hy', add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      rw [this]; exact hw'
    have hsup : graphSetLimsup Tseq ⊆ graph T := aux_limsup_subset hT (fun n => (hTn n).1) hsub
    have hinfsup : graphSetLiminf Tseq ⊆ graphSetLimsup Tseq := aux_liminf_subset_limsup _
    exact ⟨Set.Subset.antisymm hsup (hsub.trans hinfsup),
      Set.Subset.antisymm (hinfsup.trans hsup) hsub⟩

lemma aux_part4 {Tseq : ℕ → E → Set E} {T : E → Set E} (lamseq : ℕ → ℝ) (lam : ℝ)
    (hlim : Filter.Tendsto lamseq Filter.atTop (𝓝 lam)) (hlam : 0 < lam)
    (hconv : GraphicallyConverges Tseq T) (hT : IsMaximalMonotone T)
    (hTn : ∀ i, IsMaximalMonotone (Tseq i)) (hpos : ∀ i, 0 < lamseq i) :
    UniformlyConvergesOnBounded (fun i => invMap (addMap idMap (smulMap (lamseq i) (Tseq i))))
      (invMap (addMap idMap (smulMap lam T))) := by
  intro R hR ε hε ρ hρ
  have hsub : graph T ⊆ graphSetLiminf Tseq := by rw [hconv.2]
  have hJn : ∀ n y, ∃ x, ∃ w ∈ Tseq n x, y = x + lamseq n • w :=
    fun n y => aux_minty (hTn n) (hpos n) y
  have hJ : ∀ y, ∃ x, ∃ w ∈ T x, y = x + lam • w := fun y => aux_minty hT hlam y
  choose jn wn hwn hyn using hJn
  choose j w hw hy using hJ
  have hpt : ∀ y, Filter.Tendsto (fun n => jn n y) Filter.atTop (𝓝 (j y)) := fun y =>
    aux_resolvent_tendsto (fun n => (hTn n).1) hsub hlim (fun n => (hpos n).le) (hw y) (hy y)
      (fun n => hwn n y) (fun n => hyn n y)
  have hLn : ∀ n y y', ‖jn n y - jn n y'‖ ≤ ‖y - y'‖ := by
    intro n y y'
    have := aux_nonexp (hTn n).1 (hpos n).le (hwn n y) (hwn n y')
    rwa [← hyn n y, ← hyn n y'] at this
  have hL : ∀ y y', ‖j y - j y'‖ ≤ ‖y - y'‖ := by
    intro y y'
    have := aux_nonexp hT.1 hlam.le (hw y) (hw y')
    rwa [← hy y, ← hy y'] at this
  obtain ⟨t, -, htfin, hcover⟩ :=
    (isCompact_closedBall (0:E) R).finite_cover_balls (show 0 < ε / 3 by positivity)
  have hev : ∀ᶠ n in Filter.atTop, ∀ y' ∈ t, dist (jn n y') (j y') < ε / 3 := by
    rw [htfin.eventually_all]
    intro y' _
    exact (Metric.tendsto_nhds.mp (hpt y')) _ (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn y hy' => ?_⟩
  have hy'' : y ∈ Metric.closedBall (0:E) R := by
    rw [mem_closedBall_zero_iff]; exact hy'
  obtain ⟨y', hy't, hyy'⟩ := Set.mem_iUnion₂.mp (hcover hy'')
  have hclose : dist (jn n y) (j y) < ε := by
    have h1 := hLn n y y'
    have h2 := hL y' y
    have h3 := hN n hn y' hy't
    rw [Metric.mem_ball, dist_eq_norm] at hyy'
    rw [dist_eq_norm] at h3 ⊢
    rw [norm_sub_rev y' y] at h2
    have h4 : ‖jn n y - j y‖ ≤ ‖jn n y - jn n y'‖ + ‖jn n y' - j y'‖ + ‖j y' - j y‖ := by
      have e : jn n y - j y = (jn n y - jn n y') + (jn n y' - j y') + (j y' - j y) := by abel
      rw [e]; exact norm_add₃_le
    linarith
  constructor
  · rintro z ⟨hz, -⟩
    obtain ⟨w', hw', hy'''⟩ := aux_mem_resolvent_iff.mp hz
    have := aux_unique (hTn n).1 (hpos n).le hw' hy''' (hwn n y) (hyn n y)
    exact ⟨j y, aux_mem_resolvent_iff.mpr ⟨w y, hw y, hy y⟩, this ▸ hclose⟩
  · rintro z ⟨hz, -⟩
    obtain ⟨w', hw', hy'''⟩ := aux_mem_resolvent_iff.mp hz
    have := aux_unique hT.1 hlam.le hw' hy''' (hw y) (hy y)
    refine ⟨jn n y, aux_mem_resolvent_iff.mpr ⟨wn n y, hwn n y, hyn n y⟩, ?_⟩
    rw [this, _root_.dist_comm]; exact hclose

theorem RW_chap_12_32
  (Tseq : ℕ → (E → Set E))
  (T : E → Set E) :
  let resolvent : ℝ → (E → Set E) → (E → Set E) :=
    fun l S => invMap (addMap idMap (smulMap l S))
  ((GraphicallyConverges Tseq T ∧ ∀ i, IsMonotone (Tseq i)) →
    IsMonotone T) ∧
  ((GraphicallyConverges Tseq T ∧ (∀ i, IsMaximalMonotone (Tseq i)) ∧ (graph T).Nonempty) →
    IsMaximalMonotone T) ∧
  (∀ lam : ℝ, 0 < lam →
    (IsMaximalMonotone T ∧ ∀ i, IsMaximalMonotone (Tseq i)) →
      (GraphicallyConverges Tseq T ↔
        PointwiseMapConverges
          (fun i => resolvent lam (Tseq i))
          (resolvent lam T))) ∧
  (∀ (lamseq : ℕ → ℝ) (lam : ℝ),
    Filter.Tendsto lamseq Filter.atTop (𝓝 lam) →
    0 < lam →
    ((GraphicallyConverges Tseq T) ∧
      IsMaximalMonotone T ∧
      (∀ i, IsMaximalMonotone (Tseq i)) ∧
      (∀ i, 0 < lamseq i)) →
    UniformlyConvergesOnBounded
      (fun i => resolvent (lamseq i) (Tseq i))
      (resolvent lam T)) := by
  intro resolvent
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨hconv, hmono⟩
    exact aux_part1 hconv hmono
  · rintro ⟨hconv, hmax, hne⟩
    exact aux_part2 hconv hmax hne
  · rintro lam hlam ⟨hT, hTn⟩
    exact aux_part3 hlam hT hTn
  · rintro lamseq lam hlim hlam ⟨hconv, hT, hTn, hpos⟩
    exact aux_part4 lamseq lam hlim hlam hconv hT hTn hpos

end RW_chap_12_32
