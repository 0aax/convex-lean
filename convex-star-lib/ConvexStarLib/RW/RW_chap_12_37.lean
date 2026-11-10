import ConvexStarLib.Defs

/-!
# `RW_chap_12_37`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_37` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_37`, so the main result is `RW_chap_12_37.RW_chap_12_37`.
-/

namespace RW_chap_12_37

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace RWAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mm_mem_of_forall {T : E → Set E} (hT : IsMaximalMonotone T) {x w : E}
    (h : ∀ y w', w' ∈ T y → 0 ≤ inner ℝ (w - w') (x - y)) : w ∈ T x := by
  by_contra hw
  obtain ⟨y, w', hw', hlt⟩ := hT.2 x w hw
  exact absurd (h y w' hw') (not_le.mpr hlt)

lemma mm_graph_nonempty {T : E → Set E} (hT : IsMaximalMonotone T) : ∃ y w, w ∈ T y := by
  by_cases h : (0:E) ∈ T 0
  · exact ⟨0, 0, h⟩
  · obtain ⟨y, w, hw, -⟩ := hT.2 0 0 h
    exact ⟨y, w, hw⟩

lemma norm_le_of_inner_nonneg {a b : E} (h : 0 ≤ inner ℝ (b - a) a) : ‖a‖ ≤ ‖b‖ := by
  have h1 : ‖a‖ ^ 2 ≤ ‖b‖ * ‖a‖ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
    nlinarith [real_inner_le_norm b a]
  by_cases ha : ‖a‖ = 0
  · rw [ha]; exact norm_nonneg _
  · have : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
    nlinarith

lemma resolvent_bound {T : E → Set E} (hT : IsMaximalMonotone T) {lam : ℝ} (hlam : 0 ≤ lam)
    {z x w y w' : E} (hw : w ∈ T x) (hz : z = x + lam • w) (hw' : w' ∈ T y) :
    ‖x - y‖ ≤ ‖z - y - lam • w'‖ := by
  apply norm_le_of_inner_nonneg
  have h1 : z - y - lam • w' - (x - y) = lam • (w - w') := by
    rw [hz, smul_sub]; abel
  rw [h1, real_inner_smul_left]
  exact mul_nonneg hlam (hT.1 y x w' w hw' hw)

lemma le_zero_of_forall_le_mul {d K : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → d ≤ t * K) : d ≤ 0 := by
  by_contra hd
  push_neg at hd
  have h1 := h 1 one_pos le_rfl
  have hK : 0 < K := by linarith
  have h2 := h (d / (2 * K)) (by positivity) (by rw [div_le_one (by positivity)]; linarith)
  have : d / (2 * K) * K = d / 2 := by field_simp
  linarith

lemma aux_double_sum {ι : Type*} [Fintype ι] (μ : ι → ℝ) (hμ : ∑ i, μ i = 1) (y w : ι → E) :
    ∑ i, ∑ j, μ i * μ j * inner ℝ (w i - w j) (y i - y j) =
      2 * (∑ i, μ i * inner ℝ (w i) (y i)) - 2 * inner ℝ (∑ i, μ i • w i) (∑ j, μ j • y j) := by
  have hB' : inner ℝ (∑ i, μ i • w i) (∑ j, μ j • y j) =
      ∑ i, ∑ j, μ i * μ j * inner ℝ (w j) (y i) := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hB : inner ℝ (∑ i, μ i • w i) (∑ j, μ j • y j) =
      ∑ i, ∑ j, μ i * μ j * inner ℝ (w i) (y j) := by
    rw [hB']
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hA1 : ∑ i, ∑ j, μ i * μ j * inner ℝ (w i) (y i) = ∑ i, μ i * inner ℝ (w i) (y i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum, hμ, mul_one]
  have hA2 : ∑ i, ∑ j, μ i * μ j * inner ℝ (w j) (y j) = ∑ i, μ i * inner ℝ (w i) (y i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, hμ, one_mul]
  have hexp : ∀ i j, μ i * μ j * inner ℝ (w i - w j) (y i - y j) =
      μ i * μ j * inner ℝ (w i) (y i) + μ i * μ j * inner ℝ (w j) (y j)
        - μ i * μ j * inner ℝ (w i) (y j) - μ i * μ j * inner ℝ (w j) (y i) := by
    intro i j; simp only [inner_sub_left, inner_sub_right]; ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA1, hA2, ← hB, ← hB']; ring

end RWAux

namespace RWAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma finite_minty {ι : Type*} [Fintype ι] [Nonempty ι] (y w : ι → E) (z : E)
    (hmono : ∀ i j, 0 ≤ inner ℝ (w i - w j) (y i - y j)) :
    ∃ x : E, ∀ i, 0 ≤ inner ℝ (z - x - w i) (x - y i) := by
  classical
  let c : ι → E := fun i => (1/2 : ℝ) • (z - w i + y i)
  let ℓ : ι → ℝ := fun i => inner ℝ (z - w i) (y i)
  let Φ : (ι → ℝ) → ℝ := fun μ => ∑ i, μ i * ℓ i - ‖∑ i, μ i • c i‖ ^ 2
  have hΦdef : ∀ ν, Φ ν = ∑ i, ν i * ℓ i - ‖∑ i, ν i • c i‖ ^ 2 := fun ν => rfl
  have hcont : Continuous Φ := by fun_prop
  obtain ⟨μ, hμS, hmax⟩ := (isCompact_stdSimplex ι).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ι)⟩ hcont.continuousOn
  have hμsum : ∑ i, μ i = 1 := hμS.2
  have hμnn : ∀ i, 0 ≤ μ i := hμS.1
  set x := ∑ i, μ i • c i with hx
  -- Step 1: Φ μ ≤ 0
  have hΦ : Φ μ ≤ 0 := by
    set wb := ∑ i, μ i • w i with hwb
    set yb := ∑ i, μ i • y i with hyb
    have hds := aux_double_sum μ hμsum y w
    have hnn : 0 ≤ ∑ i, ∑ j, μ i * μ j * inner ℝ (w i - w j) (y i - y j) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (mul_nonneg (hμnn i) (hμnn j)) (hmono i j)))
    have hL : ∑ i, μ i * ℓ i = inner ℝ z yb - ∑ i, μ i * inner ℝ (w i) (y i) := by
      simp only [ℓ, yb, inner_sum, real_inner_smul_right, inner_sub_left, mul_sub,
        Finset.sum_sub_distrib]
    have hxeq : x = (1/2 : ℝ) • (z - wb + yb) := by
      rw [hx]
      have : ∀ i, μ i • c i = (1/2 : ℝ) • (μ i • z - μ i • w i + μ i • y i) := by
        intro i; simp only [c]; rw [smul_comm, smul_add, smul_sub]
      simp only [this, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hμsum, one_smul, hwb, hyb]
    have hn1 : ‖(1/2 : ℝ) • (z - wb + yb)‖ ^ 2 = (1/4) * ‖z - wb + yb‖ ^ 2 := by
      rw [norm_smul, mul_pow]; norm_num
    have hn2 : ‖z - wb + yb‖ ^ 2 = ‖z - wb‖ ^ 2 + 2 * inner ℝ (z - wb) yb + ‖yb‖ ^ 2 :=
      norm_add_sq_real _ _
    have hn3 : 0 ≤ ‖z - wb - yb‖ ^ 2 := sq_nonneg _
    have hn4 : ‖z - wb - yb‖ ^ 2 = ‖z - wb‖ ^ 2 - 2 * inner ℝ (z - wb) yb + ‖yb‖ ^ 2 :=
      norm_sub_sq_real _ _
    have hn5 : inner ℝ (z - wb) yb = inner ℝ z yb - inner ℝ wb yb := inner_sub_left _ _ _
    rw [hΦdef, hL, ← hx, hxeq, hn1]
    linarith
  -- Step 2: g_j(x) ≤ Φ μ
  have hstep : ∀ j, inner ℝ (x - (z - w j)) (x - y j) ≤ Φ μ := by
    intro j
    apply sub_nonpos.mp
    apply le_zero_of_forall_le_mul (K := ‖x - c j‖ ^ 2)
    intro t ht0 ht1
    have hmem : (1 - t) • μ + t • (Pi.single j 1 : ι → ℝ) ∈ stdSimplex ℝ ι :=
      convex_stdSimplex ℝ ι hμS (single_mem_stdSimplex ℝ j) (by linarith) ht0.le (by ring)
    have hle : Φ ((1 - t) • μ + t • (Pi.single j 1 : ι → ℝ)) ≤ Φ μ := isMaxOn_iff.mp hmax _ hmem
    have hS1 : ∑ i, ((1 - t) • μ + t • (Pi.single j 1 : ι → ℝ)) i * ℓ i =
        (1 - t) * ∑ i, μ i * ℓ i + t * ℓ j := by
      simp [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, Pi.single_apply]
    have hS2 : ∑ i, ((1 - t) • μ + t • (Pi.single j 1 : ι → ℝ)) i • c i = (1 - t) • x + t • c j := by
      simp [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, Pi.single_apply, ← hx]
    rw [hΦdef, hΦdef, hS1, hS2, ← hx] at hle
    have e1 : ‖(1 - t) • x + t • c j‖ ^ 2 = (1-t)^2 * ‖x‖^2 + 2 * ((1-t) * t) * inner ℝ x (c j)
        + t^2 * ‖c j‖^2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]; ring
    have e2 : ‖x - c j‖ ^ 2 = ‖x‖^2 - 2 * inner ℝ x (c j) + ‖c j‖^2 := norm_sub_sq_real _ _
    have e3 : inner ℝ (x - (z - w j)) (x - y j) = ‖x‖^2 - 2 * inner ℝ x (c j) + ℓ j := by
      simp only [c, ℓ, inner_sub_left, inner_sub_right, inner_add_right,
        real_inner_smul_right, real_inner_self_eq_norm_sq]
      rw [real_inner_comm (y j) x, real_inner_comm (z) x, real_inner_comm (w j) x]
      ring
    rw [hΦdef, ← hx, e3, e2]
    rw [e1] at hle
    nlinarith
  refine ⟨x, fun j => ?_⟩
  have h1 := hstep j
  have h2 : inner ℝ (z - x - w j) (x - y j) = - inner ℝ (x - (z - w j)) (x - y j) := by
    rw [← inner_neg_left]; congr 1; abel
  linarith

end RWAux

namespace RWAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma minty [ProperSpace E] {T : E → Set E} (hT : IsMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam)
    (z : E) : ∃ x w, w ∈ T x ∧ z = x + lam • w := by
  classical
  let G := {p : E × E // p.2 ∈ T p.1}
  let S : G → Set E := fun p => {x | 0 ≤ inner ℝ (z - x - lam • p.1.2) (x - p.1.1)}
  have hSclosed : ∀ p, IsClosed (S p) := fun p => isClosed_le continuous_const (by fun_prop)
  have hSbdd : ∀ p, S p ⊆ Metric.closedBall p.1.1 ‖z - p.1.1 - lam • p.1.2‖ := by
    intro p x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply norm_le_of_inner_nonneg
    have : z - p.1.1 - lam • p.1.2 - (x - p.1.1) = z - x - lam • p.1.2 := by abel
    rw [this]; exact hx
  obtain ⟨y₀, w₀, h₀⟩ := mm_graph_nonempty hT
  let p₀ : G := ⟨(y₀, w₀), h₀⟩
  have hcpt : IsCompact (S p₀) :=
    (isCompact_closedBall _ _).of_isClosed_subset (hSclosed p₀) (hSbdd p₀)
  have hfin : ∀ u : Finset G, (S p₀ ∩ ⋂ i ∈ u, S i).Nonempty := by
    intro u
    let s := insert p₀ u
    haveI : Nonempty s := ⟨⟨p₀, Finset.mem_insert_self _ _⟩⟩
    obtain ⟨x, hx⟩ := finite_minty (fun k : s => k.1.1.1) (fun k : s => lam • k.1.1.2) z
      (fun i j => by
        rw [← smul_sub, real_inner_smul_left]
        exact mul_nonneg hlam.le (hT.1 _ _ _ _ j.1.2 i.1.2))
    refine ⟨x, hx ⟨p₀, Finset.mem_insert_self _ _⟩, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    exact hx ⟨i, Finset.mem_insert_of_mem hi⟩
  obtain ⟨x, -, hx⟩ := hcpt.inter_iInter_nonempty S hSclosed hfin
  refine ⟨x, lam⁻¹ • (z - x), ?_, ?_⟩
  · apply mm_mem_of_forall hT
    intro y w' hw'
    have h1 := Set.mem_iInter.mp hx ⟨(y, w'), hw'⟩
    have h2 : lam⁻¹ • (z - x) - w' = lam⁻¹ • (z - x - lam • w') := by
      rw [smul_sub (lam⁻¹) (z - x) (lam • w'), smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    rw [h2, real_inner_smul_left]
    exact mul_nonneg (inv_nonneg.mpr hlam.le) h1
  · rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]

lemma convex_closure_dom [ProperSpace E] {T : E → Set E} (hT : IsMaximalMonotone T) :
    Convex ℝ (closure {x | (T x).Nonempty}) := by
  have key : ∀ a ∈ {x | (T x).Nonempty}, ∀ b ∈ {x | (T x).Nonempty}, ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      s + t = 1 → s • a + t • b ∈ closure {x | (T x).Nonempty} := by
    rintro a ⟨wa, hwa⟩ b ⟨wb, hwb⟩ s t hs ht hst
    rw [Metric.mem_closure_iff]
    intro ε hε
    set z := s • a + t • b with hz
    set C := ‖wa‖ * (‖z - a‖ + ‖wa‖) + ‖wb‖ * (‖z - b‖ + ‖wb‖) with hC
    have hCnn : 0 ≤ C := by positivity
    set lam := min 1 (ε ^ 2 / (2 * (C + 1))) with hlam
    have hlam0 : 0 < lam := by positivity
    have hlam1 : lam ≤ 1 := min_le_left _ _
    have hlam2 : lam ≤ ε ^ 2 / (2 * (C + 1)) := min_le_right _ _
    obtain ⟨x, w, hw, hzx⟩ := minty hT hlam0 z
    refine ⟨x, ⟨w, hw⟩, ?_⟩
    -- inequalities from monotonicity
    have hma : 0 ≤ inner ℝ (w - wa) (x - a) := hT.1 a x wa w hwa hw
    have hmb : 0 ≤ inner ℝ (w - wb) (x - b) := hT.1 b x wb w hwb hw
    have hzx' : z - x = lam • w := by rw [hzx]; abel
    have hia : inner ℝ (z - x) (a - x) ≤ lam * inner ℝ wa (a - x) := by
      rw [hzx', real_inner_smul_left]
      have : inner ℝ (w - wa) (x - a) = inner ℝ wa (a - x) - inner ℝ w (a - x) := by
        rw [← neg_sub a x, inner_neg_right, inner_sub_left]; ring
      rw [this] at hma
      nlinarith
    have hib : inner ℝ (z - x) (b - x) ≤ lam * inner ℝ wb (b - x) := by
      rw [hzx', real_inner_smul_left]
      have : inner ℝ (w - wb) (x - b) = inner ℝ wb (b - x) - inner ℝ w (b - x) := by
        rw [← neg_sub b x, inner_neg_right, inner_sub_left]; ring
      rw [this] at hmb
      nlinarith
    have hsum : s * inner ℝ (z - x) (a - x) + t * inner ℝ (z - x) (b - x) = ‖z - x‖ ^ 2 := by
      rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right,
        ← real_inner_self_eq_norm_sq]
      congr 1
      have : s • (a - x) + t • (b - x) = (s • a + t • b) - (s + t) • x := by
        rw [smul_sub, smul_sub, add_smul]; abel
      rw [this, hst, one_smul]
    -- bounds on ‖a - x‖, ‖b - x‖
    have hax : ‖a - x‖ ≤ ‖z - a‖ + ‖wa‖ := by
      rw [norm_sub_rev]
      calc ‖x - a‖ ≤ ‖z - a - lam • wa‖ := resolvent_bound hT hlam0.le hw hzx hwa
        _ ≤ ‖z - a‖ + ‖lam • wa‖ := norm_sub_le _ _
        _ ≤ ‖z - a‖ + ‖wa‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
          nlinarith [norm_nonneg wa]
    have hbx : ‖b - x‖ ≤ ‖z - b‖ + ‖wb‖ := by
      rw [norm_sub_rev]
      calc ‖x - b‖ ≤ ‖z - b - lam • wb‖ := resolvent_bound hT hlam0.le hw hzx hwb
        _ ≤ ‖z - b‖ + ‖lam • wb‖ := norm_sub_le _ _
        _ ≤ ‖z - b‖ + ‖wb‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
          nlinarith [norm_nonneg wb]
    have hia' : inner ℝ wa (a - x) ≤ ‖wa‖ * (‖z - a‖ + ‖wa‖) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hax (norm_nonneg _))
    have hib' : inner ℝ wb (b - x) ≤ ‖wb‖ * (‖z - b‖ + ‖wb‖) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hbx (norm_nonneg _))
    have hs1 : s ≤ 1 := by linarith
    have ht1 : t ≤ 1 := by linarith
    -- ‖z - x‖^2 ≤ lam * C
    have hA : 0 ≤ ‖wa‖ * (‖z - a‖ + ‖wa‖) := by positivity
    have hB : 0 ≤ ‖wb‖ * (‖z - b‖ + ‖wb‖) := by positivity
    have h1 : s * inner ℝ (z - x) (a - x) ≤ lam * (‖wa‖ * (‖z - a‖ + ‖wa‖)) :=
      calc s * inner ℝ (z - x) (a - x) ≤ s * (lam * inner ℝ wa (a - x)) :=
            mul_le_mul_of_nonneg_left hia hs
        _ ≤ s * (lam * (‖wa‖ * (‖z - a‖ + ‖wa‖))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hia' hlam0.le) hs
        _ ≤ lam * (‖wa‖ * (‖z - a‖ + ‖wa‖)) :=
            mul_le_of_le_one_left (mul_nonneg hlam0.le hA) hs1
    have h2 : t * inner ℝ (z - x) (b - x) ≤ lam * (‖wb‖ * (‖z - b‖ + ‖wb‖)) :=
      calc t * inner ℝ (z - x) (b - x) ≤ t * (lam * inner ℝ wb (b - x)) :=
            mul_le_mul_of_nonneg_left hib ht
        _ ≤ t * (lam * (‖wb‖ * (‖z - b‖ + ‖wb‖))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hib' hlam0.le) ht
        _ ≤ lam * (‖wb‖ * (‖z - b‖ + ‖wb‖)) :=
            mul_le_of_le_one_left (mul_nonneg hlam0.le hB) ht1
    have hCeq : lam * C = lam * (‖wa‖ * (‖z - a‖ + ‖wa‖)) + lam * (‖wb‖ * (‖z - b‖ + ‖wb‖)) := by
      rw [hC]; ring
    have hzx2 : ‖z - x‖ ^ 2 ≤ lam * C := by rw [← hsum, hCeq]; linarith
    have hlC : lam * C < ε ^ 2 := by
      calc lam * C ≤ ε ^ 2 / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right hlam2 hCnn
        _ < ε ^ 2 := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [sq_nonneg ε, mul_pos hε hε]
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le (by linarith)
  intro p hp q hq s t hs ht hst
  have := map_mem_closure₂ (f := fun p q : E => s • p + t • q)
    (by exact (by fun_prop : Continuous (fun pq : E × E => s • pq.1 + t • pq.2))) hp hq
    (fun a ha b hb => key a ha b hb s t hs ht hst)
  rwa [closure_closure] at this

end RWAux

namespace RWAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mem_normalCone_of {C : Set E} {x v : E} (hx : x ∈ C)
    (h : ∀ y ∈ C, inner ℝ v (y - x) ≤ 0) : v ∈ normalCone C x := by
  refine ⟨fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds, fun _ => ?_⟩
  exact ⟨hx, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ, Filter.univ_mem,
    fun y _ hy => h y hy⟩

lemma regular_normal_convex {C : Set E} (hC : Convex ℝ C) {x v : E}
    (hv : IsRegularNormalAt C x v) : x ∈ C ∧ ∀ y ∈ C, inner ℝ v (y - x) ≤ 0 := by
  obtain ⟨hx, r, hr, V, hV, hVr⟩ := hv
  refine ⟨hx, fun y hy => ?_⟩
  by_contra hpos
  push_neg at hpos
  set c := inner ℝ v (y - x) with hc
  have hyx : y - x ≠ 0 := by
    intro h; rw [h, inner_zero_right] at hc; linarith
  have hd0 : 0 < ‖y - x‖ := norm_pos_iff.mpr hyx
  have hev := hr.def (show 0 < c / (2 * ‖y - x‖) by positivity)
  have hpath : Filter.Tendsto (fun t : ℝ => x + t • (y - x)) (𝓝[>] 0) (𝓝 x) := by
    have : Filter.Tendsto (fun t : ℝ => x + t • (y - x)) (𝓝 0) (𝓝 (x + (0:ℝ) • (y - x))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev2 := hpath.eventually (hev.and hV)
  have hev3 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨t, ⟨hr1, hV1⟩, ht0, ht1⟩ := (hev2.and hev3).exists
  have hmem : x + t • (y - x) ∈ C := hC.add_smul_sub_mem hx hy ⟨ht0.le, ht1.le⟩
  have h1 := hVr _ hV1 hmem
  rw [add_sub_cancel_left, real_inner_smul_right] at h1
  rw [add_sub_cancel_left, norm_norm, norm_smul, Real.norm_of_nonneg ht0.le] at hr1
  have h2 : r (x + t • (y - x)) ≤ c / (2 * ‖y - x‖) * (t * ‖y - x‖) :=
    (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hr1)
  have h3 : c / (2 * ‖y - x‖) * (t * ‖y - x‖) = t * c / 2 := by field_simp
  rw [h3] at h2
  nlinarith [mul_pos ht0 hpos]

lemma normalCone_sub {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) {x v : E}
    (hv : v ∈ normalCone C x) : x ∈ C ∧ ∀ y ∈ C, inner ℝ v (y - x) ≤ 0 := by
  obtain ⟨xs, vs, hxs, hvs, hreg⟩ := hv
  have hreg' := fun n => regular_normal_convex hC (hreg n)
  refine ⟨hCc.mem_of_tendsto hxs (Filter.Eventually.of_forall fun n => (hreg' n).1),
    fun y hy => ?_⟩
  have : Filter.Tendsto (fun n => inner ℝ (vs n) (y - xs n)) Filter.atTop
      (𝓝 (inner ℝ v (y - x))) :=
    hvs.inner (tendsto_const_nhds.sub hxs)
  exact le_of_tendsto' this (fun n => (hreg' n).2 y hy)

lemma proj_char {C : Set E} (hC : Convex ℝ C) {z p : E} (hp : p ∈ C) :
    (∀ y ∈ C, ‖p - z‖ ≤ ‖y - z‖) ↔ (∀ y ∈ C, inner ℝ (z - p) (y - p) ≤ 0) := by
  constructor
  · intro h y hy
    apply le_zero_of_forall_le_mul (K := ‖y - p‖ ^ 2 / 2)
    intro t ht0 ht1
    have hmem : p + t • (y - p) ∈ C := hC.add_smul_sub_mem hp hy ⟨ht0.le, ht1⟩
    have h1 := h _ hmem
    have h2 : ‖p - z‖ ^ 2 ≤ ‖p + t • (y - p) - z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : p + t • (y - p) - z = (p - z) + t • (y - p) := by abel
    rw [h3, norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
      sq_abs] at h2
    have h4 : inner ℝ (p - z) (y - p) = - inner ℝ (z - p) (y - p) := by
      rw [← inner_neg_left, neg_sub]
    rw [h4] at h2
    nlinarith
  · intro h y hy
    have h1 := h y hy
    have h2 : y - z = (y - p) + (p - z) := by abel
    have h3 : ‖y - z‖ ^ 2 = ‖y - p‖ ^ 2 + 2 * inner ℝ (y - p) (p - z) + ‖p - z‖ ^ 2 := by
      rw [h2, norm_add_sq_real]
    have h4 : inner ℝ (y - p) (p - z) = - inner ℝ (z - p) (y - p) := by
      rw [real_inner_comm, ← inner_neg_left, neg_sub]
    have h5 : ‖p - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by rw [h3, h4]; nlinarith [sq_nonneg ‖y - p‖]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h5

lemma key_ineq {z x p y w w' : E} {lam : ℝ} (hzx : z - x = lam • w)
    (h1 : inner ℝ (z - p) (x - p) ≤ 0) (h2 : 0 ≤ inner ℝ (w - w') (x - y)) (hlam : 0 ≤ lam) :
    ‖x - p‖ ^ 2 ≤ ‖z - x‖ * ‖y - p‖ + lam * (‖w'‖ * ‖x - y‖) := by
  have e1 : inner ℝ (z - x) (x - y) + inner ℝ (z - x) (y - p) = inner ℝ (z - x) (x - p) := by
    rw [← inner_add_right]; congr 1; abel
  have e2 : inner ℝ (z - p) (x - p) - inner ℝ (z - x) (x - p) = ‖x - p‖ ^ 2 := by
    rw [← inner_sub_left, ← real_inner_self_eq_norm_sq]; congr 1; abel
  have e3 : lam * inner ℝ w' (x - y) ≤ inner ℝ (z - x) (x - y) := by
    rw [hzx, real_inner_smul_left]
    have : inner ℝ (w - w') (x - y) = inner ℝ w (x - y) - inner ℝ w' (x - y) :=
      inner_sub_left _ _ _
    nlinarith [mul_nonneg hlam h2]
  have e4 : - inner ℝ (z - x) (y - p) ≤ ‖z - x‖ * ‖y - p‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have e5 : - (lam * inner ℝ w' (x - y)) ≤ lam * (‖w'‖ * ‖x - y‖) := by
    have h6 := (neg_le_abs (inner ℝ w' (x - y))).trans (abs_real_inner_le_norm w' (x - y))
    nlinarith
  linarith

lemma resolvent_uniform [ProperSpace E] {T : E → Set E} (hT : IsMaximalMonotone T)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ δ > 0, ∀ lam : ℝ, 0 < lam → lam < δ → ∀ z x w p : E, ‖z‖ ≤ R → w ∈ T x →
      z = x + lam • w → p ∈ closure {x | (T x).Nonempty} →
      (∀ y ∈ closure {x | (T x).Nonempty}, inner ℝ (z - p) (y - p) ≤ 0) →
      ‖x - p‖ < ε := by
  classical
  obtain ⟨y₀, w₀, h₀⟩ := mm_graph_nonempty hT
  set A := R + ‖y₀‖ + ‖w₀‖ with hA
  set M := R + A + ‖y₀‖ with hM
  set B := 2 * R + ‖y₀‖ with hB
  have hMnn : 0 ≤ M := by positivity
  set η := ε ^ 2 / (2 * (M + 1)) with hη
  have hη0 : 0 < η := by positivity
  set K := closure {x | (T x).Nonempty} ∩ Metric.closedBall 0 B with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 B).inter_left isClosed_closure
  let G := {q : E × E // q.2 ∈ T q.1}
  have hcover : K ⊆ ⋃ i : G, Metric.ball i.1.1 η := by
    intro p hp
    obtain ⟨b, ⟨wb, hwb⟩, hdist⟩ := Metric.mem_closure_iff.mp hp.1 η hη0
    exact Set.mem_iUnion.mpr ⟨⟨(b, wb), hwb⟩, by rw [Metric.mem_ball]; exact hdist⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun i : G => Metric.ball i.1.1 η)
    (fun _ => Metric.isOpen_ball) hcover
  set C := ∑ i ∈ t, ‖i.1.2‖ * (A + ‖y₀‖ + ‖i.1.1‖) with hC
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨min 1 (ε ^ 2 / (2 * (C + 1))), by positivity, ?_⟩
  intro lam hlam hlamδ z x w p hz hw hzx hp hpvar
  have hlam1 : lam ≤ 1 := le_trans hlamδ.le (min_le_left _ _)
  have hlamC : lam ≤ ε ^ 2 / (2 * (C + 1)) := le_trans hlamδ.le (min_le_right _ _)
  have hxy₀ : ‖x - y₀‖ ≤ A := by
    calc ‖x - y₀‖ ≤ ‖z - y₀ - lam • w₀‖ := resolvent_bound hT hlam.le hw hzx h₀
      _ ≤ ‖z - y₀‖ + ‖lam • w₀‖ := norm_sub_le _ _
      _ ≤ ‖z‖ + ‖y₀‖ + ‖w₀‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
          have := norm_sub_le z y₀
          nlinarith [norm_nonneg w₀]
      _ ≤ A := by rw [hA]; linarith
  have hxnorm : ‖x‖ ≤ A + ‖y₀‖ := by
    have := norm_sub_norm_le x y₀
    linarith
  have hzx_norm : ‖z - x‖ ≤ M := by
    have := norm_sub_le z x
    rw [hM]; linarith
  have hy₀D : y₀ ∈ closure {x | (T x).Nonempty} := subset_closure ⟨w₀, h₀⟩
  have hpz : ‖p - z‖ ≤ ‖y₀ - z‖ := ((proj_char (convex_closure_dom hT) hp).mpr hpvar) y₀ hy₀D
  have hpK : p ∈ K := by
    refine ⟨hp, ?_⟩
    rw [Metric.mem_closedBall, _root_.dist_zero_right]
    have h1 := norm_sub_le y₀ z
    have h2 : ‖p‖ ≤ ‖p - z‖ + ‖z‖ := by
      have := norm_sub_norm_le p z; linarith
    rw [hB]; linarith
  obtain ⟨i, hit, hpi⟩ : ∃ i ∈ t, p ∈ Metric.ball i.1.1 η := by
    have := ht hpK
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨i, hi, h⟩
  have hw' : i.1.2 ∈ T i.1.1 := i.2
  have hCi : ‖i.1.2‖ * (A + ‖y₀‖ + ‖i.1.1‖) ≤ C :=
    Finset.single_le_sum (f := fun i : G => ‖i.1.2‖ * (A + ‖y₀‖ + ‖i.1.1‖))
      (fun i _ => by positivity) hit
  have hxy : ‖x - i.1.1‖ ≤ A + ‖y₀‖ + ‖i.1.1‖ := (norm_sub_le _ _).trans (by linarith)
  have hzx' : z - x = lam • w := by rw [hzx]; abel
  have hxD : x ∈ closure {x | (T x).Nonempty} := subset_closure ⟨w, hw⟩
  have hkey := key_ineq hzx' (hpvar x hxD) (hT.1 i.1.1 x i.1.2 w hw' hw) hlam.le
  have hyp : ‖i.1.1 - p‖ < η := by
    rw [Metric.mem_ball, dist_eq_norm] at hpi; rwa [norm_sub_rev]
  have h1 : ‖z - x‖ * ‖i.1.1 - p‖ ≤ M * η :=
    mul_le_mul hzx_norm hyp.le (norm_nonneg _) hMnn
  have h2 : M * η < ε ^ 2 / 2 := by
    rw [hη, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hε hε]
  have h3 : lam * (‖i.1.2‖ * ‖x - i.1.1‖) ≤ lam * C :=
    mul_le_mul_of_nonneg_left
      (le_trans (mul_le_mul_of_nonneg_left hxy (norm_nonneg _)) hCi) hlam.le
  have h4 : lam * C < ε ^ 2 / 2 := by
    calc lam * C ≤ ε ^ 2 / (2 * (C + 1)) * C := mul_le_mul_of_nonneg_right hlamC hCnn
      _ < ε ^ 2 / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_pos hε hε]
  have : ‖x - p‖ ^ 2 < ε ^ 2 := by linarith
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this

end RWAux

theorem RW_chap_12_37
  (T : E → Set E)
  (hT : IsMaximalMonotone T) :
  let domT : Set E := {x | (T x).Nonempty}
  let D : Set E := closure domT
  Convex ℝ D ∧
  (∀ x, x ∈ domT → horizonCone (T x) = normalCone D x) ∧
  (∀ (lamseq : ℕ → ℝ),
    Filter.Tendsto lamseq Filter.atTop (𝓝[>] (0 : ℝ)) →
    GraphicallyConverges
      (fun n => smulMap (lamseq n) T)
      (normalCone D)) ∧
  (invMap (addMap idMap (normalCone D)) = projectionMapping D) ∧
  (∀ (lamseq : ℕ → ℝ),
    Filter.Tendsto lamseq Filter.atTop (𝓝[>] (0 : ℝ)) →
    UniformlyConvergesOnBounded
      (fun n => invMap (addMap idMap (smulMap (lamseq n) T)))
      (invMap (addMap idMap (normalCone D)))) := by
  intro domT D
  have hDconv : Convex ℝ D := RWAux.convex_closure_dom hT
  have hDclosed : IsClosed D := isClosed_closure
  have hdomD : ∀ x, x ∈ domT → x ∈ D := fun x hx => subset_closure hx
  have hN : ∀ x v, v ∈ normalCone D x ↔ (x ∈ D ∧ ∀ y ∈ D, inner ℝ v (y - x) ≤ 0) := fun x v =>
    ⟨RWAux.normalCone_sub hDconv hDclosed, fun h => RWAux.mem_normalCone_of h.1 h.2⟩
  have hext : ∀ (f : E → ℝ), Continuous f → (∀ y ∈ domT, f y ≤ 0) → ∀ y ∈ D, f y ≤ 0 :=
    fun f hf h y hy => closure_minimal h (isClosed_le hf continuous_const) hy
  -- Part 4
  have hP4 : invMap (addMap idMap (normalCone D)) = projectionMapping D := by
    funext z
    ext x
    constructor
    · rintro ⟨u, hu, v, hv, hz⟩
      have hu' : u = x := hu
      subst hu'
      subst hz
      obtain ⟨huD, hv'⟩ := (hN u v).mp hv
      refine ⟨huD, (RWAux.proj_char hDconv huD).mpr ?_⟩
      intro y hy
      have : u + v - u = v := by abel
      rw [this]; exact hv' y hy
    · rintro ⟨hxD, hmin⟩
      refine ⟨x, rfl, z - x, (hN x (z - x)).mpr ⟨hxD, (RWAux.proj_char hDconv hxD).mp hmin⟩, ?_⟩
      abel
  have hP4' : ∀ z p, p ∈ invMap (addMap idMap (normalCone D)) z ↔
      (p ∈ D ∧ ∀ y ∈ D, inner ℝ (z - p) (y - p) ≤ 0) := by
    intro z p
    rw [hP4]
    constructor
    · rintro ⟨hpD, hmin⟩; exact ⟨hpD, (RWAux.proj_char hDconv hpD).mp hmin⟩
    · rintro ⟨hpD, hvar⟩; exact ⟨hpD, (RWAux.proj_char hDconv hpD).mpr hvar⟩
  obtain ⟨y₀, w₀, h₀⟩ := RWAux.mm_graph_nonempty hT
  have hDne : D.Nonempty := ⟨y₀, hdomD y₀ ⟨w₀, h₀⟩⟩
  have hproj : ∀ z, ∃ p, p ∈ D ∧ ∀ y ∈ D, inner ℝ (z - p) (y - p) ≤ 0 := by
    intro z
    obtain ⟨p, hpD, hpd⟩ := hDclosed.exists_infDist_eq_dist hDne z
    refine ⟨p, hpD, (RWAux.proj_char hDconv hpD).mp (fun y hy => ?_)⟩
    rw [← dist_eq_norm, ← dist_eq_norm, _root_.dist_comm p z, _root_.dist_comm y z, ← hpd]
    exact Metric.infDist_le_dist_of_mem hy
  refine ⟨hDconv, ?_, ?_, hP4, ?_⟩
  · -- Part 2
    intro x hx
    ext v
    rw [hN]
    constructor
    · rintro ⟨vs, l, hvs, hl, hlim⟩
      refine ⟨hdomD x hx, ?_⟩
      apply hext (fun y => inner ℝ v (y - x)) (by fun_prop)
      rintro y ⟨w', hw'⟩
      have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hl).1
      have hlpos : ∀ᶠ i in Filter.atTop, 0 < l i := (tendsto_nhdsWithin_iff.mp hl).2
      have hlim2 : Filter.Tendsto
          (fun i => inner ℝ (l i • vs i) (x - y) - l i * inner ℝ w' (x - y)) Filter.atTop
          (𝓝 (inner ℝ v (x - y) - 0 * inner ℝ w' (x - y))) :=
        (hlim.inner tendsto_const_nhds).sub (hl0.mul_const _)
      rw [zero_mul, sub_zero] at hlim2
      have hge : 0 ≤ inner ℝ v (x - y) := by
        apply ge_of_tendsto hlim2
        filter_upwards [hlpos] with i hi
        rw [real_inner_smul_left, ← mul_sub, ← inner_sub_left]
        exact mul_nonneg hi.le (hT.1 y x w' (vs i) hw' (hvs i))
      have : inner ℝ v (y - x) = - inner ℝ v (x - y) := by rw [← inner_neg_right, neg_sub]
      show inner ℝ v (y - x) ≤ 0
      linarith
    · rintro ⟨-, hv⟩
      obtain ⟨w, hw⟩ := hx
      refine ⟨fun i => w + ((i:ℝ) + 1) • v, fun i => 1 / ((i:ℝ) + 1), fun i => ?_, ?_, ?_⟩
      · apply RWAux.mm_mem_of_forall hT
        intro y w' hw'
        have h1 := hT.1 y x w' w hw' hw
        have h2 := hv y (hdomD y ⟨w', hw'⟩)
        have : inner ℝ (w + ((i:ℝ) + 1) • v - w') (x - y) =
            inner ℝ (w - w') (x - y) + ((i:ℝ) + 1) * (- inner ℝ v (y - x)) := by
          rw [show w + ((i:ℝ) + 1) • v - w' = (w - w') + ((i:ℝ) + 1) • v by abel,
            inner_add_left, real_inner_smul_left, ← inner_neg_right, neg_sub]
        rw [this]
        have : (0:ℝ) ≤ (i:ℝ) + 1 := by positivity
        nlinarith
      · exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ),
          Filter.Eventually.of_forall (fun i => by simp only [Set.mem_Ioi]; positivity)⟩
      · have : (fun i : ℕ => (1 / ((i:ℝ) + 1)) • (w + ((i:ℝ) + 1) • v)) =
            fun i : ℕ => (1 / ((i:ℝ) + 1)) • w + v := by
          funext i
          rw [smul_add, smul_smul, div_mul_cancel₀ _ (by positivity : ((i:ℝ) + 1) ≠ 0), one_smul]
        rw [this]
        have h1 : Filter.Tendsto (fun i : ℕ => 1 / ((i:ℝ) + 1)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have := (h1.smul_const w).add_const v
        rwa [zero_smul, zero_add] at this
  · -- Part 3
    intro lamseq hlam
    have hlim0 : Filter.Tendsto lamseq Filter.atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hlam).1
    have hpos : ∀ᶠ n in Filter.atTop, 0 < lamseq n := (tendsto_nhdsWithin_iff.mp hlam).2
    have hinfsup : graphSetLiminf (fun n => smulMap (lamseq n) T) ⊆
        graphSetLimsup (fun n => smulMap (lamseq n) T) :=
      fun u hu V hV => (hu V hV).frequently
    have hsup : graphSetLimsup (fun n => smulMap (lamseq n) T) ⊆ graph (normalCone D) := by
      rintro ⟨x, v⟩ hu
      show v ∈ normalCone D x
      rw [hN]
      have hxD : x ∈ D := by
        by_contra hx
        have hV : (Dᶜ ×ˢ (Set.univ : Set E)) ∈ 𝓝 (x, v) :=
          prod_mem_nhds (hDclosed.isOpen_compl.mem_nhds hx) Filter.univ_mem
        obtain ⟨n, ⟨x', v'⟩, hgr, hmem⟩ := (hu _ hV).exists
        obtain ⟨w, hw, -⟩ := hgr
        exact hmem.1 (hdomD x' ⟨w, hw⟩)
      refine ⟨hxD, hext (fun y => inner ℝ v (y - x)) (by fun_prop) ?_⟩
      rintro y ⟨w', hw'⟩
      by_contra hcon
      push_neg at hcon
      set c := inner ℝ v (y - x) / 2 with hc
      have hc0 : 0 < c := by linarith
      set V : Set (E × E) := {q | c < inner ℝ q.2 (y - q.1)} ∩ {q | ‖q.1 - x‖ < 1} with hVdef
      have hVopen : IsOpen V :=
        (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt (by fun_prop) continuous_const)
      have hxv : (x, v) ∈ V := ⟨by show c < inner ℝ v (y - x); linarith, by simp⟩
      have hev : ∀ᶠ n in Filter.atTop,
          0 < lamseq n ∧ lamseq n * (‖w'‖ * (1 + ‖x - y‖)) < c := by
        refine hpos.and ?_
        have := hlim0.mul_const (‖w'‖ * (1 + ‖x - y‖))
        rw [zero_mul] at this
        exact this.eventually_lt_const hc0
      obtain ⟨n, ⟨⟨x', v'⟩, hgr, hmem⟩, hn0, hnc⟩ :=
        ((hu V (hVopen.mem_nhds hxv)).and_eventually hev).exists
      obtain ⟨w, hw, rfl⟩ := hgr
      obtain ⟨hm1, hm2⟩ := hmem
      simp only [Set.mem_setOf_eq] at hm1 hm2
      have hmono := hT.1 y x' w' w hw' hw
      have e1 : inner ℝ (lamseq n • w) (y - x') = - (lamseq n * inner ℝ w (x' - y)) := by
        rw [real_inner_smul_left, ← neg_sub x' y, inner_neg_right]; ring
      have e2 : inner ℝ (w - w') (x' - y) = inner ℝ w (x' - y) - inner ℝ w' (x' - y) :=
        inner_sub_left _ _ _
      have e3 : - inner ℝ w' (x' - y) ≤ ‖w'‖ * ‖x' - y‖ :=
        (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      have e4 : ‖x' - y‖ ≤ 1 + ‖x - y‖ := by
        have := norm_add_le (x' - x) (x - y)
        rw [show x' - x + (x - y) = x' - y by abel] at this
        linarith
      have e5 : ‖w'‖ * ‖x' - y‖ ≤ ‖w'‖ * (1 + ‖x - y‖) :=
        mul_le_mul_of_nonneg_left e4 (norm_nonneg _)
      rw [e1] at hm1
      nlinarith [mul_nonneg hn0.le hmono, mul_le_mul_of_nonneg_left e3 hn0.le,
        mul_le_mul_of_nonneg_left e5 hn0.le]
    have hinf : graph (normalCone D) ⊆ graphSetLiminf (fun n => smulMap (lamseq n) T) := by
      rintro ⟨x, v⟩ hxv V hV
      change v ∈ normalCone D x at hxv
      obtain ⟨hxD, hv⟩ := (hN x v).mp hxv
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
      obtain ⟨δ, hδ, hconv⟩ := RWAux.resolvent_uniform hT ‖x + v‖ ε (norm_nonneg _) hε
      have hev : ∀ᶠ n in Filter.atTop, 0 < lamseq n ∧ lamseq n < δ :=
        hpos.and (hlim0.eventually_lt_const hδ)
      filter_upwards [hev] with n hn
      obtain ⟨x', w, hw, hzx⟩ := RWAux.minty hT hn.1 (x + v)
      refine ⟨(x', lamseq n • w), ⟨w, hw, rfl⟩, hball ?_⟩
      have hclose := hconv (lamseq n) hn.1 hn.2 (x + v) x' w x le_rfl hw hzx hxD
        (fun y hy => by rw [add_sub_cancel_left]; exact hv y hy)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      refine ⟨hclose, ?_⟩
      have : lamseq n • w - v = x - x' := by
        have : lamseq n • w = x + v - x' := by rw [hzx]; abel
        rw [this]; abel
      simp only
      rw [this, norm_sub_rev]; exact hclose
    exact ⟨Set.Subset.antisymm hsup (hinf.trans hinfsup),
      Set.Subset.antisymm (hinfsup.trans hsup) hinf⟩
  · -- Part 5
    intro lamseq hlam R hR ε hε ρ hρ
    have hlim0 : Filter.Tendsto lamseq Filter.atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hlam).1
    have hpos : ∀ᶠ n in Filter.atTop, 0 < lamseq n := (tendsto_nhdsWithin_iff.mp hlam).2
    obtain ⟨δ, hδ, hconv⟩ := RWAux.resolvent_uniform hT R ε hR.le hε
    have hev : ∀ᶠ n in Filter.atTop, 0 < lamseq n ∧ lamseq n < δ :=
      hpos.and (hlim0.eventually_lt_const hδ)
    obtain ⟨N, hN'⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun n hn z hz => ⟨?_, ?_⟩⟩
    · rintro x ⟨⟨u, hu, v, ⟨w, hw, rfl⟩, hzu⟩, -⟩
      have hu' : u = x := hu
      subst hu'
      obtain ⟨p, hpD, hpvar⟩ := hproj z
      refine ⟨p, (hP4' z p).mpr ⟨hpD, hpvar⟩, ?_⟩
      rw [dist_eq_norm]
      exact hconv (lamseq n) (hN' n hn).1 (hN' n hn).2 z u w p hz hw hzu hpD hpvar
    · rintro p ⟨hp, -⟩
      obtain ⟨hpD, hpvar⟩ := (hP4' z p).mp hp
      obtain ⟨x, w, hw, hzx⟩ := RWAux.minty hT (hN' n hn).1 z
      refine ⟨x, ⟨x, rfl, lamseq n • w, ⟨w, hw, rfl⟩, hzx⟩, ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      exact hconv (lamseq n) (hN' n hn).1 (hN' n hn).2 z x w p hz hw hzx hpD hpvar

end RW_chap_12_37
