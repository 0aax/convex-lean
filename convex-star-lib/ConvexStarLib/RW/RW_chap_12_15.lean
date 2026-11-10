import ConvexStarLib.Defs

/-!
# `RW_chap_12_15`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_15` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_15`, so the main result is `RW_chap_12_15.RW_chap_12_15`.
-/

namespace RW_chap_12_15

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem RW_chap_12_15
  (T : E → Set E)
  (hT : IsMaximalMonotone T) :
  let P := invMap (addMap idMap T)
  let Q := invMap (addMap idMap (invMap T))
  let Pfun : IsSingleValued P → E → E :=
    fun hP z => Classical.choose (hP z)
  let Qfun : IsSingleValued Q → E → E :=
    fun hQ z => Classical.choose (hQ z)
  IsSingleValued P ∧
  IsSingleValued Q ∧
  IsMaximalMonotone P ∧
  IsMaximalMonotone Q ∧
  IsNonexpansive P ∧
  IsNonexpansive Q ∧
  (∀ hP : IsSingleValued P, ∀ hQ : IsSingleValued Q,
    ∀ z x v,
      (Pfun hP z, Qfun hQ z) = (x, v) ↔
      z = x + v ∧ v ∈ T x) ∧
  (∀ hP : IsSingleValued P, ∀ hQ : IsSingleValued Q,
    let g : E → E × E := fun z => (Pfun hP z, Qfun hQ z)
    Function.Injective g ∧
    Set.range g = graph T) := by
  classical
  have finite_minty : ∀ (S : Finset {p : E × E // p.2 ∈ T p.1}) [Nonempty S] (y w : S → E),
      (∀ i j, 0 ≤ inner ℝ (w i - w j) (y i - y j)) →
      ∃ x : E, ∀ i, inner ℝ (x + w i) (x - y i) ≤ 0 := by
    intro S _ y w hmono
    set s : (↥S → ℝ) → E := fun l => ∑ i, l i • (y i - w i) with hs_def
    set c : (↥S → ℝ) → ℝ := fun l => ∑ i, l i * inner ℝ (w i) (y i) with hc_def
    set D : (↥S → ℝ) → ℝ := fun l => -(1/4) * inner ℝ (s l) (s l) - c l with hD_def
    have hDcont : Continuous D := by
      simp only [hD_def, hs_def, hc_def]
      fun_prop
    obtain ⟨l, hl, hmax⟩ := (isCompact_stdSimplex ↥S).exists_isMaxOn
      ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ↥S)⟩ hDcont.continuousOn
    refine ⟨(1/2 : ℝ) • s l, fun i => ?_⟩
    -- (a) D l ≤ 0
    have hDle : D l ≤ 0 := by
      have hl1 : ∑ i, l i = 1 := hl.2
      have hl0 : ∀ i, 0 ≤ l i := hl.1
      set yb := ∑ i, l i • y i with hyb
      set wb := ∑ i, l i • w i with hwb
      have hsl : s l = yb - wb := by
        simp only [hs_def, hyb, hwb, smul_sub, Finset.sum_sub_distrib]
      have hdouble : 0 ≤ ∑ i, ∑ j, l i * l j * inner ℝ (w i - w j) (y i - y j) := by
        apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _
        exact mul_nonneg (mul_nonneg (hl0 i) (hl0 j)) (hmono i j)
      have hexpand : ∑ i, ∑ j, l i * l j * inner ℝ (w i - w j) (y i - y j) =
          ∑ i, ∑ j, l i * l j * inner ℝ (w i) (y i) - ∑ i, ∑ j, l i * l j * inner ℝ (w i) (y j)
          - ∑ i, ∑ j, l i * l j * inner ℝ (w j) (y i) + ∑ i, ∑ j, l i * l j * inner ℝ (w j) (y j) := by
        simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
        simp only [inner_sub_left, inner_sub_right]; ring
      have S1 : ∑ i, ∑ j, l i * l j * inner ℝ (w i) (y i) = c l := by
        show _ = ∑ i, l i * inner ℝ (w i) (y i)
        apply Finset.sum_congr rfl; intro i _
        calc ∑ j, l i * l j * inner ℝ (w i) (y i) = (l i * inner ℝ (w i) (y i)) * ∑ j, l j := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
          _ = l i * inner ℝ (w i) (y i) := by rw [hl1, mul_one]
      have S2 : ∑ i, ∑ j, l i * l j * inner ℝ (w i) (y j) = inner ℝ wb yb := by
        rw [hwb, sum_inner]
        apply Finset.sum_congr rfl; intro i _
        rw [real_inner_smul_left, hyb, inner_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [real_inner_smul_right]; ring
      have S3 : ∑ i, ∑ j, l i * l j * inner ℝ (w j) (y i) = inner ℝ wb yb := by
        rw [Finset.sum_comm, ← S2]
        apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
      have S4 : ∑ i, ∑ j, l i * l j * inner ℝ (w j) (y j) = c l := by
        rw [Finset.sum_comm, ← S1]
        apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
      rw [hexpand, S1, S2, S3, S4] at hdouble
      have hpar : inner ℝ (yb - wb) (yb - wb) + 4 * inner ℝ wb yb = inner ℝ (yb + wb) (yb + wb) := by
        simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
          real_inner_comm wb yb]
        ring
      have : 0 ≤ inner ℝ (yb + wb) (yb + wb) := real_inner_self_nonneg
      simp only [hD_def]
      rw [hsl]
      linarith
    -- (b) g_i(x*) ≤ D l
    have hgle : inner ℝ ((1/2 : ℝ) • s l + w i) ((1/2 : ℝ) • s l - y i) ≤ D l := by
      by_contra hcon
      push_neg at hcon
      set δ := inner ℝ ((1/2 : ℝ) • s l + w i) ((1/2 : ℝ) • s l - y i) - D l with hδ
      have hδpos : 0 < δ := by linarith
      set N := inner ℝ (s l - (y i - w i)) (s l - (y i - w i)) with hN
      have hN0 : 0 ≤ N := real_inner_self_nonneg
      have key : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * δ - t^2/4 * N ≤ 0 := by
        intro t ht0 ht1
        have hμ : (1-t) • l + t • (Pi.single i 1 : ↥S → ℝ) ∈ stdSimplex ℝ ↥S :=
          convex_stdSimplex ℝ ↥S hl (single_mem_stdSimplex ℝ i) (by linarith) ht0 (by ring)
        have h1 := isMaxOn_iff.mp hmax _ hμ
        have hsμ : s ((1-t) • l + t • (Pi.single i 1 : ↥S → ℝ)) = (1-t) • s l + t • (y i - w i) := by
          simp only [hs_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
            Finset.sum_add_distrib, ← Finset.smul_sum]
          congr 2
          rw [Fintype.sum_eq_single i (fun j hj => by simp [Pi.single_eq_of_ne hj])]
          simp
        have hcμ : c ((1-t) • l + t • (Pi.single i 1 : ↥S → ℝ)) = (1-t) * c l + t * inner ℝ (w i) (y i) := by
          simp only [hc_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
            Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 2
          rw [Fintype.sum_eq_single i (fun j hj => by simp [Pi.single_eq_of_ne hj])]
          simp
        have : D ((1-t) • l + t • (Pi.single i 1 : ↥S → ℝ)) - D l = t * δ - t^2/4 * N := by
          simp only [hD_def, hsμ, hcμ, hδ, hN, inner_add_left, inner_add_right, inner_sub_left,
            inner_sub_right, real_inner_smul_left, real_inner_smul_right]
          simp only [real_inner_comm]
          ring
        linarith
      have ht := key (δ / (δ + N)) (by positivity) (by rw [div_le_one (by linarith)]; linarith)
      have hpos : 0 < δ + N := by linarith
      have e : δ / (δ + N) * δ - (δ / (δ + N))^2/4 * N = δ^2 * (4 * δ + 3 * N) / (4 * (δ + N)^2) := by
        field_simp
        ring
      rw [e] at ht
      have : 0 < δ^2 * (4 * δ + 3 * N) / (4 * (δ + N)^2) := by positivity
      linarith
    linarith
  have minty_exists : ∀ z : E, ∃ x, z - x ∈ T x := by
    intro z
    obtain ⟨hmono, hmax⟩ := hT
    have hne : ∃ p : E × E, p.2 ∈ T p.1 := by
      by_cases h : (0:E) ∈ T 0
      · exact ⟨(0, 0), h⟩
      · obtain ⟨x, v, hv, -⟩ := hmax 0 0 h
        exact ⟨(x, v), hv⟩
    obtain ⟨p0, hp0⟩ := hne
    let K : E × E → Set E := fun p => {x | inner ℝ (x - z + p.2) (x - p.1) ≤ 0}
    have hKclosed : ∀ p, IsClosed (K p) := by
      intro p
      exact isClosed_le (by fun_prop) continuous_const
    have hKcompact : IsCompact (K p0) := by
      have hsub : K p0 ⊆ Metric.closedBall p0.1 ‖z - p0.2 - p0.1‖ := by
        intro x hx
        simp only [K, Set.mem_setOf_eq] at hx
        rw [Metric.mem_closedBall, dist_eq_norm]
        have e : x - p0.1 = (x - z + p0.2) + (z - p0.2 - p0.1) := by abel
        have h1 : ‖x - p0.1‖ ^ 2 ≤ ‖z - p0.2 - p0.1‖ * ‖x - p0.1‖ := by
          rw [← real_inner_self_eq_norm_sq]
          calc inner ℝ (x - p0.1) (x - p0.1)
              = inner ℝ (x - z + p0.2) (x - p0.1) + inner ℝ (z - p0.2 - p0.1) (x - p0.1) := by
                conv_lhs => rw [e]
                rw [inner_add_left, ← e]
            _ ≤ 0 + ‖z - p0.2 - p0.1‖ * ‖x - p0.1‖ := by
                gcongr
                exact real_inner_le_norm _ _
            _ = _ := by ring
        nlinarith [norm_nonneg (x - p0.1), norm_nonneg (z - p0.2 - p0.1)]
      exact (isCompact_closedBall _ _).of_isClosed_subset (hKclosed p0) hsub
    have hfin : ∀ u : Finset {p : E × E // p.2 ∈ T p.1},
        (K p0 ∩ ⋂ i ∈ u, K i.1).Nonempty := by
      intro u
      let S : Finset {p : E × E // p.2 ∈ T p.1} := insert ⟨p0, hp0⟩ u
      haveI : Nonempty S := ⟨⟨⟨p0, hp0⟩, Finset.mem_insert_self _ _⟩⟩
      obtain ⟨x, hx⟩ := finite_minty S (fun i => i.1.1.1) (fun i => i.1.1.2 - z) (by
        intro i j
        have := hmono j.1.1.1 i.1.1.1 j.1.1.2 i.1.1.2 j.1.2 i.1.2
        simpa using this)
      refine ⟨x, ?_, ?_⟩
      · have := hx ⟨⟨p0, hp0⟩, Finset.mem_insert_self _ _⟩
        simp only [K, Set.mem_setOf_eq]
        convert this using 2; abel
      · simp only [Set.mem_iInter]
        intro i hi
        have := hx ⟨i, Finset.mem_insert_of_mem hi⟩
        simp only [K, Set.mem_setOf_eq]
        convert this using 2; abel
    obtain ⟨x, -, hx⟩ := hKcompact.inter_iInter_nonempty
      (fun i : {p : E × E // p.2 ∈ T p.1} => K i.1) (fun i => hKclosed _) hfin
    refine ⟨x, ?_⟩
    by_contra hcon
    obtain ⟨x', v', hv', hlt⟩ := hmax x (z - x) hcon
    have h1 := Set.mem_iInter.mp hx ⟨(x', v'), hv'⟩
    simp only [K, Set.mem_setOf_eq] at h1
    have e : inner ℝ (z - x - v') (x - x') = - inner ℝ (x - z + v') (x - x') := by
      rw [← inner_neg_left]; congr 1; abel
    linarith
  have firm_lemma : ∀ (S : E → Set E), IsSingleValued S →
      (∀ z₀ z₁ x₀ x₁, x₀ ∈ S z₀ → x₁ ∈ S z₁ → ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (x₁ - x₀) (z₁ - z₀)) →
      IsMaximalMonotone S ∧ IsNonexpansive S := by
    intro S hS hfirm
    have hne : IsNonexpansive S := by
      intro z₀ z₁ w₀ w₁ h₀ h₁
      have h := hfirm z₀ z₁ w₀ w₁ h₀ h₁
      have hcs := real_inner_le_norm (w₁ - w₀) (z₁ - z₀)
      have hn0 := norm_nonneg (w₁ - w₀)
      have hn1 := norm_nonneg (z₁ - z₀)
      nlinarith
    refine ⟨⟨?_, ?_⟩, hne⟩
    · intro z₀ z₁ x₀ x₁ h₀ h₁
      have h := hfirm z₀ z₁ x₀ x₁ h₀ h₁
      have : 0 ≤ ‖x₁ - x₀‖ ^ 2 := sq_nonneg _
      linarith
    · intro zh xh hxh
      obtain ⟨xz, hxz, -⟩ := hS zh
      set d := xh - xz with hd
      have hd0 : d ≠ 0 := by
        intro h; apply hxh; rw [hd, sub_eq_zero] at h; rw [h]; exact hxz
      obtain ⟨xt, hxt, -⟩ := hS (zh + (1/2 : ℝ) • d)
      refine ⟨zh + (1/2:ℝ) • d, xt, hxt, ?_⟩
      have hnexp := hne zh (zh + (1/2:ℝ) • d) xz xt hxz hxt
      have e1 : zh - (zh + (1/2:ℝ) • d) = -((1/2:ℝ) • d) := by abel
      have e2 : xh - xt = d - (xt - xz) := by rw [hd]; abel
      rw [e1, e2, inner_neg_right, real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq]
      have hcs := real_inner_le_norm (xt - xz) d
      have e3 : ‖zh + (1/2:ℝ) • d - zh‖ = (1/2) * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul]; norm_num
      rw [e3] at hnexp
      have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
      nlinarith
  intro P Q Pfun Qfun
  have hmono := hT.1
  have hPmem : ∀ z x, x ∈ P z ↔ z - x ∈ T x := by
    intro z x
    simp only [P, invMap, addMap, idMap, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl, v, hv, rfl⟩; simpa using hv
    · intro h; exact ⟨x, rfl, z - x, h, by abel⟩
  have hQmem : ∀ z v, v ∈ Q z ↔ v ∈ T (z - v) := by
    intro z v
    simp only [Q, invMap, addMap, idMap, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl, x, hx, rfl⟩; simpa using hx
    · intro h; exact ⟨v, rfl, z - v, h, by abel⟩
  have hex : ∀ z, ∃ x, z - x ∈ T x := minty_exists
  have huniq : ∀ z x₁ x₂, z - x₁ ∈ T x₁ → z - x₂ ∈ T x₂ → x₁ = x₂ := by
    intro z x₁ x₂ h₁ h₂
    have h := hmono x₁ x₂ (z - x₁) (z - x₂) h₁ h₂
    have e : (z - x₂) - (z - x₁) = -(x₂ - x₁) := by abel
    rw [e, inner_neg_left, real_inner_self_eq_norm_sq] at h
    have h0 : ‖x₂ - x₁‖ = 0 := by nlinarith [norm_nonneg (x₂ - x₁)]
    rw [norm_eq_zero, sub_eq_zero] at h0
    exact h0.symm
  have hPsv : IsSingleValued P := by
    intro z
    obtain ⟨x, hx⟩ := hex z
    exact ⟨x, (hPmem z x).2 hx, fun y hy => huniq z y x ((hPmem z y).1 hy) hx⟩
  have hQsv : IsSingleValued Q := by
    intro z
    obtain ⟨x, hx⟩ := hex z
    refine ⟨z - x, (hQmem z _).2 (by simpa using hx), fun v hv => ?_⟩
    have hv' := (hQmem z v).1 hv
    have h : z - v = x := huniq z (z - v) x (by simpa using hv') hx
    rw [← h]; abel
  have hPfirm : ∀ z₀ z₁ x₀ x₁, x₀ ∈ P z₀ → x₁ ∈ P z₁ →
      ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (x₁ - x₀) (z₁ - z₀) := by
    intro z₀ z₁ x₀ x₁ h₀ h₁
    have h := hmono x₀ x₁ (z₀ - x₀) (z₁ - x₁) ((hPmem _ _).1 h₀) ((hPmem _ _).1 h₁)
    have e : (z₁ - x₁) - (z₀ - x₀) = (z₁ - z₀) - (x₁ - x₀) := by abel
    rw [e, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm] at h
    linarith
  have hQfirm : ∀ z₀ z₁ v₀ v₁, v₀ ∈ Q z₀ → v₁ ∈ Q z₁ →
      ‖v₁ - v₀‖ ^ 2 ≤ inner ℝ (v₁ - v₀) (z₁ - z₀) := by
    intro z₀ z₁ v₀ v₁ h₀ h₁
    have h := hmono (z₀ - v₀) (z₁ - v₁) v₀ v₁ ((hQmem _ _).1 h₀) ((hQmem _ _).1 h₁)
    have e : (z₁ - v₁) - (z₀ - v₀) = (z₁ - z₀) - (v₁ - v₀) := by abel
    rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at h
    linarith
  obtain ⟨hPmax, hPne⟩ := firm_lemma P hPsv hPfirm
  obtain ⟨hQmax, hQne⟩ := firm_lemma Q hQsv hQfirm
  have hchar : ∀ hP : IsSingleValued P, ∀ hQ : IsSingleValued Q, ∀ z x v,
      (Pfun hP z, Qfun hQ z) = (x, v) ↔ z = x + v ∧ v ∈ T x := by
    intro hP hQ z x v
    obtain ⟨ha, ha'⟩ := Classical.choose_spec (hP z)
    obtain ⟨hb, hb'⟩ := Classical.choose_spec (hQ z)
    change (Classical.choose (hP z), Classical.choose (hQ z)) = (x, v) ↔ _
    constructor
    · intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at ha ha'
      rw [h2] at hb hb'
      have hb2 := (hQmem z v).1 hb
      have h3 : z - v = x := ha' (z - v) ((hPmem z _).2 (by simpa using hb2))
      refine ⟨?_, ?_⟩
      · rw [← h3]; abel
      · rw [← h3]; exact hb2
    · rintro ⟨rfl, hv⟩
      have h1 : x = Classical.choose (hP (x + v)) := ha' x ((hPmem _ _).2 (by simpa using hv))
      have h2 : v = Classical.choose (hQ (x + v)) := hb' v ((hQmem _ _).2 (by simpa using hv))
      rw [← h1, ← h2]
  refine ⟨hPsv, hQsv, hPmax, hQmax, hPne, hQne, hchar, ?_⟩
  intro hP hQ g
  refine ⟨?_, ?_⟩
  · intro z₁ z₂ h
    have h1 := (hchar hP hQ z₁ (g z₁).1 (g z₁).2).1 rfl
    have h2 := (hchar hP hQ z₂ (g z₁).1 (g z₁).2).1 h.symm
    rw [h1.1, h2.1]
  · ext ⟨x, v⟩
    simp only [Set.mem_range, graph, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz⟩
      exact ((hchar hP hQ z x v).1 hz).2
    · intro hv
      exact ⟨x + v, (hchar hP hQ (x + v) x v).2 ⟨rfl, hv⟩⟩

end RW_chap_12_15
