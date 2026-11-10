import ConvexStarLib.Defs

/-!
# `RW_chap_11_34`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_11_34` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_11_34`, so the main result is `RW_chap_11_34.RW_chap_11_34`.
-/

namespace RW_chap_11_34

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Auxiliary lemmas -/

lemma E_sub_le_iff (a β : ℝ) (z : EReal) :
    (a : EReal) - z ≤ (β : EReal) ↔ ((a - β : ℝ) : EReal) ≤ z := by
  induction z using EReal.rec with
  | bot =>
    rw [EReal.coe_sub_bot]
    simp only [top_le_iff, le_bot_iff, EReal.coe_ne_top, EReal.coe_ne_bot]
  | top =>
    rw [EReal.sub_top]
    simp only [bot_le, le_top]
  | coe z =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma conj_le_iff (f : E → EReal) (v : E) (β : ℝ) :
    conjugate f v ≤ (β : EReal) ↔ ∀ x, (((inner ℝ v x) - β : ℝ) : EReal) ≤ f x := by
  unfold conjugate
  rw [sSup_le_iff, Set.forall_mem_image]
  constructor
  · intro hx x
    exact (E_sub_le_iff _ _ _).mp (hx (Set.mem_univ x))
  · intro hx x _
    exact (E_sub_le_iff _ _ _).mpr (hx x)

lemma gen_ineq (fseq : ℕ → E → EReal) (f : E → EReal)
    (h : epigraph f ⊆ epiLimsupSet fseq) :
    epiLiminfSet (fun ν => conjugate (fseq ν)) ⊆ epigraph (conjugate f) := by
  rintro ⟨v, β⟩ hvb
  simp only [epiLiminfSet, setLimsup, Set.mem_setOf_eq] at hvb
  show conjugate f v ≤ (β : EReal)
  rw [conj_le_iff]
  intro x
  have key : ∀ s : ℝ, f x ≤ (s : EReal) → inner ℝ v x - β ≤ s := by
    intro s hs
    by_contra hlt
    push_neg at hlt
    have hxs : ((x, s) : E × ℝ) ∈ epiLimsupSet fseq :=
      h (show ((x, s) : E × ℝ) ∈ epigraph f from hs)
    simp only [epiLimsupSet, setLiminf, Set.mem_setOf_eq] at hxs
    let Φ : (E × ℝ) × (E × ℝ) → ℝ := fun pq => inner ℝ pq.2.1 pq.1.1 - pq.1.2 - pq.2.2
    have hΦ : Continuous Φ := by
      fun_prop
    have hmem : Φ ⁻¹' Set.Ioi 0 ∈ 𝓝 (((x, s), (v, β)) : (E × ℝ) × (E × ℝ)) := by
      apply hΦ.continuousAt.preimage_mem_nhds
      apply Ioi_mem_nhds
      show (0 : ℝ) < inner ℝ v x - s - β
      linarith
    rw [mem_nhds_prod_iff] at hmem
    obtain ⟨U, hU, W, hW, hUW⟩ := hmem
    have h1 := hxs U hU
    have h2 := hvb W hW
    obtain ⟨n, ⟨q, hq, hqW⟩, ⟨p, hp, hpU⟩⟩ := (h2.and_eventually h1).exists
    have hpq : ((p, q) : (E × ℝ) × (E × ℝ)) ∈ Φ ⁻¹' Set.Ioi 0 := hUW (Set.mk_mem_prod hpU hqW)
    have hpq' : (0 : ℝ) < inner ℝ q.1 p.1 - p.2 - q.2 := hpq
    have hp' : fseq n p.1 ≤ (p.2 : EReal) := hp
    have hq' : conjugate (fseq n) q.1 ≤ (q.2 : EReal) := hq
    rw [conj_le_iff] at hq'
    have h3 := (hq' p.1).trans hp'
    rw [EReal.coe_le_coe_iff] at h3
    linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  have h4 := key r hr1.le
  have h5 := EReal.coe_lt_coe_iff.mp hr2
  linarith

lemma setLiminf_subset_setLimsup {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) :
    setLiminf A ⊆ setLimsup A := fun _ hu V hV => (hu V hV).frequently

lemma eventually_gt_on_compact (fseq : ℕ → E → EReal) (K : Set E) (hK : IsCompact K)
    (g : E → ℝ) (hg : Continuous g)
    (h : ∀ x ∈ K, (x, g x) ∉ epiLiminfSet fseq) :
    ∀ᶠ n in Filter.atTop, ∀ y ∈ K, ((g y : ℝ) : EReal) < fseq n y := by
  refine hK.induction_on
    (p := fun S => ∀ᶠ n in Filter.atTop, ∀ y ∈ S, ((g y : ℝ) : EReal) < fseq n y) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun n y hy => by simp at hy)
  · intro s t hst ht
    exact ht.mono (fun n hn y hy => hn y (hst hy))
  · intro s t hs ht
    filter_upwards [hs, ht] with n hn1 hn2
    intro y hy
    rcases hy with hy | hy
    · exact hn1 y hy
    · exact hn2 y hy
  · intro x hx
    have hx' := h x hx
    simp only [epiLiminfSet, setLimsup, Set.mem_setOf_eq, not_forall, Filter.not_frequently]
      at hx'
    obtain ⟨V, hV, hev⟩ := hx'
    refine ⟨(fun y => (y, g y)) ⁻¹' V, ?_, ?_⟩
    · apply mem_nhdsWithin_of_mem_nhds
      exact (continuous_id.prodMk hg).continuousAt.preimage_mem_nhds hV
    · filter_upwards [hev] with n hn
      intro y hy
      by_contra hcon
      exact hn ⟨(y, g y), not_lt.mp hcon, hy⟩

lemma eventually_bdd_below_on_compact (fseq : ℕ → E → EReal) (K : Set E) (hK : IsCompact K)
    (h : ∀ x ∈ K, ∃ s : ℝ, (x, s) ∉ epiLiminfSet fseq) :
    ∃ m : ℝ, ∀ᶠ n in Filter.atTop, ∀ y ∈ K, ((m : ℝ) : EReal) < fseq n y := by
  refine hK.induction_on
    (p := fun S => ∃ m : ℝ, ∀ᶠ n in Filter.atTop, ∀ y ∈ S, ((m : ℝ) : EReal) < fseq n y)
    ?_ ?_ ?_ ?_
  · exact ⟨0, Filter.Eventually.of_forall (fun n y hy => by simp at hy)⟩
  · intro s t hst ht
    obtain ⟨m, hm⟩ := ht
    exact ⟨m, hm.mono (fun n hn y hy => hn y (hst hy))⟩
  · intro s t hs ht
    obtain ⟨m1, hm1⟩ := hs
    obtain ⟨m2, hm2⟩ := ht
    refine ⟨min m1 m2, ?_⟩
    filter_upwards [hm1, hm2] with n hn1 hn2
    intro y hy
    rcases hy with hy | hy
    · exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (min_le_left _ _)) (hn1 y hy)
    · exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (min_le_right _ _)) (hn2 y hy)
  · intro x hx
    obtain ⟨s, hs⟩ := h x hx
    simp only [epiLiminfSet, setLimsup, Set.mem_setOf_eq, not_forall, Filter.not_frequently]
      at hs
    obtain ⟨V, hV, hev⟩ := hs
    refine ⟨(fun y => (y, s)) ⁻¹' V, ?_, s, ?_⟩
    · apply mem_nhdsWithin_of_mem_nhds
      exact (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hV
    · filter_upwards [hev] with n hn
      intro y hy
      by_contra hcon
      exact hn ⟨(y, s), not_lt.mp hcon, hy⟩

lemma dual_lemma (F : E → EReal) (hF : Convex ℝ (epigraph F)) (v : E) (m δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x, ((inner ℝ v x + m - δ * ‖x‖ : ℝ) : EReal) ≤ F x) :
    ∃ w : E, ‖w - v‖ ≤ δ ∧ ∀ x, ((inner ℝ w x + m : ℝ) : EReal) ≤ F x := by
  classical
  -- F never takes the value ⊥
  have hbot : ∀ y, F y ≠ ⊥ := by
    intro y hy
    have := h y
    rw [hy] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  by_cases hne : (epigraph F).Nonempty
  swap
  · -- empty epigraph: F ≡ ⊤
    refine ⟨v, by simp [hδ], fun x => ?_⟩
    have hFx : F x = ⊤ := by
      by_contra hx
      apply hne
      refine ⟨(x, (F x).toReal), ?_⟩
      show F x ≤ ((F x).toReal : EReal)
      rw [EReal.coe_toReal hx (hbot x)]
    rw [hFx]; exact le_top
  · set C : Set (E × ℝ) := {p | p.2 < inner ℝ v p.1 + m - δ * ‖p.1‖} with hC
    have hCopen : IsOpen C := by
      apply isOpen_lt
      · exact continuous_snd
      · fun_prop
    have hCconv : Convex ℝ C := by
      intro p hp q hq a b ha hb hab
      simp only [hC, Set.mem_setOf_eq] at hp hq ⊢
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have h1 : ‖a • p.1 + b • q.1‖ ≤ a * ‖p.1‖ + b * ‖q.1‖ := by
        calc ‖a • p.1 + b • q.1‖ ≤ ‖a • p.1‖ + ‖b • q.1‖ := norm_add_le _ _
        _ = a * ‖p.1‖ + b * ‖q.1‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      have h2 : δ * ‖a • p.1 + b • q.1‖ ≤ δ * (a * ‖p.1‖ + b * ‖q.1‖) :=
        mul_le_mul_of_nonneg_left h1 hδ
      have hm : m = a * m + b * m := by rw [← add_mul, hab, one_mul]
      rcases ha.lt_or_eq with hapos | ha0
      · have h3 := mul_lt_mul_of_pos_left hp hapos
        have h4 := mul_le_mul_of_nonneg_left hq.le hb
        linarith
      · subst ha0
        have hb1 : b = 1 := by linarith
        subst hb1
        simp only [zero_mul, zero_add, one_mul, zero_smul, one_smul] at h2 ⊢
        linarith
    have hdisj : Disjoint C (epigraph F) := by
      rw [Set.disjoint_left]
      rintro ⟨x, s⟩ hxC hxE
      simp only [hC, Set.mem_setOf_eq] at hxC
      have h1 : F x ≤ (s : EReal) := hxE
      have h2 := (h x).trans h1
      rw [EReal.coe_le_coe_iff] at h2
      linarith
    obtain ⟨ℓ, u, hℓC, hℓE⟩ := geometric_hahn_banach_open hCconv hCopen hF hdisj
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    set c : ℝ := ℓ ((0 : E), (1 : ℝ)) with hc
    set w' : E := (InnerProductSpace.toDual ℝ E).symm (ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ))
      with hw'
    have hdecomp : ∀ y : E, ∀ s : ℝ, ℓ (y, s) = inner ℝ w' y + s * c := by
      intro y s
      have : ((y, s) : E × ℝ) = (y, (0 : ℝ)) + s • ((0 : E), (1 : ℝ)) := by
        ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul, hw', InnerProductSpace.toDual_symm_apply]
      simp [hc]
    -- inequality from C
    have hCineq : ∀ x : E, ∀ s : ℝ, s < inner ℝ v x + m - δ * ‖x‖ →
        inner ℝ w' x + s * c < u := by
      intro x s hs
      have := hℓC (x, s) hs
      rwa [hdecomp] at this
    -- inequality from epigraph
    have hEineq : ∀ y : E, ∀ s : ℝ, F y ≤ (s : EReal) → u ≤ inner ℝ w' y + s * c := by
      intro y s hs
      have := hℓE (y, s) hs
      rwa [hdecomp] at this
    -- c ≥ 0
    have hc0 : 0 ≤ c := by
      by_contra hneg
      push_neg at hneg
      set s : ℝ := min (m - 1) (u / c) with hs
      have hs1 : s < inner ℝ v (0 : E) + m - δ * ‖(0 : E)‖ := by
        simp only [inner_zero_right, norm_zero, mul_zero, zero_add, sub_zero]
        have := min_le_left (m - 1) (u / c)
        linarith
      have h1 := hCineq 0 s hs1
      rw [inner_zero_right, zero_add] at h1
      have h2 : (u / c) * c ≤ s * c :=
        mul_le_mul_of_nonpos_right (min_le_right _ _) hneg.le
      rw [div_mul_cancel₀ u hneg.ne] at h2
      linarith
    -- c ≠ 0
    have hcpos : 0 < c := by
      rcases hc0.lt_or_eq with hpos | hzero
      · exact hpos
      · exfalso
        obtain ⟨⟨y, s⟩, hys⟩ := hne
        have hall : ∀ x : E, inner ℝ w' x < u := by
          intro x
          have := hCineq x (inner ℝ v x + m - δ * ‖x‖ - 1) (by linarith)
          rw [← hzero, mul_zero, add_zero] at this
          exact this
        have h0 := hall 0
        rw [inner_zero_right] at h0
        have hy := hEineq y s hys
        rw [← hzero, mul_zero, add_zero] at hy
        have h2 := hall ((2 : ℝ) • y)
        rw [real_inner_smul_right] at h2
        linarith
    -- the limit inequality
    have hlim : ∀ x : E, inner ℝ w' x + (inner ℝ v x + m - δ * ‖x‖) * c ≤ u := by
      intro x
      by_contra hgt
      push_neg at hgt
      set D := inner ℝ w' x + (inner ℝ v x + m - δ * ‖x‖) * c - u with hD
      have hDpos : 0 < D := by rw [hD]; linarith
      have hs : inner ℝ v x + m - δ * ‖x‖ - D / c < inner ℝ v x + m - δ * ‖x‖ := by
        have : 0 < D / c := div_pos hDpos hcpos
        linarith
      have h1 := hCineq x _ hs
      have h2 : (inner ℝ v x + m - δ * ‖x‖ - D / c) * c
          = (inner ℝ v x + m - δ * ‖x‖) * c - D := by
        field_simp
      rw [h2] at h1
      linarith
    set w : E := -(1 / c) • w' with hw
    set K : ℝ := u / c with hK
    have hinner_w : ∀ x : E, inner ℝ w x = -(1 / c) * inner ℝ w' x := by
      intro x
      rw [hw, real_inner_smul_left]
    -- key bounds
    have hFbound : ∀ y : E, ∀ r : ℝ, F y ≤ (r : EReal) → inner ℝ w y + K ≤ r := by
      intro y r hr
      have h1 := hEineq y r hr
      rw [hinner_w, hK]
      have : u / c ≤ inner ℝ w' y / c + r := by
        rw [div_le_iff₀ hcpos]
        have : (inner ℝ w' y / c + r) * c = inner ℝ w' y + r * c := by
          field_simp
        linarith
      have h3 : -(1 / c) * inner ℝ w' y = - (inner ℝ w' y / c) := by ring
      linarith
    have hxbound : ∀ x : E, inner ℝ (v - w) x - δ * ‖x‖ ≤ K - m := by
      intro x
      have h1 := hlim x
      rw [inner_sub_left, hinner_w, hK]
      have : inner ℝ w' x / c + (inner ℝ v x + m - δ * ‖x‖) ≤ u / c := by
        rw [le_div_iff₀ hcpos]
        have : (inner ℝ w' x / c + (inner ℝ v x + m - δ * ‖x‖)) * c
            = inner ℝ w' x + (inner ℝ v x + m - δ * ‖x‖) * c := by
          field_simp
        linarith
      have h3 : -(1 / c) * inner ℝ w' x = - (inner ℝ w' x / c) := by ring
      linarith
    have hmK : m ≤ K := by
      have := hxbound 0
      simp only [inner_zero_right, norm_zero, mul_zero, sub_zero] at this
      linarith
    refine ⟨w, ?_, ?_⟩
    · rw [norm_sub_rev]
      by_contra hgt
      push_neg at hgt
      set d := v - w with hd
      have hP : 0 < ‖d‖ * (‖d‖ - δ) := by
        apply _root_.mul_pos
        · linarith
        · linarith
      set k : ℝ := (K - m + 1) / (‖d‖ * (‖d‖ - δ)) with hk
      have hkpos : 0 < k := div_pos (by linarith) hP
      have h1 := hxbound (k • d)
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
        Real.norm_of_nonneg hkpos.le] at h1
      have h2 : k * ‖d‖ ^ 2 - δ * (k * ‖d‖) = k * (‖d‖ * (‖d‖ - δ)) := by ring
      have h3 : k * (‖d‖ * (‖d‖ - δ)) = K - m + 1 := by
        rw [hk, div_mul_cancel₀ _ hP.ne']
      linarith
    · intro x
      induction hFx : F x using EReal.rec with
      | bot => exact absurd hFx (hbot x)
      | top => exact le_top
      | coe r =>
        rw [EReal.coe_le_coe_iff]
        have := hFbound x r (le_of_eq hFx)
        linarith

lemma C_key (F : E → EReal) (hF : Convex ℝ (epigraph F)) (v x0 : E) (r R m a : ℝ)
    (hr : 0 ≤ r) (hR : 2 * r < R) (hx0 : ‖x0‖ ≤ r) (hFx0 : F x0 ≤ (a : EReal))
    (hball : ∀ x, ‖x‖ ≤ R → ((inner ℝ v x + m : ℝ) : EReal) ≤ F x)
    (hAm : 0 ≤ a + r * ‖v‖ - m) (hp : -(r * ‖v‖) ≤ inner ℝ v x0)
    (x : E) (hx : R < ‖x‖) (s : ℝ) (hs : F x ≤ (s : EReal)) :
    inner ℝ v x + m - ((a + r * ‖v‖ - m) / (R - r)) * ‖x‖ ≤ s := by
  have hρ : 0 < R - r := by linarith
  have hd1 : ‖x‖ - ‖x0‖ ≤ ‖x - x0‖ := norm_sub_norm_le x x0
  have hd2 : ‖x - x0‖ ≤ ‖x‖ + ‖x0‖ := norm_sub_le x x0
  have hdρ : R - r < ‖x - x0‖ := by linarith
  have hdpos : 0 < ‖x - x0‖ := by linarith
  have htd : (R - r) / ‖x - x0‖ * ‖x - x0‖ = R - r := div_mul_cancel₀ (R - r) hdpos.ne'
  have ht0 : 0 < (R - r) / ‖x - x0‖ := div_pos hρ hdpos
  have ht1 : (R - r) / ‖x - x0‖ < 1 := (div_lt_one hdpos).mpr hdρ
  set t := (R - r) / ‖x - x0‖ with ht_def
  set d := ‖x - x0‖ with hd_def
  have hconv := hF (show (x0, a) ∈ epigraph F from hFx0) (show (x, s) ∈ epigraph F from hs)
    (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
  have hy : F ((1 - t) • x0 + t • x) ≤ (((1 - t) * a + t * s : ℝ) : EReal) := by
    simpa [epigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hconv
  have hyeq : (1 - t) • x0 + t • x = x0 + t • (x - x0) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  have hynorm : ‖(1 - t) • x0 + t • x‖ ≤ R := by
    rw [hyeq]
    calc ‖x0 + t • (x - x0)‖ ≤ ‖x0‖ + ‖t • (x - x0)‖ := norm_add_le _ _
      _ = ‖x0‖ + t * d := by rw [norm_smul_of_nonneg ht0.le]
      _ ≤ R := by linarith
  have hb := hball _ hynorm
  have H : inner ℝ v ((1 - t) • x0 + t • x) + m ≤ (1 - t) * a + t * s := by
    exact_mod_cast le_trans hb hy
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at H
  have H2 : (1 - t) * (a - inner ℝ v x0) ≤ (1 - t) * (a + r * ‖v‖) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have H3 : m - (a + r * ‖v‖) ≤ t * (s - inner ℝ v x - (a + r * ‖v‖)) := by linarith
  have H4 : d * (m - (a + r * ‖v‖)) ≤ d * (t * (s - inner ℝ v x - (a + r * ‖v‖))) :=
    mul_le_mul_of_nonneg_left H3 hdpos.le
  have H5 : d * (t * (s - inner ℝ v x - (a + r * ‖v‖)))
      = (R - r) * (s - inner ℝ v x - (a + r * ‖v‖)) := by
    rw [← mul_assoc, mul_comm d t, htd]
  have H6 : 0 ≤ (‖x‖ + r - d) * (a + r * ‖v‖ - m) := mul_nonneg (by linarith) hAm
  have H7 : 0 ≤ (R - 2 * r) * (a + r * ‖v‖ - m) := mul_nonneg (by linarith) hAm
  have hδ : (a + r * ‖v‖ - m) / (R - r) * (R - r) = a + r * ‖v‖ - m :=
    div_mul_cancel₀ _ hρ.ne'
  have hδn : (a + r * ‖v‖ - m) / (R - r) * (R - r) * ‖x‖ = (a + r * ‖v‖ - m) * ‖x‖ := by
    rw [hδ]
  have key : (R - r) * (inner ℝ v x + m - ((a + r * ‖v‖ - m) / (R - r)) * ‖x‖)
      ≤ (R - r) * s := by
    linarith
  exact le_of_mul_le_mul_left key hρ

lemma cone_bound (F : E → EReal) (hF : Convex ℝ (epigraph F)) (v x0 : E) (r R m a : ℝ)
    (hr : 0 ≤ r) (hR : 2 * r < R) (hx0 : ‖x0‖ ≤ r) (hFx0 : F x0 ≤ (a : EReal))
    (hball : ∀ x, ‖x‖ ≤ R → ((inner ℝ v x + m : ℝ) : EReal) ≤ F x) :
    ∀ x, ((inner ℝ v x + m - ((a + r * ‖v‖ - m) / (R - r)) * ‖x‖ : ℝ) : EReal) ≤ F x := by
  intro x
  have hρ : 0 < R - r := by linarith
  have hx0R : ‖x0‖ ≤ R := by linarith
  have h3 : inner ℝ v x0 + m ≤ a := by
    have := le_trans (hball x0 hx0R) hFx0
    exact_mod_cast this
  have hp : -(r * ‖v‖) ≤ inner ℝ v x0 := by
    have h4 := (abs_le.mp (abs_real_inner_le_norm v x0)).1
    have h5 : ‖v‖ * ‖x0‖ ≤ ‖v‖ * r := mul_le_mul_of_nonneg_left hx0 (norm_nonneg v)
    linarith
  have hAm : 0 ≤ a + r * ‖v‖ - m := by linarith
  have hδ : 0 ≤ (a + r * ‖v‖ - m) / (R - r) := div_nonneg hAm hρ.le
  by_cases hxR : ‖x‖ ≤ R
  · refine le_trans ?_ (hball x hxR)
    rw [EReal.coe_le_coe_iff]
    have := mul_nonneg hδ (norm_nonneg x)
    linarith
  · push_neg at hxR
    rcases eq_bot_or_bot_lt (F x) with hbot | hbot
    · exfalso
      have := C_key F hF v x0 r R m a hr hR hx0 hFx0 hball hAm hp x hxR
        (inner ℝ v x + m - ((a + r * ‖v‖ - m) / (R - r)) * ‖x‖ - 1)
        (by rw [hbot]; exact bot_le)
      linarith
    rcases eq_top_or_lt_top (F x) with htop | htop
    · rw [htop]; exact le_top
    · have hc := EReal.coe_toReal htop.ne hbot.ne'
      rw [← hc, EReal.coe_le_coe_iff]
      exact C_key F hF v x0 r R m a hr hR hx0 hFx0 hball hAm hp x hxR (F x).toReal hc.ge

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma A_epi_closed (f : E → EReal) (hl : LowerSemicontinuous f) : IsClosed (epigraph f) := by
  have h := hl.isClosed_epigraph
  have hcont : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  exact h.preimage hcont

lemma A_sep (f : E → EReal) (hl : LowerSemicontinuous f) (hc : ConvexEReal f) (x : E) (t : ℝ)
    (hxt : ¬ f x ≤ (t : EReal)) (y0 : E) (s0 : ℝ) (h0 : f y0 ≤ (s0 : EReal)) :
    ∃ w : E, ∃ c u : ℝ, 0 ≤ c ∧ inner ℝ w x + c * t < u ∧
      ∀ y (s : ℝ), f y ≤ (s : EReal) → u < inner ℝ w y + c * s := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hnot : ((x, t) : E × ℝ) ∉ epigraph f := hxt
  obtain ⟨ℓ, u, hℓx, hℓb⟩ := geometric_hahn_banach_point_closed hc (A_epi_closed f hl) hnot
  set w : E := (InnerProductSpace.toDual ℝ E).symm (ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ))
    with hw
  set c : ℝ := ℓ ((0 : E), (1 : ℝ)) with hc_def
  have hdecomp : ∀ y : E, ∀ s : ℝ, ℓ (y, s) = inner ℝ w y + c * s := by
    intro y s
    have h1 : ((y, s) : E × ℝ) = (y, 0) + s • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [h1, map_add, map_smul, hw, InnerProductSpace.toDual_symm_apply]
    simp [smul_eq_mul, mul_comm, hc_def]
  have hb : ∀ y (s : ℝ), f y ≤ (s : EReal) → u < inner ℝ w y + c * s := by
    intro y s hys
    have := hℓb (y, s) hys
    rwa [hdecomp] at this
  refine ⟨w, c, u, ?_, ?_, hb⟩
  · by_contra hneg
    push_neg at hneg
    set D := inner ℝ w y0 + c * s0 - u with hD
    have hD0 : 0 < D := by have := hb y0 s0 h0; linarith
    have hk : 0 ≤ D / (-c) := by
      apply div_nonneg hD0.le; linarith
    have h2 := hb y0 (s0 + D / (-c)) (by
      refine h0.trans ?_
      exact_mod_cast (by linarith : s0 ≤ s0 + D / (-c)))
    have h3 : c * (D / (-c)) = -D := by
      have : c ≠ 0 := hneg.ne
      field_simp
    rw [mul_add, h3] at h2
    linarith
  · have := hℓx
    rwa [hdecomp] at this

omit [FiniteDimensional ℝ E] in
lemma A_pos (f : E → EReal) (hbot : ∀ y, ⊥ < f y) (x : E) (t : ℝ) (w : E) (c u : ℝ)
    (hc : 0 < c) (hx : inner ℝ w x + c * t < u)
    (hb : ∀ y (s : ℝ), f y ≤ (s : EReal) → u < inner ℝ w y + c * s) :
    ∃ v : E, ∃ β : ℝ, (∀ y, ((inner ℝ v y - β : ℝ) : EReal) ≤ f y) ∧ t < inner ℝ v x - β := by
  have key : ∀ z : E, inner ℝ (-(1 / c) • w) z - (-u / c) = (u - inner ℝ w z) / c := by
    intro z
    rw [real_inner_smul_left]
    field_simp
    ring
  refine ⟨-(1 / c) • w, -u / c, ?_, ?_⟩
  · intro y
    rw [key]
    by_cases htop : f y = ⊤
    · rw [htop]; exact le_top
    · obtain ⟨r, hr⟩ : ∃ r : ℝ, f y = (r : EReal) :=
        ⟨(f y).toReal, (EReal.coe_toReal htop (hbot y).ne').symm⟩
      have := hb y r hr.le
      rw [hr, EReal.coe_le_coe_iff, div_le_iff₀ hc]
      linarith
  · rw [key, lt_div_iff₀ hc]
    linarith

lemma exists_affine_minorant_gt (f : E → EReal) (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : ConvexEReal f) (x : E) (t : ℝ) (ht : (t : EReal) < f x) :
    ∃ v : E, ∃ β : ℝ, (∀ y, ((inner ℝ v y - β : ℝ) : EReal) ≤ f y) ∧ t < inner ℝ v x - β := by
  obtain ⟨hbot, x0, hx0⟩ := hp
  obtain ⟨r0, hfx0⟩ : ∃ r : ℝ, f x0 = (r : EReal) :=
    ⟨(f x0).toReal, (EReal.coe_toReal hx0.ne (hbot x0).ne').symm⟩
  -- a first affine minorant
  obtain ⟨v0, β0, hv0, -⟩ : ∃ v : E, ∃ β : ℝ, (∀ y, ((inner ℝ v y - β : ℝ) : EReal) ≤ f y) ∧
      r0 - 1 < inner ℝ v x0 - β := by
    have hnot : ¬ f x0 ≤ ((r0 - 1 : ℝ) : EReal) := by
      rw [hfx0, EReal.coe_le_coe_iff]; linarith
    obtain ⟨w', c', u', hc'0, hx', hb'⟩ := A_sep f hl hc x0 (r0 - 1) hnot x0 r0 hfx0.le
    rcases hc'0.lt_or_eq with hc'pos | hc'eq
    · exact A_pos f hbot x0 (r0 - 1) w' c' u' hc'pos hx' hb'
    · exfalso
      have := hb' x0 r0 hfx0.le
      rw [← hc'eq] at this hx'
      linarith
  have hnot : ¬ f x ≤ (t : EReal) := not_le.mpr ht
  obtain ⟨w, c, u, hc0, hx, hb⟩ := A_sep f hl hc x t hnot x0 r0 hfx0.le
  rcases hc0.lt_or_eq with hcpos | hceq
  · exact A_pos f hbot x t w c u hcpos hx hb
  · subst hceq
    simp only [zero_mul, add_zero] at hx hb
    have hgpos : 0 < u - inner ℝ w x := by linarith
    set a := inner ℝ v0 x - β0 with ha
    set g := u - inner ℝ w x with hg
    set lam := (|t - a| + 1) / g with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (by positivity) hgpos.le
    have hlamg : lam * g = |t - a| + 1 := by rw [hlam]; exact div_mul_cancel₀ _ hgpos.ne'
    refine ⟨v0 - lam • w, β0 - lam * u, ?_, ?_⟩
    · intro y
      have key : inner ℝ (v0 - lam • w) y - (β0 - lam * u)
          = (inner ℝ v0 y - β0) + lam * (u - inner ℝ w y) := by
        rw [inner_sub_left, real_inner_smul_left]; ring
      rw [key]
      by_cases htop : f y = ⊤
      · rw [htop]; exact le_top
      · obtain ⟨r, hr⟩ : ∃ r : ℝ, f y = (r : EReal) :=
          ⟨(f y).toReal, (EReal.coe_toReal htop (hbot y).ne').symm⟩
        have h1 := hb y r hr.le
        have h2 := hv0 y
        rw [hr, EReal.coe_le_coe_iff] at h2 ⊢
        have : lam * (u - inner ℝ w y) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlam0 (by linarith)
        linarith
    · have key : inner ℝ (v0 - lam • w) x - (β0 - lam * u) = a + lam * g := by
        rw [inner_sub_left, real_inner_smul_left, ha, hg]; ring
      rw [key, hlamg]
      have := le_abs_self (t - a)
      linarith

lemma conj_convex (f : E → EReal) : ConvexEReal (conjugate f) := by
  intro p hp q hq a b ha hb hab
  have hp' := (conj_le_iff f p.1 p.2).1 hp
  have hq' := (conj_le_iff f q.1 q.2).1 hq
  show conjugate f (a • p + b • q).1 ≤ (((a • p + b • q).2 : ℝ) : EReal)
  rw [conj_le_iff]
  intro x
  have h1 := hp' x
  have h2 := hq' x
  generalize f x = y at h1 h2 ⊢
  induction y using EReal.rec with
  | bot => exact absurd (le_bot_iff.1 h1) (EReal.coe_ne_bot _)
  | top => exact le_top
  | coe r =>
    rw [EReal.coe_le_coe_iff] at h1 h2 ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      inner_add_left, real_inner_smul_left]
    have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma conj_lsc (f : E → EReal) : LowerSemicontinuous (conjugate f) := by
  have key : ∀ x, LowerSemicontinuous (fun v : E => ((inner ℝ v x : ℝ) : EReal) - f x) := by
    intro x
    generalize f x = c
    induction c using EReal.rec with
    | bot =>
      have : (fun v : E => ((inner ℝ v x : ℝ) : EReal) - ⊥) = fun _ => ⊤ := by
        funext v; exact EReal.sub_bot (EReal.coe_ne_bot _)
      rw [this]; exact lowerSemicontinuous_const
    | top =>
      have : (fun v : E => ((inner ℝ v x : ℝ) : EReal) - ⊤) = fun _ => ⊥ := by
        funext v; exact EReal.sub_top _
      rw [this]; exact lowerSemicontinuous_const
    | coe r =>
      have : (fun v : E => ((inner ℝ v x : ℝ) : EReal) - (r : EReal))
          = fun v => ((inner ℝ v x - r : ℝ) : EReal) := by
        funext v; rw [EReal.coe_sub]
      rw [this]
      exact (continuous_coe_real_ereal.comp
        ((continuous_id.inner continuous_const).sub continuous_const)).lowerSemicontinuous
  have h : conjugate f = fun v => ⨆ x, (((inner ℝ v x : ℝ) : EReal) - f x) := by
    funext v
    simp only [conjugate, Set.image_univ, sSup_range]
  rw [h]
  exact lowerSemicontinuous_iSup key

lemma conj_proper (f : E → EReal) (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : ConvexEReal f) : IsProper (conjugate f) := by
  obtain ⟨hbot, x0, hx0⟩ := hp
  have hx0' : f x0 < ⊤ := hx0
  have hb0 := hbot x0
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, f x0 = r0 :=
    ⟨(f x0).toReal, (EReal.coe_toReal hx0'.ne hb0.ne').symm⟩
  constructor
  · intro v
    have : ((inner ℝ v x0 - r0 : ℝ) : EReal) ≤ conjugate f v := by
      apply le_sSup
      refine ⟨x0, Set.mem_univ _, ?_⟩
      simp only [hr0, EReal.coe_sub]
    exact lt_of_lt_of_le (EReal.bot_lt_coe _) this
  · obtain ⟨v, β, hvβ, -⟩ := exists_affine_minorant_gt f ⟨hbot, x0, hx0⟩ hl hc x0 (r0 - 1)
      (by rw [hr0]; exact EReal.coe_lt_coe_iff.2 (by linarith))
    refine ⟨v, ?_⟩
    show conjugate f v < ⊤
    exact lt_of_le_of_lt ((conj_le_iff f v β).2 hvβ) (EReal.coe_lt_top β)

lemma biconj_eq (f : E → EReal) (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : ConvexEReal f) : conjugate (conjugate f) = f := by
  funext x
  apply le_antisymm
  · have hb := hp.1 x
    generalize hy : f x = y at hb ⊢
    induction y using EReal.rec with
    | bot => exact absurd hb (lt_irrefl _)
    | top => exact le_top
    | coe r =>
      rw [conj_le_iff]
      intro v
      apply le_sSup
      refine ⟨x, Set.mem_univ _, ?_⟩
      simp only [hy, EReal.coe_sub, real_inner_comm]
  · apply le_of_forall_lt
    intro c hcx
    obtain ⟨t, hct, htf⟩ := EReal.lt_iff_exists_real_btwn.1 hcx
    obtain ⟨v, β, hvβ, htv⟩ := exists_affine_minorant_gt f hp hl hc x t htf
    have h1 : conjugate f v ≤ β := (conj_le_iff f v β).2 hvβ
    have h2 : ((inner ℝ x v : ℝ) : EReal) - conjugate f v ≤ conjugate (conjugate f) x :=
      le_sSup ⟨v, Set.mem_univ _, rfl⟩
    have h3 : ((inner ℝ x v - β : ℝ) : EReal) ≤ ((inner ℝ x v : ℝ) : EReal) - conjugate f v := by
      rw [EReal.coe_sub]
      exact EReal.sub_le_sub le_rfl h1
    calc c < t := hct
      _ < ((inner ℝ x v - β : ℝ) : EReal) := by
        rw [real_inner_comm]; exact_mod_cast htv
      _ ≤ _ := h3
      _ ≤ _ := h2

lemma bcond_extract (g : ℕ → E → EReal) (B : Set E)
    (h : Filter.limsup (fun ν => sInf ((fun x => g ν x) '' B)) Filter.atTop < ⊤) :
    ∃ a : ℝ, ∀ᶠ ν in Filter.atTop, ∃ x ∈ B, g ν x ≤ (a : EReal) := by
  obtain ⟨b, hb1, -⟩ := EReal.lt_iff_exists_real_btwn.1 h
  refine ⟨b, ?_⟩
  have hev : ∀ᶠ ν in Filter.atTop, sInf ((fun x => g ν x) '' B) < (b : EReal) :=
    Filter.eventually_lt_of_limsup_lt hb1 (by isBoundedDefault)
  filter_upwards [hev] with ν hν
  obtain ⟨y, ⟨x, hx, rfl⟩, hlt⟩ := sInf_lt_iff.1 hν
  exact ⟨x, hx, le_of_lt hlt⟩

lemma bcond_build (g : ℕ → E → EReal) (B : Set E) (a : ℝ)
    (h : ∀ᶠ ν in Filter.atTop, ∃ x ∈ B, g ν x ≤ (a : EReal)) :
    Filter.limsup (fun ν => sInf ((fun x => g ν x) '' B)) Filter.atTop < ⊤ := by
  have h1 : ∀ᶠ ν in Filter.atTop, sInf ((fun x => g ν x) '' B) ≤ (a : EReal) := by
    filter_upwards [h] with ν hν
    obtain ⟨x, hx, hgx⟩ := hν
    exact sInf_le_of_le (Set.mem_image_of_mem _ hx) hgx
  have h2 : Filter.limsup (fun ν => sInf ((fun x => g ν x) '' B)) Filter.atTop ≤ (a : EReal) :=
    Filter.limsup_le_of_le (by isBoundedDefault) h1
  exact lt_of_le_of_lt h2 (EReal.coe_lt_top a)

lemma bcond_of_subset (fseq : ℕ → E → EReal) (f : E → EReal) (hf : (effDom f).Nonempty)
    (h : epigraph f ⊆ epiLimsupSet fseq) :
    ∃ B : Set E, Bornology.IsBounded B ∧
        Filter.limsup (fun ν => sInf ((fun x => fseq ν x) '' B)) Filter.atTop < ⊤ := by
  obtain ⟨x0, hx0⟩ := hf
  obtain ⟨t, ht⟩ : ∃ t : ℝ, f x0 ≤ (t : EReal) := by
    obtain ⟨t, ht1, -⟩ := EReal.lt_iff_exists_real_btwn.1 hx0
    exact ⟨t, le_of_lt ht1⟩
  have hmem : ((x0, t) : E × ℝ) ∈ epiLimsupSet fseq := h ht
  have hV : Metric.ball ((x0, t) : E × ℝ) 1 ∈ 𝓝 ((x0, t) : E × ℝ) :=
    Metric.ball_mem_nhds _ one_pos
  have hev : ∀ᶠ n in Filter.atTop, ∃ p ∈ epigraph (fseq n), p ∈ Metric.ball ((x0, t) : E × ℝ) 1 :=
    hmem _ hV
  refine ⟨Metric.ball x0 1, Metric.isBounded_ball, ?_⟩
  apply bcond_build fseq (Metric.ball x0 1) (t + 1)
  filter_upwards [hev] with n hn
  obtain ⟨p, hp1, hp2⟩ := hn
  rw [Metric.mem_ball, Prod.dist_eq] at hp2
  have hd1 : dist p.1 x0 < 1 := lt_of_le_of_lt (le_max_left _ _) hp2
  have hd2 : dist p.2 t < 1 := lt_of_le_of_lt (le_max_right _ _) hp2
  rw [Real.dist_eq] at hd2
  have hp2t : p.2 ≤ t + 1 := by
    have := (abs_lt.1 hd2).2
    linarith
  refine ⟨p.1, Metric.mem_ball.2 hd1, ?_⟩
  have hp1' : fseq n p.1 ≤ (p.2 : EReal) := hp1
  calc fseq n p.1 ≤ (p.2 : EReal) := hp1'
    _ ≤ ((t + 1 : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hp2t

lemma H1 (fseq : ℕ → E → EReal) (f : E → EReal)
    (hconv : ∀ ν, ConvexEReal (fseq ν))
    (hB : ∃ B : Set E, Bornology.IsBounded B ∧
        Filter.limsup (fun ν => sInf ((fun x => fseq ν x) '' B)) Filter.atTop < ⊤)
    (h : epiLiminfSet fseq ⊆ epigraph f) :
    epigraph (conjugate f) ⊆ epiLimsupSet (fun ν => conjugate (fseq ν)) := by
  obtain ⟨B, hBb, hBl⟩ := hB
  obtain ⟨a, ha⟩ := bcond_extract fseq B hBl
  obtain ⟨r0, hr0⟩ := hBb.subset_closedBall 0
  set r := max r0 0 with hr_def
  have hr : 0 ≤ r := le_max_right _ _
  rintro ⟨v, β⟩ hvβ
  have hmin := (conj_le_iff f v β).1 hvβ
  intro V hV
  rw [nhds_prod_eq] at hV
  obtain ⟨U, hU, T, hT, hUT⟩ := Filter.mem_prod_iff.1 hV
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.1 hT
  set m : ℝ := -β - ε / 2 with hm_def
  set R : ℝ := 2 * r + 1 + |a + r * ‖v‖ - m| / δ with hR_def
  have hRr : 2 * r < R := by
    have : 0 ≤ |a + r * ‖v‖ - m| / δ := by positivity
    linarith
  set δ' : ℝ := (a + r * ‖v‖ - m) / (R - r) with hδ'_def
  have hδ'δ : δ' < δ := by
    have hRr' : 0 < R - r := by linarith
    rw [hδ'_def, div_lt_iff₀ hRr']
    have h1 : δ * (R - r) = δ * (r + 1) + |a + r * ‖v‖ - m| := by
      rw [hR_def]; field_simp; ring
    rw [h1]
    have : 0 < δ * (r + 1) := by positivity
    have := le_abs_self (a + r * ‖v‖ - m)
    linarith
  have hK : ∀ x ∈ Metric.closedBall (0 : E) R, (x, inner ℝ v x + m) ∉ epiLiminfSet fseq := by
    intro x _ hx
    have h1 : f x ≤ ((inner ℝ v x + m : ℝ) : EReal) := h hx
    have h2 := hmin x
    have h3 : ((inner ℝ v x - β : ℝ) : EReal) ≤ ((inner ℝ v x + m : ℝ) : EReal) := h2.trans h1
    rw [EReal.coe_le_coe_iff] at h3
    rw [hm_def] at h3
    linarith
  have hev := eventually_gt_on_compact fseq _ (isCompact_closedBall (0 : E) R)
    (fun x => inner ℝ v x + m) (by fun_prop) hK
  show ∀ᶠ n in Filter.atTop, ∃ p ∈ epigraph (conjugate (fseq n)), p ∈ V
  filter_upwards [ha, hev] with n ⟨x0, hx0B, hx0⟩ hn
  have hx0r : ‖x0‖ ≤ r := by
    have := hr0 hx0B
    rw [mem_closedBall_zero_iff] at this
    exact this.trans (le_max_left _ _)
  have hcone := cone_bound (fseq n) (hconv n) v x0 r R m a hr hRr hx0r hx0
    (fun x hx => (hn x (mem_closedBall_zero_iff.2 hx)).le)
  obtain ⟨w, hw, hwmin⟩ := dual_lemma (fseq n) (hconv n) v m (max δ' 0) (le_max_right _ _)
    (fun x => by
      refine le_trans ?_ (hcone x)
      rw [EReal.coe_le_coe_iff]
      have : δ' * ‖x‖ ≤ max δ' 0 * ‖x‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      linarith)
  refine ⟨(w, β + ε / 2), ?_, hUT ⟨hδU ?_, hεT ?_⟩⟩
  · show conjugate (fseq n) w ≤ ((β + ε / 2 : ℝ) : EReal)
    rw [conj_le_iff]
    intro x
    have := hwmin x
    have e : inner ℝ w x - (β + ε / 2) = inner ℝ w x + m := by rw [hm_def]; ring
    rw [e]; exact this
  · rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hw (max_lt hδ'δ hδ)
  · rw [Metric.mem_ball, Real.dist_eq]
    rw [show β + ε / 2 - β = ε / 2 by ring, abs_of_pos (by positivity)]
    linarith

lemma dual_cond (fseq : ℕ → E → EReal)
    (hconv : ∀ ν, ConvexEReal (fseq ν))
    (hnn : EpiSetNoNegInf (epiLiminfSet fseq))
    (hB : ∃ B : Set E, Bornology.IsBounded B ∧
        Filter.limsup (fun ν => sInf ((fun x => fseq ν x) '' B)) Filter.atTop < ⊤) :
    ∃ B : Set E, Bornology.IsBounded B ∧
        Filter.limsup (fun ν => sInf ((fun x => conjugate (fseq ν) x) '' B)) Filter.atTop < ⊤ := by
  obtain ⟨B, hBb, hBl⟩ := hB
  obtain ⟨a, ha⟩ := bcond_extract fseq B hBl
  obtain ⟨r0, hr0⟩ := hBb.subset_closedBall 0
  set r := max r0 0 with hr_def
  have hr : 0 ≤ r := le_max_right _ _
  set R : ℝ := 2 * r + 1 with hR_def
  have hRr : 2 * r < R := by linarith
  obtain ⟨m, hm⟩ := eventually_bdd_below_on_compact fseq (Metric.closedBall 0 R)
    (isCompact_closedBall 0 R) (fun x _ => by
      obtain ⟨k, hk⟩ := hnn x
      refine ⟨k - 1, fun hmem => ?_⟩
      have := hk (k - 1) ⟨(x, k - 1), hmem, rfl, rfl⟩
      linarith)
  set δ' : ℝ := (a + r * ‖(0 : E)‖ - m) / (R - r) with hδ'_def
  refine ⟨Metric.closedBall 0 (max δ' 0), Metric.isBounded_closedBall,
    bcond_build (fun ν => conjugate (fseq ν)) _ (-m) ?_⟩
  filter_upwards [ha, hm] with n ⟨x0, hx0B, hx0⟩ hmn
  have hx0r : ‖x0‖ ≤ r := by
    have := hr0 hx0B
    rw [mem_closedBall_zero_iff] at this
    exact this.trans (le_max_left _ _)
  have hcone := cone_bound (fseq n) (hconv n) 0 x0 r R m a hr hRr hx0r hx0
    (fun x hx => by
      have := (hmn x (mem_closedBall_zero_iff.2 hx)).le
      simpa using this)
  obtain ⟨w, hw, hwmin⟩ := dual_lemma (fseq n) (hconv n) 0 m (max δ' 0) (le_max_right _ _)
    (fun x => by
      refine le_trans ?_ (hcone x)
      rw [EReal.coe_le_coe_iff]
      have : δ' * ‖x‖ ≤ max δ' 0 * ‖x‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      linarith)
  refine ⟨w, by simpa using hw, ?_⟩
  show conjugate (fseq n) w ≤ ((-m : ℝ) : EReal)
  rw [conj_le_iff]
  intro x
  have := hwmin x
  rw [show inner ℝ w x - -m = inner ℝ w x + m by ring]
  exact this

lemma part1_fwd (fseq : ℕ → E → EReal) (f : E → EReal)
    (hconv : ∀ ν, ConvexEReal (fseq ν)) (hf : (effDom f).Nonempty)
    (h : EpiConverges fseq f) : EpiConverges (fun ν => conjugate (fseq ν)) (conjugate f) := by
  obtain ⟨h1, h2⟩ := h
  have hB := bcond_of_subset fseq f hf h2.symm.subset
  have hA : epiLiminfSet (fun ν => conjugate (fseq ν)) ⊆ epigraph (conjugate f) :=
    gen_ineq fseq f h2.symm.subset
  have hC : epigraph (conjugate f) ⊆ epiLimsupSet (fun ν => conjugate (fseq ν)) :=
    H1 fseq f hconv hB h1.subset
  have hD : epiLimsupSet (fun ν => conjugate (fseq ν)) ⊆
      epiLiminfSet (fun ν => conjugate (fseq ν)) := setLiminf_subset_setLimsup _
  exact ⟨subset_antisymm hA (hC.trans hD), subset_antisymm (hD.trans hA) hC⟩

theorem RW_chap_11_34
  (fseq : ℕ → E → EReal)
  (f : E → EReal)
  (hfseq_proper : ∀ (ν : ℕ), IsProper (fseq ν))
  (hfseq_lsc : ∀ (ν : ℕ), LowerSemicontinuous (fseq ν))
  (hfseq_convex : ∀ (ν : ℕ), ConvexEReal (fseq ν))
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f)
  (hf_convex : ConvexEReal f) :
  (EpiConverges fseq f ↔
    EpiConverges
      (fun (ν : ℕ) => conjugate (fseq ν))
      (conjugate f)) ∧
  ((EpiSetNoNegInf (epiLiminfSet fseq) ∧
      (∃ (B : Set E), Bornology.IsBounded B ∧
        Filter.limsup
          (fun (ν : ℕ) => sInf ((fun (x : E) => fseq ν x) '' B))
          Filter.atTop < ⊤)) →
    ((epiLiminfSet fseq ⊆ epigraph f) ↔
      (epigraph (conjugate f) ⊆
        epiLimsupSet (fun (ν : ℕ) => conjugate (fseq ν)))) ∧
    ((epigraph f ⊆ epiLimsupSet fseq) ↔
      (epiLiminfSet (fun (ν : ℕ) => conjugate (fseq ν)) ⊆
        epigraph (conjugate f)))) := by
  have hcc : ∀ ν, ConvexEReal (conjugate (fseq ν)) := fun ν => conj_convex _
  have hseq : (fun ν => conjugate (conjugate (fseq ν))) = fseq :=
    funext fun ν => biconj_eq _ (hfseq_proper ν) (hfseq_lsc ν) (hfseq_convex ν)
  have hbicf : conjugate (conjugate f) = f := biconj_eq f hf_proper hf_lsc hf_convex
  have hfcp : IsProper (conjugate f) := conj_proper f hf_proper hf_lsc hf_convex
  refine ⟨⟨part1_fwd fseq f hfseq_convex hf_proper.2, fun h => ?_⟩,
    fun ⟨hnn, hB⟩ => ⟨⟨H1 fseq f hfseq_convex hB, fun h => ?_⟩, ⟨gen_ineq fseq f, fun h => ?_⟩⟩⟩
  · have := part1_fwd (fun ν => conjugate (fseq ν)) (conjugate f) hcc hfcp.2 h
    rw [hseq, hbicf] at this
    exact this
  · have := gen_ineq (fun ν => conjugate (fseq ν)) (conjugate f) h
    rw [hseq, hbicf] at this
    exact this
  · have := H1 (fun ν => conjugate (fseq ν)) (conjugate f) hcc (dual_cond fseq hfseq_convex hnn hB) h
    rw [hseq, hbicf] at this
    exact this

end RW_chap_11_34
