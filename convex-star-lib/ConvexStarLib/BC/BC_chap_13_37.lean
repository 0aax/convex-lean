import ConvexStarLib.Defs

/-!
# `BC_chap_13_37`

Source: Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces.

Statement from the `convex-eval-v28-2h/BC_chap_13_37` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace BC_chap_13_37`, so the main result is `BC_chap_13_37.BC_chap_13_37`.
-/

namespace BC_chap_13_37

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma BC_sub_le_iff (a c : ℝ) (y : EReal) :
    (a : EReal) - y ≤ (c : EReal) ↔ ((a - c : ℝ) : EReal) ≤ y := by
  induction y using EReal.rec with
  | bot =>
    rw [EReal.coe_sub_bot]
    simp only [top_le_iff, le_bot_iff, EReal.coe_ne_top, EReal.coe_ne_bot]
  | top => simp [EReal.sub_top]
  | coe b =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

omit [CompleteSpace E] in
lemma BC_conj_le_iff (f : E → EReal) (v : E) (c : ℝ) :
    conjugate f v ≤ (c : EReal) ↔ ∀ x, ((inner ℝ v x - c : ℝ) : EReal) ≤ f x := by
  unfold conjugate
  rw [sSup_le_iff]
  simp only [Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact forall_congr' fun x => BC_sub_le_iff _ _ _

omit [CompleteSpace E] in
lemma BC_le_conj (f : E → EReal) (v x : E) :
    ((inner ℝ v x : ℝ) : EReal) - f x ≤ conjugate f v :=
  le_sSup ⟨x, Set.mem_univ _, rfl⟩

lemma BC_ereal_aux (a : ℝ) (y z : EReal) (h : (a : EReal) - y ≤ z) : (a : EReal) - z ≤ y := by
  induction y using EReal.rec with
  | top => exact le_top
  | bot =>
    rw [EReal.coe_sub_bot, top_le_iff] at h
    rw [h, EReal.sub_top]
  | coe b =>
    induction z using EReal.rec with
    | top => rw [EReal.sub_top]; exact bot_le
    | bot =>
      rw [← EReal.coe_sub, le_bot_iff] at h
      exact absurd h (EReal.coe_ne_bot _)
    | coe d =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h ⊢
      linarith

omit [CompleteSpace E] in
lemma BC_biconj_le (f : E → EReal) (u : E) : biconjugate f u ≤ f u := by
  unfold biconjugate
  apply sSup_le
  rintro _ ⟨v, -, rfl⟩
  have h1 := BC_le_conj f v u
  rw [real_inner_comm] at h1
  exact BC_ereal_aux _ _ _ h1

omit [CompleteSpace E] in
lemma BC_conj_lsc (g : E → EReal) : LowerSemicontinuous (conjugate g) := by
  have h : conjugate g = fun v => ⨆ x, (((inner ℝ v x : ℝ) : EReal) - g x) := by
    funext v
    unfold conjugate
    rw [Set.image_univ, sSup_range]
  rw [h]
  apply lowerSemicontinuous_iSup
  intro x
  generalize g x = c
  induction c using EReal.rec with
  | bot => simp only [EReal.coe_sub_bot]; exact lowerSemicontinuous_const
  | top => simp only [EReal.sub_top]; exact lowerSemicontinuous_const
  | coe c =>
    apply Continuous.lowerSemicontinuous
    simp_rw [← EReal.coe_sub]
    exact continuous_coe_real_ereal.comp ((continuous_id.inner continuous_const).sub continuous_const)

omit [CompleteSpace E] in
lemma BC_conj_convex (g : E → EReal) : ConvexEReal (conjugate g) := by
  unfold ConvexEReal epigraph
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_setOf_eq] at hp hq ⊢
  rw [BC_conj_le_iff] at hp hq ⊢
  intro x
  have h1 := hp x
  have h2 := hq x
  set A := inner ℝ p.1 x - p.2
  set B := inner ℝ q.1 x - q.2
  have hM : ((max A B : ℝ) : EReal) ≤ g x := by
    rcases le_total A B with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  refine le_trans ?_ hM
  rw [EReal.coe_le_coe_iff]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    inner_add_left, real_inner_smul_left]
  have hA : A ≤ max A B := le_max_left _ _
  have hB : B ≤ max A B := le_max_right _ _
  have e : a * max A B + b * max A B = max A B := by rw [← add_mul, hab, one_mul]
  have h3 := mul_le_mul_of_nonneg_left hA ha
  have h4 := mul_le_mul_of_nonneg_left hB hb
  simp only [A, B] at h3 h4 e ⊢
  nlinarith

lemma BC_sep (f : E → EReal) (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    (hconv : ConvexEReal f) (u : E) (α : ℝ) (hα : (α : EReal) < f u) :
    ∃ (w : E) (s c : ℝ), s ≤ 0 ∧ (∀ x (y : ℝ), f x ≤ y → inner ℝ w x + y * s < c) ∧
      c < inner ℝ w u + α * s := by
  have hclosed : IsClosed (epigraph f) := by
    have := hlsc.isClosed_epigraph
    exact this.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  have hnot : (u, α) ∉ epigraph f := by
    simp only [epigraph, Set.mem_setOf_eq, not_le]; exact hα
  obtain ⟨L, c, hL, hc⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
  set phi : StrongDual ℝ E := L.comp (ContinuousLinearMap.inl ℝ E ℝ) with hphi
  set w := (InnerProductSpace.toDual ℝ E).symm phi with hw
  set s := L ((0 : E), (1 : ℝ)) with hs
  have hdec : ∀ (x : E) (r : ℝ), L (x, r) = inner ℝ w x + r * s := by
    intro x r
    have e : (x, r) = (x, (0:ℝ)) + r • ((0:E), (1:ℝ)) := by ext <;> simp
    rw [e, map_add, map_smul, hw, InnerProductSpace.toDual_symm_apply]
    simp [phi, smul_eq_mul, hs]
  have hsep : ∀ x (y : ℝ), f x ≤ y → inner ℝ w x + y * s < c := by
    intro x y hxy
    rw [← hdec]
    exact hL (x, y) hxy
  refine ⟨w, s, c, ?_, hsep, by rw [← hdec]; exact hc⟩
  obtain ⟨x1, hx1⟩ := hf.2
  have hx1' : f x1 < ⊤ := hx1
  by_contra hpos
  push_neg at hpos
  set y1 := (f x1).toReal
  have hy1 : f x1 ≤ y1 := EReal.le_coe_toReal hx1'.ne
  set r := max y1 ((c - inner ℝ w x1) / s)
  have hr : f x1 ≤ r := hy1.trans (EReal.coe_le_coe_iff.2 (le_max_left _ _))
  have h1 := hsep x1 r hr
  have h2 : (c - inner ℝ w x1) / s * s ≤ r * s :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le
  rw [div_mul_cancel₀ _ hpos.ne'] at h2
  linarith

omit [CompleteSpace E] in
lemma BC_case_neg (f : E → EReal) (w : E) (s c : ℝ) (hs : s < 0)
    (hsep : ∀ x (y : ℝ), f x ≤ y → inner ℝ w x + y * s < c) :
    ∀ x, ((inner ℝ ((1 / (-s)) • w) x - c / (-s) : ℝ) : EReal) ≤ f x := by
  intro x
  by_contra h
  push_neg at h
  obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.1 h
  have h3 := hsep x y hy1.le
  rw [EReal.coe_lt_coe_iff, real_inner_smul_left, one_div_mul_eq_div, div_sub_div_same,
    lt_div_iff₀ (neg_pos.2 hs)] at hy2
  nlinarith

lemma BC_minorant (f : E → EReal) (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    (hconv : ConvexEReal f) :
    ∃ (v : E) (c : ℝ), ∀ x, ((inner ℝ v x - c : ℝ) : EReal) ≤ f x := by
  obtain ⟨x1, hx1⟩ := hf.2
  have hx1' : f x1 < ⊤ := hx1
  set y1 := (f x1).toReal
  have hy1 : f x1 = y1 := (EReal.coe_toReal hx1'.ne (hf.1 x1).ne').symm
  have hα : ((y1 - 1 : ℝ) : EReal) < f x1 := by
    rw [hy1, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨w, s, c, hs, hsep, hc⟩ := BC_sep f hf hlsc hconv x1 (y1 - 1) hα
  rcases hs.lt_or_eq with hs | hs
  · exact ⟨_, _, BC_case_neg f w s c hs hsep⟩
  · exfalso
    subst hs
    have := hsep x1 y1 hy1.le
    simp only [mul_zero, add_zero] at this hc
    linarith

lemma BC_key (f : E → EReal) (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    (hconv : ConvexEReal f) (u : E) (α : ℝ) (hα : (α : EReal) < f u) :
    ∃ (v : E) (c : ℝ), (∀ x, ((inner ℝ v x - c : ℝ) : EReal) ≤ f x) ∧
      α < inner ℝ u v - c := by
  obtain ⟨w, s, c, hs, hsep, hc⟩ := BC_sep f hf hlsc hconv u α hα
  rcases hs.lt_or_eq with hs | hs
  · refine ⟨(1 / (-s)) • w, c / (-s), BC_case_neg f w s c hs hsep, ?_⟩
    rw [real_inner_smul_right, real_inner_comm w u, one_div_mul_eq_div, div_sub_div_same,
      lt_div_iff₀ (neg_pos.2 hs)]
    nlinarith
  · subst hs
    obtain ⟨v0, c0, hv0⟩ := BC_minorant f hf hlsc hconv
    simp only [mul_zero, add_zero] at hc hsep
    set D := inner ℝ w u - c with hD_def
    have hD : 0 < D := by rw [hD_def]; linarith
    set t := (|α - (inner ℝ u v0 - c0)| + 1) / D with ht_def
    have ht : 0 ≤ t := div_nonneg (by positivity) hD.le
    have htD : t * D = |α - (inner ℝ u v0 - c0)| + 1 := by
      rw [ht_def, div_mul_cancel₀ _ hD.ne']
    refine ⟨v0 + t • w, c0 + t * c, ?_, ?_⟩
    · intro x
      by_cases hx : f x = ⊤
      · rw [hx]; exact le_top
      · have h1 := hsep x (f x).toReal (EReal.le_coe_toReal hx)
        have h2 := hv0 x
        refine le_trans ?_ h2
        rw [EReal.coe_le_coe_iff, inner_add_left, real_inner_smul_left]
        nlinarith
    · rw [inner_add_right, real_inner_smul_right, real_inner_comm w u]
      have := le_abs_self (α - (inner ℝ u v0 - c0))
      have e : inner ℝ u v0 + t * inner ℝ w u - (c0 + t * c) = (inner ℝ u v0 - c0) + t * D := by
        rw [hD_def]; ring
      rw [e, htD]
      linarith

lemma BC_le_biconj (f : E → EReal) (hf : IsProper f) (hlsc : LowerSemicontinuous f)
    (hconv : ConvexEReal f) (u : E) : f u ≤ biconjugate f u := by
  by_contra h
  push_neg at h
  obtain ⟨α, hα1, hα2⟩ := EReal.lt_iff_exists_real_btwn.1 h
  obtain ⟨v, c, hvc, hlt⟩ := BC_key f hf hlsc hconv u α hα2
  have h1 : conjugate f v ≤ c := (BC_conj_le_iff f v c).2 hvc
  have h2 : ((inner ℝ u v : ℝ) : EReal) - conjugate f v ≤ biconjugate f u :=
    BC_le_conj (conjugate f) u v
  have h3 : ((inner ℝ u v - c : ℝ) : EReal) ≤ ((inner ℝ u v : ℝ) : EReal) - conjugate f v := by
    rw [EReal.coe_sub]; exact EReal.sub_le_sub le_rfl h1
  have h4 : (α : EReal) < biconjugate f u :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlt) (h3.trans h2)
  exact lt_asymm hα1 h4

theorem BC_chap_13_37
  (f : E → EReal)
  (hf_proper : IsProper f) :
  ((LowerSemicontinuous f ∧ ConvexEReal f) ↔
    (f = biconjugate f)) ∧
  ((LowerSemicontinuous f ∧ ConvexEReal f) →
    IsProper (conjugate f)) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · funext u
    exact le_antisymm (BC_le_biconj f hf_proper h.1 h.2 u) (BC_biconj_le f u)
  · rw [h]
    exact ⟨BC_conj_lsc _, BC_conj_convex _⟩
  · refine ⟨fun v => ?_, ?_⟩
    · obtain ⟨x1, hx1⟩ := hf_proper.2
      have hx1' : f x1 < ⊤ := hx1
      have hy1 : f x1 = ((f x1).toReal : EReal) :=
        (EReal.coe_toReal hx1'.ne (hf_proper.1 x1).ne').symm
      have := BC_le_conj f v x1
      rw [hy1, ← EReal.coe_sub] at this
      exact lt_of_lt_of_le (EReal.bot_lt_coe _) this
    · obtain ⟨v, c, hvc⟩ := BC_minorant f hf_proper h.1 h.2
      exact ⟨v, lt_of_le_of_lt ((BC_conj_le_iff f v c).2 hvc) (EReal.coe_lt_top c)⟩

end BC_chap_13_37
