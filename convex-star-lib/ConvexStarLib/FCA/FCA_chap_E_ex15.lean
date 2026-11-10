import ConvexStarLib.Defs

/-!
# `FCA_chap_E_ex15`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_ex15` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_ex15`, so the main result is `FCA_chap_E_ex15.FCA_chap_E_ex15`.
-/

namespace FCA_chap_E_ex15

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_ex15
  (f g : E → EReal)
  (hf : InClosedConvRn f)
  (hg : InClosedConvRn g)
  (hf_proper : (effDom f).Nonempty)
  (hg_proper : (effDom g).Nonempty)
  (f_ne_bot : ∀ x, ⊥ < f x)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  (∀ (s : E),
    (conjugate f s + conjugate g (-s) ≤ 0) ↔
    (∃ (r : ℝ), ∀ x, (r + inner ℝ s x ≤ f x) ∧
                      ((r + inner ℝ s x) ≥ -1 * (g x)))) ∧
  (∀ (x' : E),
    ((f x') = -1 * (g x')) →
    {s | conjugate f s + conjugate g (-s) ≤ 0} =
      (convexSubdifferential f x') ∩
      {s | -s ∈ convexSubdifferential g x'}) := by
  have hcase : ∀ (h : E → EReal), (∀ x, ⊥ < h x) → ∀ x, h x = ⊤ ∨ ∃ b : ℝ, h x = (b : EReal) := by
    intro h hb x
    rcases eq_or_ne (h x) ⊤ with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨(h x).toReal, (EReal.coe_toReal hx (hb x).ne').symm⟩
  have conj_le : ∀ (h : E → EReal) (v : E) (c : EReal),
      conjugate h v ≤ c ↔ ∀ x, ((inner ℝ v x : ℝ) : EReal) - h x ≤ c := by
    intro h v c
    unfold conjugate
    rw [sSup_le_iff]
    simp
  have le_conj : ∀ (h : E → EReal) (v x : E),
      ((inner ℝ v x : ℝ) : EReal) - h x ≤ conjugate h v := by
    intro h v x
    exact (conj_le h v _).1 le_rfl x
  have neg_one_mul' : ∀ a : EReal, (-1 : EReal) * a = -a := by
    intro a
    rw [EReal.neg_mul, one_mul]
  have conj_ne_bot : ∀ (h : E → EReal), (∀ x, ⊥ < h x) → (effDom h).Nonempty →
      ∀ v, conjugate h v ≠ ⊥ := by
    intro h hb hne v
    obtain ⟨x0, hx0⟩ := hne
    rcases hcase h hb x0 with h0 | ⟨b, h0⟩
    · exact absurd h0 (ne_of_lt hx0)
    · have := le_conj h v x0
      rw [h0, ← EReal.coe_sub] at this
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) this
  have conj_real : ∀ s, conjugate f s + conjugate g (-s) ≤ 0 →
      ∃ a c : ℝ, conjugate f s = a ∧ conjugate g (-s) = c ∧ a + c ≤ 0 := by
    intro s hs
    have hfb : conjugate f s ≠ ⊥ := conj_ne_bot f f_ne_bot hf_proper s
    have hgb : conjugate g (-s) ≠ ⊥ := conj_ne_bot g g_ne_bot hg_proper (-s)
    have hft : conjugate f s ≠ ⊤ := by
      intro ht
      rw [ht, EReal.top_add_of_ne_bot hgb] at hs
      exact absurd hs (by simp)
    have hgt : conjugate g (-s) ≠ ⊤ := by
      intro ht
      rw [ht, EReal.add_top_of_ne_bot hfb] at hs
      exact absurd hs (by simp)
    refine ⟨(conjugate f s).toReal, (conjugate g (-s)).toReal,
      (EReal.coe_toReal hft hfb).symm, (EReal.coe_toReal hgt hgb).symm, ?_⟩
    have : ((conjugate f s).toReal : EReal) + ((conjugate g (-s)).toReal : EReal) ≤ 0 := by
      rw [EReal.coe_toReal hft hfb, EReal.coe_toReal hgt hgb]; exact hs
    exact_mod_cast this
  constructor
  · intro s
    constructor
    · intro hs
      obtain ⟨a, c, ha, hc, hac⟩ := conj_real s hs
      refine ⟨-a, fun x => ⟨?_, ?_⟩⟩
      · have h1 := le_conj f s x
        rw [ha] at h1
        rcases hcase f f_ne_bot x with hx | ⟨b, hx⟩
        · rw [hx]; exact le_top
        · rw [hx] at h1 ⊢
          rw [← EReal.coe_sub] at h1
          rw [← EReal.coe_add]
          have := EReal.coe_le_coe_iff.1 h1
          exact EReal.coe_le_coe_iff.2 (by linarith)
      · have h1 := le_conj g (-s) x
        rw [hc] at h1
        rw [neg_one_mul']
        rcases hcase g g_ne_bot x with hx | ⟨b, hx⟩
        · rw [hx]; simp
        · rw [hx] at h1 ⊢
          rw [← EReal.coe_sub] at h1
          rw [← EReal.coe_add, ← EReal.coe_neg]
          have := EReal.coe_le_coe_iff.1 h1
          rw [inner_neg_left] at this
          exact EReal.coe_le_coe_iff.2 (by linarith)
    · rintro ⟨r, hr⟩
      have h1 : conjugate f s ≤ ((-r : ℝ) : EReal) := by
        rw [conj_le]
        intro x
        obtain ⟨hx1, _⟩ := hr x
        rcases hcase f f_ne_bot x with hx | ⟨b, hx⟩
        · rw [hx, EReal.sub_top]; exact bot_le
        · rw [hx] at hx1 ⊢
          rw [← EReal.coe_sub]
          rw [← EReal.coe_add] at hx1
          have := EReal.coe_le_coe_iff.1 hx1
          exact EReal.coe_le_coe_iff.2 (by linarith)
      have h2 : conjugate g (-s) ≤ ((r : ℝ) : EReal) := by
        rw [conj_le]
        intro x
        obtain ⟨_, hx2⟩ := hr x
        rw [neg_one_mul'] at hx2
        rcases hcase g g_ne_bot x with hx | ⟨b, hx⟩
        · rw [hx, EReal.sub_top]; exact bot_le
        · rw [hx] at hx2 ⊢
          rw [← EReal.coe_sub]
          rw [← EReal.coe_add, ← EReal.coe_neg] at hx2
          have := EReal.coe_le_coe_iff.1 hx2
          rw [inner_neg_left]
          exact EReal.coe_le_coe_iff.2 (by linarith)
      calc conjugate f s + conjugate g (-s) ≤ ((-r : ℝ) : EReal) + ((r : ℝ) : EReal) :=
            add_le_add h1 h2
        _ = 0 := by rw [← EReal.coe_add]; simp
  · intro x' hx'
    rw [neg_one_mul'] at hx'
    obtain ⟨p, hp⟩ : ∃ p : ℝ, f x' = p := by
      rcases hcase f f_ne_bot x' with h | h
      · exfalso
        rw [h] at hx'
        have : g x' = ⊥ := by
          rw [← neg_neg (g x'), ← hx']
          rfl
        exact (g_ne_bot x').ne' this
      · exact h
    have hq : g x' = ((-p : ℝ) : EReal) := by
      rw [hp] at hx'
      rw [EReal.coe_neg, hx', neg_neg]
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, convexSubdifferential]
    constructor
    · intro hs
      obtain ⟨a, c, ha, hc, hac⟩ := conj_real s hs
      have h1 := le_conj f s x'
      have h2 := le_conj g (-s) x'
      rw [ha, hp, ← EReal.coe_sub] at h1
      rw [hc, hq, ← EReal.coe_sub] at h2
      have h1' := EReal.coe_le_coe_iff.1 h1
      have h2' := EReal.coe_le_coe_iff.1 h2
      rw [inner_neg_left] at h2'
      constructor
      · intro y
        have h3 := le_conj f s y
        rw [ha] at h3
        rcases hcase f f_ne_bot y with hy | ⟨b, hy⟩
        · rw [hy]; exact le_top
        · rw [hy] at h3 ⊢
          rw [hp, ← EReal.coe_add]
          rw [← EReal.coe_sub] at h3
          have := EReal.coe_le_coe_iff.1 h3
          rw [inner_sub_right]
          exact EReal.coe_le_coe_iff.2 (by linarith)
      · intro y
        have h3 := le_conj g (-s) y
        rw [hc] at h3
        rcases hcase g g_ne_bot y with hy | ⟨b, hy⟩
        · rw [hy]; exact le_top
        · rw [hy] at h3 ⊢
          rw [hq, ← EReal.coe_add]
          rw [← EReal.coe_sub] at h3
          have := EReal.coe_le_coe_iff.1 h3
          rw [inner_neg_left] at this
          rw [inner_sub_right, inner_neg_left, inner_neg_left]
          exact EReal.coe_le_coe_iff.2 (by linarith)
    · rintro ⟨hs1, hs2⟩
      have h1 : conjugate f s ≤ ((inner ℝ s x' - p : ℝ) : EReal) := by
        rw [conj_le]
        intro y
        have := hs1 y
        rcases hcase f f_ne_bot y with hy | ⟨b, hy⟩
        · rw [hy, EReal.sub_top]; exact bot_le
        · rw [hy, hp, ← EReal.coe_add] at this
          rw [hy, ← EReal.coe_sub]
          have := EReal.coe_le_coe_iff.1 this
          rw [inner_sub_right] at this
          exact EReal.coe_le_coe_iff.2 (by linarith)
      have h2 : conjugate g (-s) ≤ ((-inner ℝ s x' + p : ℝ) : EReal) := by
        rw [conj_le]
        intro y
        have := hs2 y
        rcases hcase g g_ne_bot y with hy | ⟨b, hy⟩
        · rw [hy, EReal.sub_top]; exact bot_le
        · rw [hy, hq, ← EReal.coe_add] at this
          rw [hy, ← EReal.coe_sub]
          have := EReal.coe_le_coe_iff.1 this
          rw [inner_sub_right, inner_neg_left, inner_neg_left] at this
          rw [inner_neg_left]
          exact EReal.coe_le_coe_iff.2 (by linarith)
      calc conjugate f s + conjugate g (-s)
          ≤ ((inner ℝ s x' - p : ℝ) : EReal) + ((-inner ℝ s x' + p : ℝ) : EReal) :=
            add_le_add h1 h2
        _ = 0 := by rw [← EReal.coe_add]; ring_nf; simp

end FCA_chap_E_ex15
