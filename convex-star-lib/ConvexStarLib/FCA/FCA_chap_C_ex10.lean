import ConvexStarLib.Defs

/-!
# `FCA_chap_C_ex10`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_ex10` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_ex10`, so the main result is `FCA_chap_C_ex10.FCA_chap_C_ex10`.
-/

namespace FCA_chap_C_ex10

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_ex10
  [Nontrivial E]
  (f : E → EReal)
  (A : Set E)
  (hf_minorized : ∃ (s : E) (b : ℝ),
    ∀ x, (inner ℝ s x + b : ℝ) ≤ f x)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let fA := fun x => f x + setIndicator A x
  let clco_f := lscHull ((convexHullFun f))
  (closure (convexHull ℝ (epigraph fA)) ⊆
    {p | (p.1 ∈ closure (convexHull ℝ A)) ∧ (clco_f p.1 ≤ p.2)}) ∧
  (∃ (f' : E → EReal)
      (A' : Set E),
      (IsClosed A') ∧ (Convex ℝ A') ∧
      (∃ (s' : E) (b' : ℝ),
        ∀ x, (inner ℝ s' x + b' : ℝ) ≤ f' x) ∧
      let fA' := fun x => f' x + setIndicator A' x
      let clco_f' := lscHull ((convexHullFun f'))
      closure (convexHull ℝ (epigraph fA')) ≠
        {p | (p.1 ∈ closure (convexHull ℝ A')) ∧ (clco_f' p.1 ≤ p.2)}) ∧
  (∀ (a : E) (b : ℝ),
    let f_aff : E → EReal := fun x => (inner ℝ a x + b : ℝ)
    let fA_aff := fun x => f_aff x + setIndicator A x
    let clco_f_aff := lscHull ((convexHullFun f_aff))
    closure (convexHull ℝ (epigraph fA_aff)) =
      {p | (p.1 ∈ closure (convexHull ℝ A)) ∧ (clco_f_aff p.1 ≤ p.2)}) := by
  intro fA clco_f
  have lscHull_le_self : ∀ (g : E → EReal) (x : E), lscHull g x ≤ g x := by
    intro g x
    unfold lscHull
    exact Filter.liminf_le_of_le (by isBoundedDefault) (fun _ ha => ha.self_of_nhds)
  have isClosed_epi_lscHull : ∀ (g : E → EReal), IsClosed (epigraph (lscHull g)) := by
    intro g
    have hlsc : LowerSemicontinuous (lscHull g) := by
      intro x y hy
      unfold lscHull at hy
      rw [Filter.liminf_eq] at hy
      obtain ⟨a, ha, hya⟩ := lt_sSup_iff.mp hy
      have ha' : ∀ᶠ z in 𝓝 x, a ≤ g z := ha
      filter_upwards [ha'.eventually_nhds] with x' hx'
      exact hya.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) hx')
    have hc : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact hlsc.isClosed_epigraph.preimage hc
  have part1 : ∀ (g : E → EReal), (∀ x, ⊥ < g x) →
      closure (convexHull ℝ (epigraph (fun x => g x + setIndicator A x))) ⊆
        {p | (p.1 ∈ closure (convexHull ℝ A)) ∧ (lscHull (convexHullFun g) p.1 ≤ p.2)} := by
    intro g g_ne_bot
    have hepi : epigraph (fun x => g x + setIndicator A x) ⊆ epigraph g ∩ (A ×ˢ Set.univ) := by
      intro p hp
      simp only [epigraph, Set.mem_setOf_eq] at hp
      by_cases hA : p.1 ∈ A
      · simp only [setIndicator, hA, if_true, add_zero] at hp
        exact ⟨hp, hA, Set.mem_univ _⟩
      · simp only [setIndicator, hA, if_false] at hp
        rw [EReal.add_top_of_ne_bot (g_ne_bot p.1).ne'] at hp
        exact absurd hp (by simp)
    intro p hp
    constructor
    · have h1 : closure (convexHull ℝ (epigraph (fun x => g x + setIndicator A x))) ⊆
          closure (convexHull ℝ A) ×ˢ Set.univ := by
        refine closure_minimal ?_ (isClosed_closure.prod isClosed_univ)
        refine convexHull_min ?_ ((convex_convexHull ℝ A).closure.prod convex_univ)
        intro q hq
        exact ⟨subset_closure (subset_convexHull ℝ A (hepi hq).2.1), Set.mem_univ _⟩
      exact (h1 hp).1
    · have h2 : convexHull ℝ (epigraph g) ⊆ epigraph (convexHullFun g) := by
        intro q hq
        show sInf ((fun r : ℝ => (r : EReal)) '' _) ≤ _
        apply sInf_le
        exact ⟨q.2, hq, rfl⟩
      have h3 : epigraph (convexHullFun g) ⊆ epigraph (lscHull (convexHullFun g)) := by
        intro q hq
        exact le_trans (lscHull_le_self _ q.1) hq
      have h4 : closure (convexHull ℝ (epigraph (fun x => g x + setIndicator A x))) ⊆
          epigraph (lscHull (convexHullFun g)) := by
        refine closure_minimal ?_ (isClosed_epi_lscHull _)
        exact (convexHull_mono (fun q hq => (hepi hq).1)).trans (h2.trans h3)
      exact h4 hp
  refine ⟨part1 f f_ne_bot, ?_, ?_⟩
  · -- counterexample
    classical
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    refine ⟨fun x => if x = 0 then 1 else 0, {0}, isClosed_singleton, convex_singleton 0,
      ⟨0, 0, ?_⟩, ?_⟩
    · intro x
      simp only [inner_zero_left, add_zero, EReal.coe_zero]
      split_ifs <;> simp
    · intro fA' clco_f' heq
      have hmem : ((0 : E), (0 : ℝ)) ∈
          {p : E × ℝ | p.1 ∈ closure (convexHull ℝ {0}) ∧ clco_f' p.1 ≤ p.2} := by
        constructor
        · exact subset_closure (subset_convexHull ℝ _ rfl)
        · refine le_trans (lscHull_le_self _ _) ?_
          show sInf ((fun r : ℝ => (r : EReal)) '' _) ≤ _
          apply sInf_le
          refine ⟨0, ?_, rfl⟩
          show ((0:E), (0:ℝ)) ∈ convexHull ℝ (epigraph _)
          have h1 : ((v, (0:ℝ)) : E × ℝ) ∈
              convexHull ℝ (epigraph (fun x : E => if x = 0 then (1 : EReal) else 0)) :=
            subset_convexHull ℝ _ (by simp [epigraph, hv])
          have h2 : ((-v, (0:ℝ)) : E × ℝ) ∈
              convexHull ℝ (epigraph (fun x : E => if x = 0 then (1 : EReal) else 0)) :=
            subset_convexHull ℝ _ (by simp [epigraph, hv])
          have := convex_convexHull ℝ _ h1 h2 (by norm_num : (0:ℝ) ≤ 1/2)
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
          convert this using 1
          ext <;> simp
      rw [← heq] at hmem
      have hsub : closure (convexHull ℝ (epigraph fA')) ⊆ Set.univ ×ˢ Set.Ici (1:ℝ) := by
        refine closure_minimal ?_ (isClosed_univ.prod isClosed_Ici)
        refine convexHull_min ?_ (convex_univ.prod (convex_Ici 1))
        intro p hp
        refine ⟨Set.mem_univ _, ?_⟩
        simp only [epigraph, Set.mem_setOf_eq, fA', setIndicator] at hp
        by_cases h0 : p.1 = 0
        · simp only [h0, if_true, add_zero, Set.mem_singleton_iff] at hp
          exact EReal.coe_le_coe_iff.mp (by simpa using hp)
        · simp [h0] at hp
      have := (hsub hmem).2
      norm_num at this
  · intro a b f_aff fA_aff clco_f_aff
    apply Set.Subset.antisymm
    · exact part1 f_aff (fun x => EReal.bot_lt_coe _)
    · rintro ⟨x, r⟩ ⟨hx, hr⟩
      have hconv_sub : convexHull ℝ (epigraph f_aff) ⊆
          {p : E × ℝ | inner ℝ a p.1 + b ≤ p.2} := by
        apply convexHull_min
        · intro p hp
          exact EReal.coe_le_coe_iff.mp hp
        · intro p hp q hq s t hs ht hst
          simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
            smul_eq_mul, inner_add_right, inner_smul_right] at hp hq ⊢
          obtain rfl : t = 1 - s := by linarith
          have h1 := mul_le_mul_of_nonneg_left hp hs
          have h2 := mul_le_mul_of_nonneg_left hq ht
          nlinarith
      have hlow : ∀ y, ((inner ℝ a y + b : ℝ) : EReal) ≤ convexHullFun f_aff y := by
        intro y
        apply le_sInf
        rintro _ ⟨s, hs, rfl⟩
        exact EReal.coe_le_coe_iff.mpr (hconv_sub hs)
      have hφ : ((inner ℝ a x + b : ℝ) : EReal) ≤ clco_f_aff x := by
        have hcont : Continuous (fun y => ((inner ℝ a y + b : ℝ) : EReal)) :=
          continuous_coe_real_ereal.comp (by fun_prop)
        calc ((inner ℝ a x + b : ℝ) : EReal)
            = Filter.liminf (fun y => ((inner ℝ a y + b : ℝ) : EReal)) (𝓝 x) :=
              ((hcont.tendsto x).liminf_eq).symm
          _ ≤ clco_f_aff x := Filter.liminf_le_liminf (Filter.Eventually.of_forall hlow)
      have hxr : inner ℝ a x + b ≤ r := EReal.coe_le_coe_iff.mp (hφ.trans hr)
      let T : E → E × ℝ := fun y => (y, inner ℝ a y + b + (r - (inner ℝ a x + b)))
      have hT : Continuous T := by fun_prop
      have hTx : T x = (x, r) := by
        simp only [T]
        congr 1
        ring
      rw [← hTx]
      apply map_mem_closure hT hx
      have hA_sub : A ⊆ T ⁻¹' convexHull ℝ (epigraph fA_aff) := by
        intro y hy
        apply subset_convexHull
        show fA_aff (T y).1 ≤ (T y).2
        simp only [fA_aff, f_aff, T, setIndicator, hy, if_true, add_zero]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
      have hT_conv : Convex ℝ (T ⁻¹' convexHull ℝ (epigraph fA_aff)) := by
        intro y1 hy1 y2 hy2 s t hs ht hst
        have := convex_convexHull ℝ (epigraph fA_aff) hy1 hy2 hs ht hst
        have heq : T (s • y1 + t • y2) = s • T y1 + t • T y2 := by
          simp only [T, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, inner_add_right,
            inner_smul_right]
          congr 1
          obtain rfl : t = 1 - s := by linarith
          ring
        show T (s • y1 + t • y2) ∈ convexHull ℝ (epigraph fA_aff)
        rw [heq]
        exact this
      exact convexHull_min hA_sub hT_conv

end FCA_chap_C_ex10
