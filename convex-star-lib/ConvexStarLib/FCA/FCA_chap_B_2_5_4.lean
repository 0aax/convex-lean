import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_5_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_5_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_5_4`, so the main result is `FCA_chap_B_2_5_4.FCA_chap_B_2_5_4`.
-/

namespace FCA_chap_B_2_5_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_B_2_5_4
  {n m : ℕ}
  (g : ℕ → (E → EReal))
  (hg_convex : ∀ i, i < m → InConvRn (g i))
  (hg_minorized : ∃ (s : E) (b : ℝ),
    ∀ i, i < m → ∀ x, inner ℝ s x + b ≤ g i x)
  (g_ne_bot : ∀ x₁ x₂, ⊥ < g x₁ x₂) :
  let g' := convexHullFun
    (fun x => sInf (⋃ j ∈ Finset.range m, {g j x}))
  let g_combo := fun x => sInf {v |
    ∃ α ∈ probSimplex m,
      ∃ (x' : ℕ → E),
        (∀ j < m, x' j ∈ effDom ((g j))) ∧
        (x = ∑ j, (α j) • (x' j)) ∧
        (v = ∑ j, (α j) * (g j (x' j)))}
  ∀ x, g' x = g_combo x := by
  intro g' g_combo x
  classical
  simp only [g', g_combo, convexHullFun, funFromSet]
  set F : E → EReal := fun x => sInf (⋃ j ∈ Finset.range m, {g j x}) with hF_def
  have hF_le : ∀ j < m, ∀ y, F y ≤ g j y := by
    intro j hj y
    apply sInf_le
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Finset.mem_range]
    exact ⟨j, hj, rfl⟩
  have hF_attained : ∀ y (r : ℝ), F y ≤ (r : EReal) → ∃ j < m, g j y ≤ (r : EReal) := by
    intro y r h
    have hfin : (⋃ j ∈ Finset.range m, ({g j y} : Set EReal)).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet (Finset.range m)) (fun j _ => Set.finite_singleton (g j y))
    rcases Set.eq_empty_or_nonempty (⋃ j ∈ Finset.range m, ({g j y} : Set EReal)) with hemp | hne
    · exfalso
      have hFy : F y = ⊤ := by simp only [hF_def, hemp, _root_.sInf_empty]
      rw [hFy] at h
      exact absurd h (not_le.mpr (EReal.coe_lt_top r))
    · have hmem := hne.csInf_mem hfin
      obtain ⟨j, hj, hjeq⟩ := Set.mem_iUnion₂.mp hmem
      refine ⟨j, Finset.mem_range.mp hj, ?_⟩
      rw [← Set.mem_singleton_iff.mp hjeq]
      exact h
  -- real values on the effective domain
  have hreal : ∀ j y, y ∈ effDom (g j) → ((g j y).toReal : EReal) = g j y := by
    intro j y hy
    exact EReal.coe_toReal (ne_of_lt hy) (ne_of_gt (g_ne_bot j y))
  -- coercion of sums
  have hcoe_sum : ∀ (f : Fin m → ℝ), ((∑ i, f i : ℝ) : EReal) = ∑ i, (f i : EReal) := by
    intro f
    exact map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f Finset.univ
  -- nonempty epigraphs
  have hpt : ∀ i, ∃ p : E × ℝ, i < m → p ∈ epigraph (g i) := by
    intro i
    by_cases hi : i < m
    · obtain ⟨y, hy⟩ := (hg_convex i hi).2.1
      refine ⟨(y, (g i y).toReal), fun _ => ?_⟩
      show g i y ≤ ((g i y).toReal : EReal)
      rw [hreal i y hy]
    · exact ⟨0, fun h => absurd h hi⟩
  choose p0 hp0 using hpt
  -- the key description of the convex hull
  have key : convexHull ℝ (epigraph F) ⊆ {q | ∃ α ∈ probSimplex m, ∃ p : ℕ → E × ℝ,
      (∀ j < m, p j ∈ epigraph (g j)) ∧ q = ∑ j : Fin m, α j • p j} := by
    apply convexHull_min
    · rintro ⟨y, r⟩ hyr
      obtain ⟨j, hj, hjle⟩ := hF_attained y r hyr
      refine ⟨fun i => if (i : ℕ) = j then 1 else 0, ⟨?_, ?_⟩,
        fun i => if i = j then (y, r) else p0 i, ?_, ?_⟩
      · intro i; beta_reduce; split_ifs <;> norm_num
      · rw [Fintype.sum_eq_single ⟨j, hj⟩]
        · simp
        · intro b hb
          have : (b : ℕ) ≠ j := fun h => hb (Fin.ext h)
          simp [this]
      · intro i hi
        beta_reduce
        split_ifs with h
        · subst h; exact hjle
        · exact hp0 i hi
      · rw [Fintype.sum_eq_single ⟨j, hj⟩]
        · simp
        · intro b hb
          have : (b : ℕ) ≠ j := fun h => hb (Fin.ext h)
          simp [this]
    · rintro q₁ ⟨α, hα, p, hp, rfl⟩ q₂ ⟨β, hβ, p', hp', rfl⟩ a b ha hb hab
      -- extend to ℕ
      obtain ⟨αN, hαN⟩ : ∃ αN : ℕ → ℝ, ∀ j, αN j = if h : j < m then α ⟨j, h⟩ else 0 :=
        ⟨_, fun j => rfl⟩
      obtain ⟨βN, hβN⟩ : ∃ βN : ℕ → ℝ, ∀ j, βN j = if h : j < m then β ⟨j, h⟩ else 0 :=
        ⟨_, fun j => rfl⟩
      have hαN' : ∀ i : Fin m, αN i = α i := fun i => by simp [hαN, i.isLt]
      have hβN' : ∀ i : Fin m, βN i = β i := fun i => by simp [hβN, i.isLt]
      obtain ⟨w, hw⟩ : ∃ w : ℕ → E × ℝ, ∀ j, w j = if a * αN j + b * βN j = 0 then p j else
          (a * αN j / (a * αN j + b * βN j)) • p j + (b * βN j / (a * αN j + b * βN j)) • p' j :=
        ⟨_, fun j => rfl⟩
      refine ⟨fun i => a * α i + b * β i, ⟨?_, ?_⟩, w, ?_, ?_⟩
      · intro i
        exact add_nonneg (mul_nonneg ha (hα.1 i)) (mul_nonneg hb (hβ.1 i))
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hα.2, hβ.2, mul_one,
          mul_one, hab]
      · intro j hj
        have hαj : 0 ≤ αN j := by rw [hαN, dif_pos hj]; exact hα.1 _
        have hβj : 0 ≤ βN j := by rw [hβN, dif_pos hj]; exact hβ.1 _
        rw [hw]
        split_ifs with h0
        · exact hp j hj
        · have hγpos : 0 < a * αN j + b * βN j :=
            lt_of_le_of_ne (add_nonneg (mul_nonneg ha hαj) (mul_nonneg hb hβj)) (Ne.symm h0)
          apply (hg_convex j hj).2.2 (hp j hj) (hp' j hj)
          · exact div_nonneg (mul_nonneg ha hαj) hγpos.le
          · exact div_nonneg (mul_nonneg hb hβj) hγpos.le
          · rw [← add_div]; exact div_self h0
      · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have hαi := hα.1 i
        have hβi := hβ.1 i
        beta_reduce
        rw [hw, hαN', hβN']
        split_ifs with h0
        · have h1 : a * α i = 0 := by nlinarith [mul_nonneg ha hαi, mul_nonneg hb hβi]
          have h2 : b * β i = 0 := by nlinarith [mul_nonneg ha hαi, mul_nonneg hb hβi]
          rw [h0, zero_smul, smul_smul, smul_smul, h1, h2, zero_smul, zero_smul, add_zero]
        · rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, mul_div_cancel₀ _ h0,
            mul_div_cancel₀ _ h0]
  -- main
  apply le_antisymm
  · -- g' x ≤ g_combo x
    apply le_sInf
    rintro v ⟨α, hα, x', hdom, hx, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : Fin m → ℝ, ∀ j, t j = (g j (x' j)).toReal := ⟨_, fun j => rfl⟩
    have hv : ∑ j : Fin m, ((α j : ℝ) : EReal) * g j (x' j) = ((∑ j, α j * t j : ℝ) : EReal) := by
      rw [hcoe_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [EReal.coe_mul, ht, hreal j (x' j) (hdom j j.isLt)]
    rw [hv]
    apply sInf_le
    refine ⟨∑ j, α j * t j, ?_, rfl⟩
    show (x, ∑ j, α j * t j) ∈ convexHull ℝ (epigraph F)
    have heq : (x, ∑ j, α j * t j) = ∑ j : Fin m, α j • (x' j, t j) := by
      ext
      · simp [Prod.fst_sum, hx]
      · simp [Prod.snd_sum]
    rw [heq]
    apply (convex_convexHull ℝ _).sum_mem (fun i _ => hα.1 i) hα.2
    intro j _
    apply subset_convexHull
    show F (x' j) ≤ ((t j : ℝ) : EReal)
    rw [ht, hreal j (x' j) (hdom j j.isLt)]
    exact hF_le j j.isLt _
  · -- g_combo x ≤ g' x
    apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨α, hα, p, hp, hxr⟩ := key (show (x, r) ∈ convexHull ℝ (epigraph F) from hr)
    have hdom : ∀ j < m, (p j).1 ∈ effDom (g j) :=
      fun j hj => lt_of_le_of_lt (hp j hj) (EReal.coe_lt_top _)
    have hx : x = ∑ j : Fin m, α j • (p j).1 := by
      have := congrArg Prod.fst hxr
      simpa [Prod.fst_sum] using this
    have hr' : r = ∑ j : Fin m, α j * (p j).2 := by
      have := congrArg Prod.snd hxr
      simpa [Prod.snd_sum] using this
    calc sInf {v | ∃ α ∈ probSimplex m, ∃ x' : ℕ → E, (∀ j < m, x' j ∈ effDom (g j)) ∧
            x = ∑ j : Fin m, α j • x' j ∧ v = ∑ j : Fin m, ((α j : ℝ) : EReal) * g j (x' j)}
        ≤ ∑ j : Fin m, ((α j : ℝ) : EReal) * g j (p j).1 :=
          sInf_le ⟨α, hα, fun k => (p k).1, hdom, hx, rfl⟩
      _ = ((∑ j, α j * (g j (p j).1).toReal : ℝ) : EReal) := by
          rw [hcoe_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [EReal.coe_mul, hreal j _ (hdom j j.isLt)]
      _ ≤ (r : EReal) := by
          rw [EReal.coe_le_coe_iff, hr']
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hα.1 j)
          have h1 := hp j j.isLt
          have h2 : ((g j (p j).1).toReal : EReal) ≤ ((p j).2 : EReal) := by
            rw [hreal j _ (hdom j j.isLt)]; exact h1
          exact EReal.coe_le_coe_iff.mp h2

end FCA_chap_B_2_5_4
