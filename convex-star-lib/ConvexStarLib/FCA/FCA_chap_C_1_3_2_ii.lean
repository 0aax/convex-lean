import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_3_2_ii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_3_2_ii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_3_2_ii`, so the main result is `FCA_chap_C_1_3_2_ii.FCA_chap_C_1_3_2_ii`.
-/

namespace FCA_chap_C_1_3_2_ii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_1_3_2_ii
  {m : ℕ}
  (σ : ℕ → (E → EReal))
  (J : ℕ → ℕ)
  (hσ_sublinear : ∀ i, i ≤ m → IsSublinear ((σ (J i))))
  (hσ_minorized : ∃ (s : E), ∃ (b : ℝ),
    ∀ i, i ≤ m → ∀ (x : E),
    (σ (J i)) x ≥ (inner ℝ s x) + b)
  (hm : 0 < m)
  (hσ_zero : ∀ i, i < m → σ (J i) 0 = 0) :
  let σJ := fun i => σ (J i)
  let σ_infconv := multiInfimalConv m σJ
  let σ_min := fun x => sInf (⋃ i ∈ Finset.range m, {(σ (J i)) x})
  let σ' := convexHullFun σ_min
  ∀ x, σ_infconv x = (σ') x := by
  intro σJ σ_infconv σ_min σ' x
  -- coercion of finite sums into `EReal`
  have coe_sum : ∀ (T : Finset ℕ) (f : ℕ → ℝ),
      ((∑ i ∈ T, f i : ℝ) : EReal) = ∑ i ∈ T, (f i : EReal) := by
    intro T f
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]
  have hbot : ∀ i, i < m → ∀ y, σ (J i) y ≠ ⊥ := fun i hi y =>
    ((hσ_sublinear i hi.le).1.1 y).ne'
  have hconv : ∀ i, i < m → Convex ℝ (epigraph (σ (J i))) := fun i hi =>
    (hσ_sublinear i hi.le).1.2.2
  have hhom : ∀ i, i < m → ∀ y (t : ℝ), 0 < t → σ (J i) (t • y) = t * σ (J i) y :=
    fun i hi y t ht => (hσ_sublinear i hi.le).2 y t ht
  have hmin_le : ∀ i, i < m → ∀ y, σ_min y ≤ σ (J i) y := by
    intro i hi y
    apply sInf_le
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Finset.mem_range]
    exact ⟨i, hi, rfl⟩
  have hmin_mem : ∀ y, ∃ i, i < m ∧ σ_min y = σ (J i) y := by
    intro y
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.range m) (fun i => σ (J i) y)
      ⟨0, Finset.mem_range.mpr hm⟩
    refine ⟨i, Finset.mem_range.mp hi, le_antisymm (hmin_le i (Finset.mem_range.mp hi) y) ?_⟩
    apply le_sInf
    intro b hb
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact hmin j hj
  apply le_antisymm
  · -- σ_infconv x ≤ σ' x
    set S : Set (E × ℝ) := {p | ∃ y : ℕ → E, ∃ s : ℕ → ℝ, p.1 = ∑ i ∈ Finset.range m, y i ∧
      (∀ i, i < m → σ (J i) (y i) ≤ (s i : EReal)) ∧ ∑ i ∈ Finset.range m, s i ≤ p.2} with hS
    have hepi : epigraph σ_min ⊆ S := by
      rintro ⟨u, r⟩ hur
      simp only [epigraph, Set.mem_setOf_eq] at hur
      obtain ⟨i, hi, hieq⟩ := hmin_mem u
      refine ⟨fun j => if j = i then u else 0, fun j => if j = i then r else 0, ?_, ?_, ?_⟩
      · simp [Finset.sum_ite_eq', Finset.mem_range, hi]
      · intro j hj
        by_cases hji : j = i
        · subst hji
          simp only [if_true]
          rw [← hieq]
          exact hur
        · simp [hji, hσ_zero j hj]
      · simp [Finset.sum_ite_eq', Finset.mem_range, hi]
    have hSconv : Convex ℝ S := by
      rintro ⟨u, r⟩ ⟨y, s, hu, hys, hs⟩ ⟨u', r'⟩ ⟨y', s', hu', hys', hs'⟩ a b ha hb hab
      refine ⟨fun i => a • y i + b • y' i, fun i => a * s i + b * s' i, ?_, ?_, ?_⟩
      · simp only [Prod.fst_add, Prod.smul_fst] at hu hu' ⊢
        rw [hu, hu', Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      · intro i hi
        have h1 : (y i, s i) ∈ epigraph (σ (J i)) := hys i hi
        have h2 : (y' i, s' i) ∈ epigraph (σ (J i)) := hys' i hi
        have := hconv i hi h1 h2 ha hb hab
        simpa [epigraph] using this
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum] at hs hs' ⊢
        nlinarith [mul_le_mul_of_nonneg_left hs ha, mul_le_mul_of_nonneg_left hs' hb]
    have hsub : convexHull ℝ (epigraph σ_min) ⊆ S := convexHull_min hepi hSconv
    show σ_infconv x ≤ sInf _
    apply le_sInf
    rintro w ⟨r, hr, rfl⟩
    obtain ⟨y, s, hx, hys, hs⟩ := hsub hr
    calc σ_infconv x ≤ ∑ i ∈ Finset.range m, σJ i (y i) := sInf_le ⟨y, hx, rfl⟩
      _ ≤ ∑ i ∈ Finset.range m, (s i : EReal) :=
          Finset.sum_le_sum (fun i hi => hys i (Finset.mem_range.mp hi))
      _ = ((∑ i ∈ Finset.range m, s i : ℝ) : EReal) := (coe_sum _ _).symm
      _ ≤ (r : EReal) := EReal.coe_le_coe_iff.mpr hs
  · -- σ' x ≤ σ_infconv x
    show sInf _ ≤ sInf _
    apply le_sInf
    rintro z ⟨y, hx, rfl⟩
    by_cases htop : ∃ i, i < m ∧ σ (J i) (y i) = ⊤
    · obtain ⟨i, hi, hti⟩ := htop
      have : ∑ j ∈ Finset.range m, σJ j (y j) = ⊤ := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hi)]
        show σ (J i) (y i) + _ = ⊤
        rw [hti]
        apply EReal.top_add_of_ne_bot
        apply Finset.sum_induction _ (fun a => a ≠ ⊥)
        · intro a b ha hb
          exact EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩
        · exact EReal.zero_ne_bot
        · intro j hj
          exact hbot j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj)) (y j)
      rw [this]
      exact le_top
    · push_neg at htop
      set a : ℕ → ℝ := fun i => (σ (J i) (y i)).toReal with ha
      have hcoe : ∀ i, i < m → σ (J i) (y i) = (a i : EReal) := fun i hi =>
        (EReal.coe_toReal (htop i hi) (hbot i hi (y i))).symm
      have hsum : ∑ j ∈ Finset.range m, σJ j (y j) =
          ((∑ j ∈ Finset.range m, a j : ℝ) : EReal) := by
        rw [coe_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact hcoe j (Finset.mem_range.mp hj)
      rw [hsum]
      apply sInf_le
      refine ⟨∑ j ∈ Finset.range m, a j, ?_, rfl⟩
      show (x, ∑ j ∈ Finset.range m, a j) ∈ convexHull ℝ (epigraph σ_min)
      have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      have key : (x, ∑ j ∈ Finset.range m, a j) =
          ∑ j ∈ Finset.range m, (1 / (m : ℝ)) • ((m : ℝ) • y j, (m : ℝ) * a j) := by
        rw [hx]
        ext
        · dsimp only
          rw [Prod.fst_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [Prod.smul_fst, smul_smul]
          rw [one_div_mul_cancel hmpos.ne', one_smul]
        · dsimp only
          rw [Prod.snd_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [Prod.smul_snd, smul_eq_mul]
          field_simp
      rw [key]
      apply (convex_convexHull ℝ _).sum_mem
      · intro j _
        positivity
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
      · intro j hj
        apply subset_convexHull
        have hj' := Finset.mem_range.mp hj
        show σ_min ((m : ℝ) • y j) ≤ (((m : ℝ) * a j : ℝ) : EReal)
        calc σ_min ((m:ℝ) • y j) ≤ σ (J j) ((m:ℝ) • y j) := hmin_le j hj' _
          _ = (m : ℝ) * σ (J j) (y j) := hhom j hj' _ _ hmpos
          _ = (m : ℝ) * (a j : EReal) := by rw [hcoe j hj']
          _ = (((m : ℝ) * a j : ℝ) : EReal) := by rw [EReal.coe_mul]

end FCA_chap_C_1_3_2_ii
