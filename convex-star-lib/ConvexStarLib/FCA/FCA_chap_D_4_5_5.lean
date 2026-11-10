import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_5_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_5_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_5_5`, so the main result is `FCA_chap_D_4_5_5.FCA_chap_D_4_5_5`.
-/

namespace FCA_chap_D_4_5_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FCA_chap_D_4_5_5
  (f₁ f₂ : E → ℝ)
  (y₁ y₂ : E)
  (hf_convex : ConvexOn ℝ Set.univ f₁ ∧ ConvexOn ℝ Set.univ f₂)
  (hf_minorized : ∃ (s : E) (b : ℝ),
                 ∀ x, (inner ℝ s x + b ≤ f₁ x) ∧ (inner ℝ s x + b ≤ f₂ x)) :
  let infconv := infimalConv (liftRealtoEReal f₁) (liftRealtoEReal f₂)
  (infconv (y₁ + y₂) = (f₁ y₁ + f₂ y₂ : EReal)) →
  directionalSubdifferential infconv (y₁ + y₂) =
  (directionalSubdifferential (liftRealtoEReal f₁) y₁) ∩ (directionalSubdifferential (liftRealtoEReal f₂) y₂) := by
  intro infconv hEq
  -- The directional derivative of a finite convex function is the infimum of its
  -- difference quotients over `t > 0`.
  have FCA_D455_dirDeriv : ∀ (g : E → ℝ), ConvexOn ℝ Set.univ g → ∀ x d : E,
      ∃ L : ℝ, directionalDeriv (liftRealtoEReal g) x d = (L : EReal) ∧
        (∀ t : ℝ, 0 < t → L ≤ (g (x + t • d) - g x) / t) ∧
        (∀ c : ℝ, (∀ t : ℝ, 0 < t → c ≤ (g (x + t • d) - g x) / t) → c ≤ L) := by
    intro g hg x d
    let ψ : ℝ → ℝ := fun t => g (x + t • d)
    have hψc : ConvexOn ℝ Set.univ ψ := by
      refine ⟨convex_univ, ?_⟩
      intro a _ b _ μ ν hμ hν hμν
      have h := hg.2 (Set.mem_univ (x + a • d)) (Set.mem_univ (x + b • d)) hμ hν hμν
      have e : x + (μ • a + ν • b) • d = μ • (x + a • d) + ν • (x + b • d) := by
        rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hμν, one_smul, smul_smul,
          smul_smul, ← add_smul, smul_eq_mul, smul_eq_mul]
      simp only [ψ, smul_eq_mul] at h ⊢
      rw [show x + (μ * a + ν * b) • d = μ • (x + a • d) + ν • (x + b • d) by
        simpa [smul_eq_mul] using e]
      exact h
    let q : ℝ → ℝ := fun t => (g (x + t • d) - g x) / t
    have hq_eq : ∀ t, q t = (ψ t - ψ 0) / (t - 0) := by
      intro t; simp [q, ψ]
    have hmono : MonotoneOn q (Set.Ioi 0) := by
      intro a ha b hb hab
      rw [hq_eq, hq_eq]
      exact hψc.secant_mono (Set.mem_univ 0) (Set.mem_univ a) (Set.mem_univ b)
        (ne_of_gt ha) (ne_of_gt hb) hab
    have hbdd : BddBelow (q '' Set.Ioi 0) := by
      refine ⟨(ψ (-1) - ψ 0) / (-1 - 0), ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      rw [hq_eq]
      have ht' : (0 : ℝ) < t := ht
      exact hψc.secant_mono (Set.mem_univ 0) (Set.mem_univ (-1)) (Set.mem_univ t)
        (by norm_num) (ne_of_gt ht') (by linarith)
    have hlim := hmono.tendsto_nhdsGT hbdd
    refine ⟨sInf (q '' Set.Ioi 0), ?_, ?_, ?_⟩
    · unfold directionalDeriv
      have hfun : (fun t => differenceQuotient (liftRealtoEReal g) x d t)
          = fun t => ((q t : ℝ) : EReal) := by
        funext t
        simp only [differenceQuotient, liftRealtoEReal, q, EReal.coe_div, EReal.coe_sub]
      rw [hfun]
      exact (EReal.tendsto_coe.mpr hlim).limUnder_eq
    · intro t ht
      exact csInf_le hbdd ⟨t, ht, rfl⟩
    · intro c hc
      exact le_csInf (Set.Nonempty.image _ ⟨1, Set.mem_Ioi.mpr one_pos⟩)
        (by rintro _ ⟨t, ht, rfl⟩; exact hc t ht)
  obtain ⟨hc1, hc2⟩ := hf_convex
  obtain ⟨s₀, b₀, hmin⟩ := hf_minorized
  -- the infimal convolution is real-valued
  have hbdd : ∀ x : E, BddBelow (Set.range fun y => f₁ y + f₂ (x - y)) := by
    intro x
    refine ⟨inner ℝ s₀ x + 2 * b₀, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h1 := (hmin y).1
    have h2 := (hmin (x - y)).2
    have e : inner ℝ s₀ (x - y) = inner ℝ s₀ x - inner ℝ s₀ y := inner_sub_right _ _ _
    linarith
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, g = fun x => ⨅ y, (f₁ y + f₂ (x - y)) := ⟨_, rfl⟩
  have hg_le : ∀ x y, g x ≤ f₁ y + f₂ (x - y) := by
    intro x y; rw [hg]; exact ciInf_le (hbdd x) y
  have hg_ge : ∀ x c, (∀ y, c ≤ f₁ y + f₂ (x - y)) → c ≤ g x := by
    intro x c h; rw [hg]; exact le_ciInf h
  have hinf : ∀ x, infconv x = (g x : EReal) := by
    intro x
    show sInf _ = _
    have hset : {z : EReal | ∃ y : E, z = (liftRealtoEReal f₁ y + liftRealtoEReal f₂ (x - y))}
        = Set.range (fun y => ((f₁ y + f₂ (x - y) : ℝ) : EReal)) := by
      ext z; simp [liftRealtoEReal, eq_comm]
    rw [hset, hg]
    exact (Monotone.map_ciInf_of_continuousAt continuous_coe_real_ereal.continuousAt
      EReal.coe_strictMono.monotone (hbdd x)).symm
  have hinfconv : infconv = liftRealtoEReal g := funext hinf
  -- convexity of the infimal convolution
  have hgc : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, ?_⟩
    intro u _ v _ a b ha hb hab
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨y, hy⟩ : ∃ y, f₁ y + f₂ (u - y) < g u + ε := by
      have : g u < g u + ε := by linarith
      rw [hg] at this ⊢
      exact exists_lt_of_ciInf_lt this
    obtain ⟨y', hy'⟩ : ∃ y', f₁ y' + f₂ (v - y') < g v + ε := by
      have : g v < g v + ε := by linarith
      rw [hg] at this ⊢
      exact exists_lt_of_ciInf_lt this
    have e : a • u + b • v - (a • y + b • y') = a • (u - y) + b • (v - y') := by
      rw [smul_sub, smul_sub]; abel
    calc g (a • u + b • v)
        ≤ f₁ (a • y + b • y') + f₂ (a • u + b • v - (a • y + b • y')) := hg_le _ _
      _ = f₁ (a • y + b • y') + f₂ (a • (u - y) + b • (v - y')) := by rw [e]
      _ ≤ (a • f₁ y + b • f₁ y') + (a • f₂ (u - y) + b • f₂ (v - y')) :=
          add_le_add (hc1.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab)
            (hc2.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab)
      _ = a * (f₁ y + f₂ (u - y)) + b * (f₁ y' + f₂ (v - y')) := by
          simp only [smul_eq_mul]; ring
      _ ≤ a * (g u + ε) + b * (g v + ε) :=
          add_le_add (mul_le_mul_of_nonneg_left hy.le ha) (mul_le_mul_of_nonneg_left hy'.le hb)
      _ = a • g u + b • g v + ε := by
          simp only [smul_eq_mul]; linear_combination ε * hab
  have hx0 : g (y₁ + y₂) = f₁ y₁ + f₂ y₂ := by
    have h := hEq
    rw [hinf] at h
    exact_mod_cast h
  rw [hinfconv]
  ext s
  simp only [directionalSubdifferential, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro hs
    obtain ⟨hs1, hs2⟩ : (∀ d, (inner ℝ s d : EReal) ≤ directionalDeriv (liftRealtoEReal f₁) y₁ d) ∧
        (∀ d, (inner ℝ s d : EReal) ≤ directionalDeriv (liftRealtoEReal f₂) y₂ d) := by
      constructor
      · intro d
        obtain ⟨Lh, hLh, hLh1, -⟩ := FCA_D455_dirDeriv g hgc (y₁ + y₂) d
        obtain ⟨L1, hL1, -, hL12⟩ := FCA_D455_dirDeriv f₁ hc1 y₁ d
        have h := hs d
        rw [hLh] at h
        rw [hL1]
        have hreal : inner ℝ s d ≤ Lh := by exact_mod_cast h
        have hle : Lh ≤ L1 := by
          apply hL12
          intro t ht
          refine (hLh1 t ht).trans ?_
          apply div_le_div_of_nonneg_right _ ht.le
          have h' := hg_le (y₁ + y₂ + t • d) (y₁ + t • d)
          have e : y₁ + y₂ + t • d - (y₁ + t • d) = y₂ := by abel
          rw [e] at h'
          linarith
        exact_mod_cast hreal.trans hle
      · intro d
        obtain ⟨Lh, hLh, hLh1, -⟩ := FCA_D455_dirDeriv g hgc (y₁ + y₂) d
        obtain ⟨L2, hL2, -, hL22⟩ := FCA_D455_dirDeriv f₂ hc2 y₂ d
        have h := hs d
        rw [hLh] at h
        rw [hL2]
        have hreal : inner ℝ s d ≤ Lh := by exact_mod_cast h
        have hle : Lh ≤ L2 := by
          apply hL22
          intro t ht
          refine (hLh1 t ht).trans ?_
          apply div_le_div_of_nonneg_right _ ht.le
          have h' := hg_le (y₁ + y₂ + t • d) y₁
          have e : y₁ + y₂ + t • d - y₁ = y₂ + t • d := by abel
          rw [e] at h'
          linarith
        exact_mod_cast hreal.trans hle
    exact ⟨hs1, hs2⟩
  · rintro ⟨hs1, hs2⟩ d
    -- global subgradient inequalities
    have hsub1 : ∀ z, f₁ y₁ + inner ℝ s (z - y₁) ≤ f₁ z := by
      intro z
      obtain ⟨L1, hL1, hL11, -⟩ := FCA_D455_dirDeriv f₁ hc1 y₁ (z - y₁)
      have h := hs1 (z - y₁)
      rw [hL1] at h
      have h1 : inner ℝ s (z - y₁) ≤ L1 := by exact_mod_cast h
      have h2 := hL11 1 one_pos
      rw [one_smul, div_one, add_sub_cancel] at h2
      linarith
    have hsub2 : ∀ z, f₂ y₂ + inner ℝ s (z - y₂) ≤ f₂ z := by
      intro z
      obtain ⟨L2, hL2, hL21, -⟩ := FCA_D455_dirDeriv f₂ hc2 y₂ (z - y₂)
      have h := hs2 (z - y₂)
      rw [hL2] at h
      have h1 : inner ℝ s (z - y₂) ≤ L2 := by exact_mod_cast h
      have h2 := hL21 1 one_pos
      rw [one_smul, div_one, add_sub_cancel] at h2
      linarith
    have hsubg : ∀ z, g (y₁ + y₂) + inner ℝ s (z - (y₁ + y₂)) ≤ g z := by
      intro z
      apply hg_ge
      intro y
      have h1 := hsub1 y
      have h2 := hsub2 (z - y)
      have e : inner ℝ s (z - (y₁ + y₂)) = inner ℝ s (y - y₁) + inner ℝ s (z - y - y₂) := by
        rw [← inner_add_right]; congr 1; abel
      linarith
    obtain ⟨Lh, hLh, -, hLh2⟩ := FCA_D455_dirDeriv g hgc (y₁ + y₂) d
    rw [hLh]
    have hfin : inner ℝ s d ≤ Lh := by
      apply hLh2
      intro t ht
      rw [le_div_iff₀ ht]
      have h := hsubg (y₁ + y₂ + t • d)
      have e : inner ℝ s (y₁ + y₂ + t • d - (y₁ + y₂)) = t * inner ℝ s d := by
        rw [add_sub_cancel_left, real_inner_smul_right]
      linarith
    exact_mod_cast hfin

end FCA_chap_D_4_5_5
