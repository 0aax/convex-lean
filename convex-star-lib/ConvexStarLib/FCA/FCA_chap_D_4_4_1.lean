import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_4_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_4_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_4_1`, so the main result is `FCA_chap_D_4_4_1.FCA_chap_D_4_4_1`.
-/

namespace FCA_chap_D_4_4_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
theorem FCA_chap_D_4_4_1 {J : Type*}
  (f : J → (E → ℝ))
  (x : E)
  (hf_convex : ∀ (i : J), ConvexOn ℝ Set.univ (f i))
  (hf_finite : ∀ z, ⨆ (j : J), (f j z : EReal) < ⊤) :
  let F : E → EReal := fun z => ⨆ (j : J), (f j z)
  let Jx := {j | f j x = F x}
  closure (convexHull ℝ (⋃ j ∈ Jx, directionalSubdifferential (liftRealtoEReal (f j)) x)) ⊆
  directionalSubdifferential F x := by
  intro F Jx
  -- difference quotients of a real convex function are monotone in `t > 0`
  have hmono : ∀ g : E → ℝ, ConvexOn ℝ Set.univ g → ∀ d : E,
      MonotoneOn (fun t : ℝ => (g (x + t • d) - g x) / t) (Set.Ioi 0) := by
    intro g hg d s hs t ht hst
    simp only [Set.mem_Ioi] at hs ht
    have hst' : s / t ≤ 1 := (div_le_one ht).2 hst
    have key := hg.2 (Set.mem_univ x) (Set.mem_univ (x + t • d)) (sub_nonneg.2 hst')
      (div_nonneg hs.le ht.le) (sub_add_cancel 1 (s / t))
    have e : (1 - s / t) • x + (s / t) • (x + t • d) = x + s • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ s ht.ne', ← add_assoc, ← add_smul, sub_add_cancel,
        one_smul]
    rw [e, smul_eq_mul, smul_eq_mul] at key
    show (g (x + s • d) - g x) / s ≤ (g (x + t • d) - g x) / t
    rw [div_le_div_iff₀ hs ht]
    have key2 := mul_le_mul_of_nonneg_right key ht.le
    have e2 : ((1 - s / t) * g x + s / t * g (x + t • d)) * t
        = (t - s) * g x + s * g (x + t • d) := by
      field_simp
    rw [e2] at key2
    nlinarith
  -- hence the (extended real) difference quotients have a limit as `t → 0⁺`
  have hlim : ∀ g : E → ℝ, ConvexOn ℝ Set.univ g → ∀ d : E, ∃ L : EReal,
      Filter.Tendsto (fun t : ℝ => differenceQuotient (fun z => (g z : EReal)) x d t)
        (𝓝[>] 0) (𝓝 L) := by
    intro g hg d
    have hm : MonotoneOn (fun t : ℝ => differenceQuotient (fun z => (g z : EReal)) x d t)
        (Set.Ioi 0) := by
      intro s hs t ht hst
      show (((g (x + s • d) - g x) / s : ℝ) : EReal) ≤ (((g (x + t • d) - g x) / t : ℝ) : EReal)
      exact EReal.coe_le_coe_iff.2 (hmono g hg d hs ht hst)
    exact ⟨_, hm.tendsto_nhdsGT (OrderBot.bddBelow _)⟩
  -- the target set is an intersection of closed half-spaces
  have hS : directionalSubdifferential F x
      = ⋂ d : E, {s : E | ((inner ℝ s d : ℝ) : EReal) ≤ directionalDeriv F x d} := by
    ext s
    simp [directionalSubdifferential]
  have hS_closed : IsClosed (directionalSubdifferential F x) := by
    rw [hS]
    exact isClosed_iInter fun d =>
      isClosed_le (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const))
        continuous_const
  have hS_convex : Convex ℝ (directionalSubdifferential F x) := by
    rw [hS]
    refine convex_iInter fun d => ?_
    intro s1 hs1 s2 hs2 a b ha hb hab
    simp only [Set.mem_setOf_eq] at hs1 hs2 ⊢
    generalize directionalDeriv F x d = c at hs1 hs2 ⊢
    induction c with
    | bot => exact absurd hs1 (by simp)
    | top => exact le_top
    | coe r =>
      rw [EReal.coe_le_coe_iff] at hs1 hs2 ⊢
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have h3 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
      linarith [mul_le_mul_of_nonneg_left hs1 ha, mul_le_mul_of_nonneg_left hs2 hb]
  apply closure_minimal _ hS_closed
  apply convexHull_min _ hS_convex
  intro s hs
  simp only [Set.mem_iUnion] at hs
  obtain ⟨j, hj, hs⟩ := hs
  have hj' : ((f j x : ℝ) : EReal) = F x := hj
  have hs' : ∀ d, ((inner ℝ s d : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal (f j)) x d := hs
  -- `F` is real valued
  have hFbot : ∀ z, F z ≠ ⊥ := fun z =>
    ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (f j z)) (le_iSup (fun i => (f i z : EReal)) j))
  have hFtop : ∀ z, F z ≠ ⊤ := fun z => (hf_finite z).ne
  obtain ⟨G, hFG⟩ : ∃ G : E → ℝ, ∀ z, F z = ((G z : ℝ) : EReal) :=
    ⟨fun z => (F z).toReal, fun z => (EReal.coe_toReal (hFtop z) (hFbot z)).symm⟩
  have hfG : ∀ i z, f i z ≤ G z := fun i z =>
    EReal.coe_le_coe_iff.1 ((le_iSup (fun i => (f i z : EReal)) i).trans (hFG z).le)
  have hGconv : ConvexOn ℝ Set.univ G := by
    refine ⟨convex_univ, fun z1 _ z2 _ a b ha hb hab => ?_⟩
    have h : F (a • z1 + b • z2) ≤ ((a * G z1 + b * G z2 : ℝ) : EReal) := by
      show (⨆ i, (f i (a • z1 + b • z2) : EReal)) ≤ _
      refine iSup_le fun i => EReal.coe_le_coe_iff.2 ?_
      calc f i (a • z1 + b • z2) ≤ a • f i z1 + b • f i z2 :=
            (hf_convex i).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
        _ ≤ a * G z1 + b * G z2 := by
          simp only [smul_eq_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hfG i z1) ha)
            (mul_le_mul_of_nonneg_left (hfG i z2) hb)
    rw [hFG] at h
    simpa [smul_eq_mul] using EReal.coe_le_coe_iff.1 h
  have hF_eq : F = fun z => ((G z : ℝ) : EReal) := funext hFG
  have hjG : f j x = G x := by
    have := hFG x
    rw [← hj'] at this
    exact_mod_cast this
  show ∀ d, ((inner ℝ s d : ℝ) : EReal) ≤ directionalDeriv F x d
  intro d
  obtain ⟨Lj, hLj⟩ := hlim (f j) (hf_convex j) d
  obtain ⟨LF, hLF⟩ := hlim G hGconv d
  have h1 : directionalDeriv (liftRealtoEReal (f j)) x d = Lj := hLj.limUnder_eq
  have h2 : directionalDeriv F x d = LF := by
    rw [hF_eq]
    exact hLF.limUnder_eq
  rw [h2]
  refine (hs' d).trans ?_
  rw [h1]
  refine le_of_tendsto_of_tendsto hLj hLF ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  show (((f j (x + t • d) - f j x) / t : ℝ) : EReal) ≤ (((G (x + t • d) - G x) / t : ℝ) : EReal)
  apply EReal.coe_le_coe_iff.2
  rw [hjG]
  exact div_le_div_of_nonneg_right (sub_le_sub_right (hfG j _) _) ht'.le

end FCA_chap_D_4_4_1
