import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_3_9_i`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_3_9_i` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_3_9_i`, so the main result is `Renegar_chap_2_2_3_9_i.Renegar_chap_2_2_3_9_i`.
-/

namespace Renegar_chap_2_2_3_9_i

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Renegar_chap_2_2_3_9_i [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (hf_sc : IsSelfConcordantLocalNorm f Df) :
  ((IsLogarithmicallyHomogeneousBarrier f Df h_Df_pd) ↔
  (∀ x ∈ Df, ∀ (t : ℝ), 0 < t →
    gradient f (t • x) = t⁻¹ • (gradient f x))) := by
  have hf_diff : ∀ x ∈ Df, DifferentiableAt ℝ f x := fun x hx =>
    (hf_C2.differentiableOn (by norm_num)).differentiableAt (h_Df_open.mem_nhds hx)
  have hinner_grad : ∀ y v : E, inner ℝ (gradient f y) v = fderiv ℝ f y v := fun y v => by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  constructor
  · -- (→)
    rintro ⟨_, K, hK, hcone, hhom⟩
    intro x hx t ht
    have hint_cone : ∀ y ∈ interior K, t • y ∈ interior K := by
      intro y hy
      rw [mem_interior] at hy ⊢
      obtain ⟨U, hUK, hUo, hyU⟩ := hy
      refine ⟨t • U, ?_, hUo.smul₀ ht.ne', Set.smul_mem_smul_set hyU⟩
      rintro _ ⟨u, hu, rfl⟩
      exact hcone u (hUK hu) t ht
    have htx : t • x ∈ Df := by rw [hK] at hx ⊢; exact hint_cone x hx
    have h1 : HasFDerivAt (fun y => f (t • y))
        ((fderiv ℝ f (t • x)).comp (t • ContinuousLinearMap.id ℝ E)) x := by
      have := (hf_diff _ htx).hasFDerivAt
      exact this.comp x ((hasFDerivAt_id x).const_smul t)
    have h2 : HasFDerivAt (fun y => f (t • y)) (fderiv ℝ f x) x := by
      have : (fun y => f y - barrierParameter f Df h_Df_pd * Real.log t) =ᶠ[𝓝 x]
          (fun y => f (t • y)) := by
        have hmem : interior K ∈ 𝓝 x := by rw [← hK]; exact h_Df_open.mem_nhds hx
        filter_upwards [hmem] with y hy
        rw [hhom y hy t ht]
      exact ((hf_diff x hx).hasFDerivAt.sub_const _).congr_of_eventuallyEq this.symm
    have h3 := h1.unique h2
    apply ext_inner_right ℝ
    intro v
    rw [hinner_grad, real_inner_smul_left, hinner_grad]
    have := congrArg (fun L => L v) h3
    simp at this
    rw [← this]
    field_simp
  · -- (←)
    intro hg
    -- the gradient is differentiable on `Df` (otherwise the Hessian would vanish)
    have hgrad_diff : ∀ x ∈ Df, DifferentiableAt ℝ (fun y => gradient f y) x := by
      intro x hx
      by_contra hnd
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have := h_Df_pd x hx v hv
      simp [localInnerProd, hessianOperator, fderiv_zero_of_not_differentiableAt hnd] at this
    -- Euler identity: `H(x) x = - ∇f(x)`
    have hHx : ∀ x ∈ Df, hessianOperator f x x = -gradient f x := by
      intro x hx
      have h1 : HasDerivAt (fun t : ℝ => gradient f (t • x)) (hessianOperator f x x) 1 := by
        have hd : HasFDerivAt (fun y => gradient f y) (hessianOperator f x) ((1:ℝ) • x) := by
          rw [one_smul]; exact (hgrad_diff x hx).hasFDerivAt
        have hl : HasDerivAt (fun t : ℝ => t • x) x 1 := by
          simpa using (hasDerivAt_id (1:ℝ)).smul_const x
        exact hd.comp_hasDerivAt 1 hl
      have h2 : HasDerivAt (fun t : ℝ => gradient f (t • x)) (-((1:ℝ)^2)⁻¹ • gradient f x) 1 := by
        have h3 : HasDerivAt (fun t : ℝ => t⁻¹ • gradient f x) (-((1:ℝ)^2)⁻¹ • gradient f x) 1 :=
          (hasDerivAt_inv one_ne_zero).smul_const _
        apply h3.congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds one_pos] with t ht
        exact hg x hx t ht
      have := h1.unique h2
      simpa using this
    -- one step inside the Dikin ball along the ray through `z`
    have hdikin : ∀ z ∈ Df, ∀ c : ℝ,
        |c - 1| * Real.sqrt (-(inner ℝ (gradient f z) z)) < 1 → c • z ∈ Df := by
      intro z hz c hlt
      apply (hf_sc z hz).1
      show localNorm f z (c • z - z) < 1
      have : c • z - z = (c - 1) • z := by rw [sub_smul, one_smul]
      rw [this]
      unfold localNorm localInnerProd
      rw [map_smul, hHx z hz, inner_smul_left, inner_smul_right, inner_neg_right, real_inner_comm]
      have : (starRingEnd ℝ) (c - 1) * ((c - 1) * -inner ℝ (gradient f z) z)
          = (c - 1) ^ 2 * -inner ℝ (gradient f z) z := by simp; ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      exact hlt
    -- `Df` is a cone
    have hcone : ∀ x ∈ Df, ∀ t : ℝ, 0 < t → t • x ∈ Df := by
      intro x hx
      set a := Real.sqrt (-(inner ℝ (gradient f x) x)) with ha
      have ha0 : 0 ≤ a := Real.sqrt_nonneg _
      set q : ℝ := 1 + 1 / (a + 1) with hq
      have hq1 : 1 < q := by have : 0 < 1 / (a + 1) := by positivity
                             linarith
      have hq0 : 0 < q := by linarith
      have hc_ok : ∀ c : ℝ, q⁻¹ ≤ c → c ≤ q → |c - 1| * a < 1 := by
        intro c h1 h2
        have h3 : |c - 1| ≤ q - 1 := by
          rw [abs_le]
          constructor
          · have : 2 - q ≤ q⁻¹ := by
              rw [← one_div, le_div_iff₀ hq0]
              nlinarith [sq_nonneg (q - 1)]
            linarith
          · linarith
        calc |c - 1| * a ≤ (q - 1) * a := mul_le_mul_of_nonneg_right h3 ha0
          _ = a / (a + 1) := by rw [hq]; field_simp; ring
          _ < 1 := by rw [div_lt_one (by linarith)]; linarith
      have hstep : ∀ s : ℝ, 0 < s → s • x ∈ Df → ∀ c : ℝ, q⁻¹ ≤ c → c ≤ q →
          (c * s) • x ∈ Df := by
        intro s hs hsx c h1 h2
        rw [mul_smul]
        apply hdikin (s • x) hsx c
        rw [hg x hx s hs, inner_smul_left, inner_smul_right]
        have : (starRingEnd ℝ) s⁻¹ * (s * inner ℝ (gradient f x) x) = inner ℝ (gradient f x) x := by
          simp; field_simp
        rw [this]
        exact hc_ok c h1 h2
      have hind : ∀ n : ℕ, ∀ t : ℝ, (q ^ n)⁻¹ ≤ t → t ≤ q ^ n → t • x ∈ Df := by
        intro n
        induction n with
        | zero =>
          intro t h1 h2
          simp only [pow_zero, inv_one] at h1 h2
          rw [le_antisymm h2 h1, one_smul]
          exact hx
        | succ n ih =>
          intro t h1 h2
          have hqn : 0 < q ^ n := pow_pos hq0 n
          have hqn1 : 1 ≤ q ^ n := one_le_pow₀ hq1.le
          have hqn2 : (q ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hqn1
          by_cases ht1 : q ^ n < t
          · have := hstep (q ^ n) hqn (ih _ (hqn2.trans hqn1) le_rfl) (t / q ^ n) ?_ ?_
            · rwa [div_mul_cancel₀ _ hqn.ne'] at this
            · have : 1 < t / q ^ n := by rw [one_lt_div hqn]; exact ht1
              have : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
              linarith
            · rw [div_le_iff₀ hqn, ← _root_.pow_succ']
              exact h2
          · by_cases ht2 : t < (q ^ n)⁻¹
            · have := hstep (q ^ n)⁻¹ (inv_pos.mpr hqn) (ih _ le_rfl (hqn2.trans hqn1))
                (t * q ^ n) ?_ ?_
              · rwa [mul_assoc, mul_inv_cancel₀ hqn.ne', mul_one] at this
              · rw [_root_.pow_succ', mul_inv] at h1
                calc q⁻¹ = q⁻¹ * (q ^ n)⁻¹ * q ^ n := by field_simp
                  _ ≤ t * q ^ n := by gcongr
              · have : t * q ^ n < 1 := by
                  calc t * q ^ n < (q ^ n)⁻¹ * q ^ n := by gcongr
                    _ = 1 := inv_mul_cancel₀ hqn.ne'
                linarith
            · exact ih t (not_lt.mp ht2) (not_lt.mp ht1)
      intro t ht
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max t t⁻¹) hq1
      apply hind n t
      · have : t⁻¹ < q ^ n := lt_of_le_of_lt (le_max_right _ _) hn
        rw [inv_le_comm₀ (pow_pos hq0 n) ht]
        exact this.le
      · exact (le_max_left _ _).trans hn.le
    -- integrate along rays: `f (t • x) = f x + ⟪∇f x, x⟫ log t`
    have hlog : ∀ x ∈ Df, ∀ t : ℝ, 0 < t →
        f (t • x) = f x + inner ℝ (gradient f x) x * Real.log t := by
      intro x hx
      have hk : ∀ s : ℝ,
          HasDerivAt (fun s => f (Real.exp s • x) - inner ℝ (gradient f x) x * s) 0 s := by
        intro s
        have hes : Real.exp s • x ∈ Df := hcone x hx _ (Real.exp_pos s)
        have h1 : HasDerivAt (fun s => Real.exp s • x) (Real.exp s • x) s :=
          (Real.hasDerivAt_exp s).smul_const x
        have h2 := (hf_diff _ hes).hasFDerivAt.comp_hasDerivAt s h1
        have h3 : fderiv ℝ f (Real.exp s • x) (Real.exp s • x) = inner ℝ (gradient f x) x := by
          rw [← hinner_grad, hg x hx _ (Real.exp_pos s), inner_smul_left, inner_smul_right]
          simp
        rw [h3] at h2
        have h4 := h2.sub ((hasDerivAt_id s).const_mul (inner ℝ (gradient f x) x))
        simpa using h4
      intro t ht
      have := is_const_of_deriv_eq_zero (fun s => (hk s).differentiableAt)
        (fun s => (hk s).deriv) (Real.log t) 0
      simp [Real.exp_log ht] at this
      linarith
    -- `⟪∇f x, x⟫` is constant on `Df`
    have hconst : ∀ x ∈ Df, ∀ y ∈ Df,
        inner ℝ (gradient f x) x = inner ℝ (gradient f y) y := by
      intro x hx y hy
      have ht : 0 < Real.exp 1 := Real.exp_pos 1
      have hF : ∀ z ∈ Df, HasFDerivAt (fun z => f (Real.exp 1 • z) - f z) (0 : E →L[ℝ] ℝ) z := by
        intro z hz
        have h1 : HasFDerivAt (fun y => f (Real.exp 1 • y))
            ((fderiv ℝ f (Real.exp 1 • z)).comp (Real.exp 1 • ContinuousLinearMap.id ℝ E)) z :=
          (hf_diff _ (hcone z hz _ ht)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul _)
        have h2 := h1.sub (hf_diff z hz).hasFDerivAt
        convert h2 using 1
        ext v
        simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply]
        rw [← hinner_grad, ← hinner_grad, hg z hz _ ht, inner_smul_left, inner_smul_right]
        simp
      have := h_Df_open.is_const_of_fderiv_eq_zero h_Df_convex.isPreconnected
        (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hF z hz).fderiv) hx hy
      simp only at this
      rw [hlog x hx _ ht, hlog y hy _ ht, Real.log_exp] at this
      linarith
    -- the barrier integrand equals `-⟪∇f x, x⟫`
    have hbi : ∀ x (hx : x ∈ Df),
        barrierIntegrand f Df h_Df_pd ⟨x, hx⟩ = -inner ℝ (gradient f x) x := by
      intro x hx
      have hLG : localGradient f Df h_Df_pd x x hx = -x := by
        unfold localGradient
        rw [ContinuousLinearEquiv.symm_apply_eq]
        show gradient f x = hessianOperator f x (-x)
        rw [map_neg, hHx x hx, neg_neg]
      unfold barrierIntegrand
      simp only
      rw [hLG]
      unfold localNorm
      rw [Real.sq_sqrt]
      · unfold localInnerProd
        rw [map_neg, hHx x hx, neg_neg, inner_neg_left, real_inner_comm]
      · by_cases h0 : x = 0
        · subst h0
          simp [localInnerProd]
        · exact (h_Df_pd x hx (-x) (neg_ne_zero.mpr h0)).le
    rcases Df.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
    · subst hempty
      refine ⟨⟨hf_sc, ⟨0, ?_⟩⟩, ∅, by simp, by simp [IsCone], by simp⟩
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      simp at hx
    · set θ := -inner ℝ (gradient f x₀) x₀ with hθdef
      have hrange : ∀ x : Df, barrierIntegrand f Df h_Df_pd x = θ := by
        rintro ⟨x, hx⟩
        rw [hbi x hx, hconst x hx x₀ hx₀]
      have hθ : barrierParameter f Df h_Df_pd = θ := by
        unfold barrierParameter
        apply IsGreatest.csSup_eq
        refine ⟨⟨⟨x₀, hx₀⟩, hrange _⟩, ?_⟩
        rintro _ ⟨x, rfl⟩
        exact (hrange x).le
      refine ⟨⟨hf_sc, ⟨θ, ?_⟩⟩, Df, h_Df_open.interior_eq.symm,
        fun x hx t ht => hcone x hx t ht, ?_⟩
      · rintro _ ⟨x, rfl⟩
        exact (hrange x).le
      · intro x hx t ht
        rw [h_Df_open.interior_eq] at hx
        rw [hθ, hlog x hx t ht, hconst x hx x₀ hx₀, hθdef]
        ring

end Renegar_chap_2_2_3_9_i
