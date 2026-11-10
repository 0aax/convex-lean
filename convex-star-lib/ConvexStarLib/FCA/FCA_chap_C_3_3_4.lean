import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_3_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_3_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_3_4`, so the main result is `FCA_chap_C_3_3_4.FCA_chap_C_3_3_4`.
-/

namespace FCA_chap_C_3_3_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A closed convex set contains every point satisfying all the linear inequalities
satisfied by the set. -/
lemma FCA_aux_mem_of_forall_inner_le {S : Set F} (hS_closed : IsClosed S)
    (hS_convex : Convex ℝ S) (q : F)
    (h : ∀ (y : F) (t : ℝ), (∀ v ∈ S, inner ℝ v y ≤ t) → inner ℝ q y ≤ t) : q ∈ S := by
  by_contra hq
  obtain ⟨f, u, hfS, hfq⟩ := geometric_hahn_banach_closed_point hS_convex hS_closed hq
  have key : ∀ z : F, inner ℝ z ((InnerProductSpace.toDual ℝ F).symm f) = f z := by
    intro z
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have h1 := h ((InnerProductSpace.toDual ℝ F).symm f) u
    (fun v hv => by rw [key]; exact (hfS v hv).le)
  rw [key] at h1
  linarith

/-- The support function of `(A*)⁻¹(S)` is below the closure of the image function. -/
lemma FCA_aux_le (A : F →ₗ[ℝ] E) (S : Set F) (x : E) :
    supportFunction {p : E | ∃ d ∈ S, A.adjoint p = d} x ≤
      lscHull (imageFun A (supportFunction S)) x := by
  apply sSup_le
  rintro _ ⟨p, ⟨d, hdS, hpd⟩, rfl⟩
  have hle : ∀ x' : E, ((inner ℝ p x' : ℝ) : EReal) ≤ imageFun A (supportFunction S) x' := by
    intro x'
    apply le_sInf
    rintro _ ⟨y, hy, rfl⟩
    have hy' : A y = x' := hy
    apply le_sSup
    refine ⟨d, hdS, ?_⟩
    simp only
    rw [← hpd, LinearMap.adjoint_inner_left, hy']
  have htend : Filter.Tendsto (fun x' : E => ((inner ℝ p x' : ℝ) : EReal)) (𝓝 x)
      (𝓝 ((inner ℝ p x : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp (continuous_const.inner continuous_id)).tendsto x
  calc ((inner ℝ p x : ℝ) : EReal)
      = Filter.liminf (fun x' : E => ((inner ℝ p x' : ℝ) : EReal)) (𝓝 x) :=
        htend.liminf_eq.symm
    _ ≤ Filter.liminf (imageFun A (supportFunction S)) (𝓝 x) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)

/-- The closure of the image function is below the support function of `(A*)⁻¹(S)`. -/
lemma FCA_aux_ge (A : F →ₗ[ℝ] E) (S : Set F) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    (hP : {p : E | ∃ d ∈ S, A.adjoint p = d}.Nonempty) (x : E) :
    lscHull (imageFun A (supportFunction S)) x ≤
      supportFunction {p : E | ∃ d ∈ S, A.adjoint p = d} x := by
  set P := {p : E | ∃ d ∈ S, A.adjoint p = d} with hPdef
  have main : ∀ r : ℝ, (r : EReal) < lscHull (imageFun A (supportFunction S)) x →
      ∃ p ∈ P, r < inner ℝ p x := by
    intro r hr
    obtain ⟨r', hrr', hr'L⟩ := EReal.lt_iff_exists_real_btwn.mp hr
    have hev : ∀ᶠ x' in 𝓝 x, (r' : EReal) < imageFun A (supportFunction S) x' :=
      Filter.eventually_lt_of_lt_liminf hr'L
    set C : Set (E × ℝ) := {z | ∃ y : F, A y = z.1 ∧ ∀ v ∈ S, inner ℝ v y ≤ z.2} with hC
    have hCconv : Convex ℝ C := by
      rintro ⟨x1, t1⟩ ⟨y1, hy1A, hy1S⟩ ⟨x2, t2⟩ ⟨y2, hy2A, hy2S⟩ a b ha hb hab
      refine ⟨a • y1 + b • y2, ?_, ?_⟩
      · simp only [Prod.smul_mk, Prod.mk_add_mk, map_add, map_smul]
        simp only at hy1A hy2A
        rw [hy1A, hy2A]
      · intro v hv
        simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, inner_add_right,
          real_inner_smul_right]
        have h1 := hy1S v hv
        have h2 := hy2S v hv
        simp only at h1 h2
        nlinarith
    have hnot : ((x, r) : E × ℝ) ∉ closure C := by
      rw [mem_closure_iff_nhds]
      push_neg
      refine ⟨{x' | (r' : EReal) < imageFun A (supportFunction S) x'} ×ˢ Set.Iio r', ?_, ?_⟩
      · exact prod_mem_nhds hev (Iio_mem_nhds (by exact_mod_cast hrr'))
      · rw [Set.eq_empty_iff_forall_notMem]
        rintro ⟨x', t⟩ ⟨⟨hx', ht⟩, ⟨y, hyA, hyS⟩⟩
        simp only [Set.mem_setOf_eq, Set.mem_Iio] at hx' ht hyA hyS
        apply absurd hx'
        rw [not_lt]
        calc imageFun A (supportFunction S) x' ≤ supportFunction S y := by
              apply sInf_le
              exact ⟨y, hyA, rfl⟩
          _ ≤ (t : EReal) := by
              apply sSup_le
              rintro _ ⟨v, hv, rfl⟩
              exact EReal.coe_le_coe_iff.mpr (hyS v hv)
          _ ≤ r' := by exact_mod_cast ht.le
    obtain ⟨f, u, hfC, hfx⟩ :=
      geometric_hahn_banach_closed_point hCconv.closure isClosed_closure hnot
    have hfC' : ∀ z ∈ C, f z < u := fun z hz => hfC z (subset_closure hz)
    have h0C : ((0 : E), (0 : ℝ)) ∈ C := ⟨0, by simp, fun v _ => by simp⟩
    have hu : 0 < u := by
      have := hfC' _ h0C
      have h00 : ((0 : E), (0 : ℝ)) = (0 : E × ℝ) := rfl
      rw [h00, map_zero] at this
      exact this
    have hcone : ∀ z ∈ C, f z ≤ 0 := by
      intro z hz
      by_contra hpos
      push_neg at hpos
      have hcz : ((2 * u / f z) • z) ∈ C := by
        obtain ⟨y, hyA, hyS⟩ := hz
        refine ⟨(2 * u / f z) • y, ?_, ?_⟩
        · simp [hyA]
        · intro v hv
          simp only [Prod.smul_snd, smul_eq_mul, real_inner_smul_right]
          have := hyS v hv
          have hc : 0 ≤ 2 * u / f z := by positivity
          exact mul_le_mul_of_nonneg_left this hc
      have := hfC' _ hcz
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    set α := f ((0 : E), (1 : ℝ)) with hα
    have h01C : ((0 : E), (1 : ℝ)) ∈ C := ⟨0, by simp, fun v _ => by simp⟩
    have hα0 : α ≤ 0 := hcone _ h01C
    set q := (InnerProductSpace.toDual ℝ E).symm (f.comp (ContinuousLinearMap.inl ℝ E ℝ))
      with hq
    have hfdecomp : ∀ (x' : E) (t : ℝ), f (x', t) = inner ℝ q x' + t * α := by
      intro x' t
      have : ((x', t) : E × ℝ) = (x', 0) + t • ((0 : E), (1 : ℝ)) := by simp
      rw [this, map_add, map_smul, smul_eq_mul, hq, InnerProductSpace.toDual_symm_apply]
      simp [hα]
    have hkey : ∀ (y : F) (t : ℝ), (∀ v ∈ S, inner ℝ v y ≤ t) →
        inner ℝ q (A y) + t * α ≤ 0 := by
      intro y t hyt
      rw [← hfdecomp]
      exact hcone _ ⟨y, rfl, hyt⟩
    have hxr : 0 < inner ℝ q x + r * α := by
      rw [← hfdecomp]; linarith
    have hpex : ∃ p : E, (∀ (y : F) (t : ℝ), (∀ v ∈ S, inner ℝ v y ≤ t) →
        inner ℝ p (A y) ≤ t) ∧ r < inner ℝ p x := by
      rcases hα0.lt_or_eq with hαneg | hαzero
      · refine ⟨(-α)⁻¹ • q, ?_, ?_⟩
        · intro y t hyt
          have := hkey y t hyt
          rw [real_inner_smul_left, inv_mul_le_iff₀ (by linarith)]
          linarith
        · rw [real_inner_smul_left, lt_inv_mul_iff₀ (by linarith)]
          linarith
      · obtain ⟨p₀, d₀, hd₀S, hp₀d⟩ := hP
        have hqx : 0 < inner ℝ q x := by rw [hαzero] at hxr; simpa using hxr
        obtain ⟨n, hn⟩ := exists_nat_gt ((r - inner ℝ p₀ x) / inner ℝ q x)
        refine ⟨p₀ + (n : ℝ) • q, ?_, ?_⟩
        · intro y t hyt
          have h1 := hkey y t hyt
          rw [hαzero, mul_zero, add_zero] at h1
          have h2 : inner ℝ p₀ (A y) ≤ t := by
            rw [← LinearMap.adjoint_inner_left, hp₀d]
            exact hyt d₀ hd₀S
          rw [inner_add_left, real_inner_smul_left]
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        · rw [inner_add_left, real_inner_smul_left]
          rw [div_lt_iff₀ hqx] at hn
          linarith
    obtain ⟨p, hp1, hp2⟩ := hpex
    refine ⟨p, ⟨A.adjoint p, ?_, rfl⟩, hp2⟩
    apply FCA_aux_mem_of_forall_inner_le hS_closed hS_convex
    intro y t hyt
    rw [LinearMap.adjoint_inner_left]
    exact hp1 y t hyt
  by_contra hlt
  push_neg at hlt
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨p, hp, hpr⟩ := main r hr2
  have h1 : ((inner ℝ p x : ℝ) : EReal) ≤ supportFunction P x := by
    apply le_sSup
    exact ⟨p, hp, rfl⟩
  have h2 : (r : EReal) < supportFunction P x :=
    lt_of_lt_of_le (by exact_mod_cast hpr) h1
  exact absurd (hr1.trans h2) (lt_irrefl _)

set_option linter.unusedVariables false in
theorem FCA_chap_C_3_3_4
  (A : F →ₗ[ℝ] E)
  (S : Set F)
  (hS_nonempty : Set.Nonempty S)
  (hS_closed : IsClosed S)
  (hS_convex : Convex ℝ S) :
  let A_star := A.adjoint
  let σ := supportFunction S
  let A_adj_inv_S :=
    {p : E |
      ∃ d ∈ S, A_star p = d}
  let σ_adj_inv := supportFunction A_adj_inv_S
  A_adj_inv_S.Nonempty →
  (∀ (d : E),
    imageFun A σ d > ⊥) →
  (∀ (x : E),
    (σ_adj_inv x) =
    lscHull (imageFun A σ) x) := by
  intro A_star σ A_adj_inv_S σ_adj_inv hP _ x
  exact le_antisymm (FCA_aux_le A S x) (FCA_aux_ge A S hS_closed hS_convex hP x)

end FCA_chap_C_3_3_4
