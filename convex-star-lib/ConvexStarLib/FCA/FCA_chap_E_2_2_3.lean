import ConvexStarLib.Defs

/-!
# `FCA_chap_E_2_2_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_2_2_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_2_2_3`, so the main result is `FCA_chap_E_2_2_3.FCA_chap_E_2_2_3`.
-/

namespace FCA_chap_E_2_2_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma exists_adjoint_eq_of_orth (A : E →ₗ[ℝ] F) (s : E)
    (hs : ∀ u, A u = 0 → inner ℝ s u = 0) :
    ∃ p : F, A.adjoint p = s := by
  have hmem : s ∈ (LinearMap.range A.adjoint)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hAu : A u = 0 := by
      rw [Submodule.mem_orthogonal] at hu
      have h := hu (A.adjoint (A u)) (LinearMap.mem_range_self _ _)
      rw [LinearMap.adjoint_inner_left] at h
      exact inner_self_eq_zero.mp h
    rw [real_inner_comm]
    exact hs u hAu
  rw [Submodule.orthogonal_orthogonal] at hmem
  exact hmem

omit [FiniteDimensional ℝ F] in
lemma ri_ball {D : Set F} {y₁ : F} (hy₁ : y₁ ∈ intrinsicInterior ℝ D) :
    ∃ ε > 0, ∀ q ∈ affineSpan ℝ D, dist q y₁ < ε → q ∈ D := by
  rw [mem_intrinsicInterior] at hy₁
  obtain ⟨y, hy, rfl⟩ := hy₁
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
  obtain ⟨ε, hε, hball⟩ := hy
  refine ⟨ε, hε, fun q hq hdist => ?_⟩
  have : (⟨q, hq⟩ : affineSpan ℝ D) ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    exact hdist
  exact hball this

lemma EReal_exists_coe {x : EReal} (h1 : ⊥ < x) (h2 : x < ⊤) : ∃ γ : ℝ, x = γ :=
  ⟨x.toReal, (EReal.coe_toReal h2.ne h1.ne').symm⟩

lemma core_sep (g : F → EReal) (hbot : ∀ y, ⊥ < g y)
    (hconv : Convex ℝ {q : F × ℝ | g q.1 ≤ q.2})
    (A : E →ₗ[ℝ] F) (y₁ : F) (hy₁ : y₁ ∈ intrinsicInterior ℝ {y | g y < ⊤})
    (s : E) (c : ℝ)
    (hmin : ∀ u : E, ∀ γ : ℝ, g (y₁ + A u) = γ → c + inner ℝ s u ≤ γ) :
    ∃ p : F, A.adjoint p = s ∧ ∀ w : F, ∀ γ : ℝ, g (y₁ + w) = γ → c + inner ℝ p w ≤ γ := by
  set D : Set F := {y | g y < ⊤} with hD
  have hy₁D : y₁ ∈ D := intrinsicInterior_subset hy₁
  obtain ⟨γ₁, hγ₁⟩ := EReal_exists_coe (hbot y₁) hy₁D
  -- s ⊥ ker A
  have hsker : ∀ u, A u = 0 → inner ℝ s u = 0 := by
    intro u hu
    by_contra hne
    have key : ∀ τ : ℝ, c + τ * inner ℝ s u ≤ γ₁ := by
      intro τ
      have := hmin (τ • u) γ₁ (by simp [hu, hγ₁])
      simpa [real_inner_smul_right] using this
    have := key ((γ₁ - c + 1) / inner ℝ s u)
    field_simp at this
    linarith
  obtain ⟨p₀, hp₀⟩ := exists_adjoint_eq_of_orth A s hsker
  -- subspaces
  set V : Submodule ℝ F := (affineSpan ℝ D).direction with hV
  set W : Submodule ℝ F := V ⊔ LinearMap.range A with hW
  set Z : Submodule ℝ F := Wᗮ with hZ
  set S : Submodule ℝ (F × ℝ) := Submodule.prod (LinearMap.range A ⊔ Z) ⊤ with hS
  let L : F × ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun q => q.2 - inner ℝ p₀ q.1
      map_add' := by intro a b; simp [inner_add_right]; ring
      map_smul' := by intro a b; simp [inner_smul_right]; ring }
  let K : ConvexCone ℝ (F × ℝ) :=
    { carrier := {q | ∃ t : ℝ, 0 < t ∧ g (y₁ + t⁻¹ • q.1) ≤ ((t⁻¹ * q.2 + c : ℝ) : EReal)}
      smul_mem' := by
        rintro a ha ⟨w, r⟩ ⟨t, ht, hle⟩
        refine ⟨a * t, mul_pos ha ht, ?_⟩
        have e1 : (a * t)⁻¹ • (a • w) = t⁻¹ • w := by
          rw [smul_smul]; congr 1; field_simp
        have e2 : (a * t)⁻¹ * (a * r) = t⁻¹ * r := by field_simp
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        rw [e1, e2]
        exact hle
      add_mem' := by
        rintro ⟨w₁, r₁⟩ ⟨t₁, ht₁, h₁⟩ ⟨w₂, r₂⟩ ⟨t₂, ht₂, h₂⟩
        refine ⟨t₁ + t₂, by positivity, ?_⟩
        have hm1 : (y₁ + t₁⁻¹ • w₁, t₁⁻¹ * r₁ + c) ∈ {q : F × ℝ | g q.1 ≤ q.2} := h₁
        have hm2 : (y₁ + t₂⁻¹ • w₂, t₂⁻¹ * r₂ + c) ∈ {q : F × ℝ | g q.1 ≤ q.2} := h₂
        have hT : 0 < t₁ + t₂ := by positivity
        have := hconv hm1 hm2 (a := t₁ / (t₁ + t₂)) (b := t₂ / (t₁ + t₂))
          (by positivity) (by positivity) (by field_simp)
        have heq : (t₁ / (t₁ + t₂)) • (y₁ + t₁⁻¹ • w₁, t₁⁻¹ * r₁ + c) +
            (t₂ / (t₁ + t₂)) • (y₁ + t₂⁻¹ • w₂, t₂⁻¹ * r₂ + c) =
            (y₁ + (t₁ + t₂)⁻¹ • (w₁ + w₂), (t₁ + t₂)⁻¹ * (r₁ + r₂) + c) := by
          ext
          · simp only [Prod.fst_add, Prod.smul_fst]
            match_scalars <;> field_simp
          · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
            field_simp
            ring
        rw [heq] at this
        exact this }
  have hnonneg : ∀ x : (L.toPMap S).domain, (x : F × ℝ) ∈ K → 0 ≤ (L.toPMap S) x := by
    rintro ⟨⟨w, r⟩, hx⟩ ⟨t, ht, hle⟩
    have hw : w ∈ LinearMap.range A ⊔ Z := (Submodule.mem_prod.mp hx).1
    obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hm
    simp only at hle
    have hlt : y₁ + t⁻¹ • (A u + z) ∈ D := lt_of_le_of_lt hle (EReal.coe_lt_top _)
    have hmemV : t⁻¹ • (A u + z) ∈ V := by
      have h1 : y₁ + t⁻¹ • (A u + z) ∈ affineSpan ℝ D := mem_affineSpan ℝ hlt
      have h2 : y₁ ∈ affineSpan ℝ D := mem_affineSpan ℝ hy₁D
      have := AffineSubspace.vsub_mem_direction h1 h2
      simpa using this
    have hmemV' : A u + z ∈ V := by
      have := V.smul_mem t hmemV
      rwa [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at this
    have hzW : z ∈ W := by
      have : z = (A u + z) - A u := by abel
      rw [this]
      exact W.sub_mem (Submodule.mem_sup_left hmemV')
        (Submodule.mem_sup_right (LinearMap.mem_range_self A u))
    have hz0 : z = 0 := by
      have := (Submodule.mem_orthogonal W z).mp hz z hzW
      exact inner_self_eq_zero.mp this
    subst hz0
    simp only [add_zero] at hle hlt
    rw [← map_smul] at hle hlt
    obtain ⟨γ, hγ⟩ := EReal_exists_coe (hbot _) hlt
    have h1 := hmin (t⁻¹ • u) γ hγ
    rw [hγ] at hle
    have h2 : γ ≤ t⁻¹ * r + c := EReal.coe_le_coe_iff.mp hle
    rw [LinearMap.toPMap_apply]
    show 0 ≤ r - inner ℝ p₀ (A u + 0)
    rw [add_zero, ← LinearMap.adjoint_inner_left, hp₀]
    rw [real_inner_smul_right] at h1
    have h3 : 0 ≤ t⁻¹ * (r - inner ℝ s u) := by nlinarith
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr ht)).mp h3
  have hdense : ∀ y : F × ℝ, ∃ x : (L.toPMap S).domain, (x : F × ℝ) + y ∈ K := by
    rintro ⟨w, r⟩
    have hwtop : w ∈ W ⊔ Wᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp hwtop
    obtain ⟨v, hv, m, hm, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨ε, hε, hball⟩ := ri_ball hy₁
    set t : ℝ := (‖v‖ + 1) / ε with ht_def
    have ht : 0 < t := by positivity
    have hq : y₁ + t⁻¹ • v ∈ D := by
      apply hball
      · have : t⁻¹ • v ∈ V := V.smul_mem _ hv
        have h2 := AffineSubspace.vadd_mem_of_mem_direction this (mem_affineSpan ℝ hy₁D)
        rwa [vadd_eq_add, add_comm] at h2
      · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr ht), ht_def, inv_div]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg v]
    obtain ⟨γ', hγ'⟩ := EReal_exists_coe (hbot _) hq
    refine ⟨⟨(-(m + z), t * (γ' - c) - r), ?_⟩, ?_⟩
    · refine Submodule.mem_prod.mpr ⟨?_, trivial⟩
      exact Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left hm)
        (Submodule.mem_sup_right hz))
    · refine ⟨t, ht, ?_⟩
      have e1 : -(m + z) + (v + m + z) = v := by abel
      have e2 : t⁻¹ * (t * (γ' - c) - r + r) + c = γ' := by field_simp; ring
      simp only [Prod.mk_add_mk, e1, e2]
      rw [hγ']
  obtain ⟨G, hGf, hGK⟩ := riesz_extension K (L.toPMap S) hnonneg hdense
  have hG01 : G (0, 1) = 1 := by
    have := hGf ⟨(0, 1), Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, trivial⟩⟩
    rw [this, LinearMap.toPMap_apply]
    show (1 : ℝ) - inner ℝ p₀ (0 : F) = 1
    simp
  let G₀ : F →ₗ[ℝ] ℝ := G.comp (LinearMap.inl ℝ F ℝ)
  set p : F := -(InnerProductSpace.toDual ℝ F).symm (LinearMap.toContinuousLinearMap G₀) with hp
  have hpw : ∀ w, inner ℝ p w = - G (w, 0) := by
    intro w
    rw [hp, inner_neg_left, InnerProductSpace.toDual_symm_apply,
      LinearMap.coe_toContinuousLinearMap']
    simp [G₀]
  have hGsplit : ∀ w r, G (w, r) = r - inner ℝ p w := by
    intro w r
    have : ((w, r) : F × ℝ) = (w, 0) + r • ((0 : F), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, hG01, hpw]
    simp only [smul_eq_mul, mul_one]
    ring
  refine ⟨p, ?_, ?_⟩
  · apply ext_inner_right ℝ
    intro u
    rw [LinearMap.adjoint_inner_left, hpw]
    have := hGf ⟨(A u, 0), Submodule.mem_prod.mpr
      ⟨Submodule.mem_sup_left (LinearMap.mem_range_self A u), trivial⟩⟩
    rw [LinearMap.toPMap_apply] at this
    rw [this]
    show -((0 : ℝ) - inner ℝ p₀ (A u)) = inner ℝ s u
    rw [← LinearMap.adjoint_inner_left, hp₀]
    ring
  · intro w γ hγ
    have hK : ((w, γ - c) : F × ℝ) ∈ K := by
      refine ⟨1, one_pos, ?_⟩
      simp only [inv_one, one_smul, one_mul, sub_add_cancel]
      rw [hγ]
    have := hGK _ hK
    rw [hGsplit] at this
    linarith

lemma EReal_top_or_coe {x : EReal} (h : ⊥ < x) : x = ⊤ ∨ ∃ γ : ℝ, x = γ := by
  rcases eq_or_ne x ⊤ with h' | h'
  · exact Or.inl h'
  · exact Or.inr ⟨x.toReal, (EReal.coe_toReal h' h.ne').symm⟩

set_option linter.unusedVariables false in
theorem FCA_chap_E_2_2_3
  (g : F → EReal)
  (y₀ : F)
  (A₀ : E →ₗ[ℝ] F)
  (hg_closed_convex : InClosedConvRn g)
  (hg_nondegenerate : IsNondegenerate g)
  (h_zero : 0 ∈ effDom g)
  (h_nonempty_domain : Set.Nonempty ((Set.image (fun v => A₀ v + y₀) Set.univ) ∩
    (intrinsicInterior ℝ (effDom g)))) :
  let gA := fun x => g (A₀ x + y₀)
  let A_star_g_star := imageFun A₀.adjoint (conjugate g)
  ∀ s ∈ effDom ((conjugate gA)), ∃ p',
  (A₀.adjoint p' = s) ∧
  ((conjugate g p') - inner ℝ p' y₀ =
  imageFun A₀.adjoint (fun p => conjugate g p - inner ℝ p y₀) s) ∧
  ((conjugate gA s) = (conjugate g p') - inner ℝ p' y₀) := by
  intro gA A_star_g_star s hs
  obtain ⟨⟨hbot, -, hconv⟩, -⟩ := hg_closed_convex
  obtain ⟨y₁, ⟨x₁, -, hx₁⟩, hy₁⟩ := h_nonempty_domain
  simp only at hx₁
  -- weak duality
  have weak : ∀ q : F, A₀.adjoint q = s →
      conjugate gA s ≤ conjugate g q - ((inner ℝ q y₀ : ℝ) : EReal) := by
    intro q hq
    apply sSup_le
    rintro _ ⟨x, -, rfl⟩
    have hle : ((inner ℝ q (A₀ x + y₀) : ℝ) : EReal) - g (A₀ x + y₀) ≤ conjugate g q :=
      le_sSup ⟨A₀ x + y₀, Set.mem_univ _, rfl⟩
    have hsx : inner ℝ s x = inner ℝ q (A₀ x + y₀) - inner ℝ q y₀ := by
      rw [← hq, LinearMap.adjoint_inner_left, inner_add_right]; ring
    show ((inner ℝ s x : ℝ) : EReal) - g (A₀ x + y₀) ≤ conjugate g q - ((inner ℝ q y₀ : ℝ) : EReal)
    rcases EReal_top_or_coe (hbot (A₀ x + y₀)) with h | ⟨γ, h⟩
    · rw [h, EReal.sub_top]; exact bot_le
    · rw [h] at hle ⊢
      rw [hsx]
      calc ((inner ℝ q (A₀ x + y₀) - inner ℝ q y₀ : ℝ) : EReal) - γ
          = (((inner ℝ q (A₀ x + y₀) : ℝ) : EReal) - γ) - ((inner ℝ q y₀ : ℝ) : EReal) := by
            rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]; congr 1; ring
        _ ≤ conjugate g q - ((inner ℝ q y₀ : ℝ) : EReal) := EReal.sub_le_sub hle le_rfl
  -- finiteness of the conjugate at s
  have hy₁D : y₁ ∈ effDom g := intrinsicInterior_subset hy₁
  obtain ⟨γ₁, hγ₁⟩ := EReal_exists_coe (hbot y₁) hy₁D
  have hlow : ((inner ℝ s x₁ - γ₁ : ℝ) : EReal) ≤ conjugate gA s := by
    apply le_sSup
    refine ⟨x₁, Set.mem_univ _, ?_⟩
    show ((inner ℝ s x₁ : ℝ) : EReal) - g (A₀ x₁ + y₀) = _
    rw [hx₁, hγ₁]; rfl
  obtain ⟨α, hα⟩ := EReal_exists_coe (lt_of_lt_of_le (EReal.bot_lt_coe _) hlow) hs
  have hmin : ∀ u : E, ∀ γ : ℝ, g (y₁ + A₀ u) = γ →
      (inner ℝ s x₁ - α) + inner ℝ s u ≤ γ := by
    intro u γ hγ
    have hle : ((inner ℝ s (x₁ + u) : ℝ) : EReal) - gA (x₁ + u) ≤ conjugate gA s :=
      le_sSup ⟨x₁ + u, Set.mem_univ _, rfl⟩
    have hgA : gA (x₁ + u) = γ := by
      show g (A₀ (x₁ + u) + y₀) = γ
      rw [map_add, add_right_comm, hx₁]; exact hγ
    rw [hgA, hα, ← EReal.coe_sub, EReal.coe_le_coe_iff, inner_add_right] at hle
    linarith
  obtain ⟨p, hpA, hp⟩ := core_sep g hbot hconv A₀ y₁ hy₁ s (inner ℝ s x₁ - α) hmin
  have hupper : conjugate g p ≤ ((α + inner ℝ p y₀ : ℝ) : EReal) := by
    apply sSup_le
    rintro _ ⟨y, -, rfl⟩
    show ((inner ℝ p y : ℝ) : EReal) - g y ≤ _
    rcases EReal_top_or_coe (hbot y) with h | ⟨γ, h⟩
    · rw [h, EReal.sub_top]; exact bot_le
    · rw [h, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := hp (y - y₁) γ (by rw [add_sub_cancel]; exact h)
      have e : inner ℝ s x₁ = inner ℝ p (A₀ x₁) := by
        rw [← hpA, LinearMap.adjoint_inner_left]
      rw [inner_sub_right, ← hx₁, inner_add_right, e] at this
      linarith
  have hval : conjugate g p - ((inner ℝ p y₀ : ℝ) : EReal) = conjugate gA s := by
    apply le_antisymm
    · rw [hα]
      calc conjugate g p - ((inner ℝ p y₀ : ℝ) : EReal)
          ≤ ((α + inner ℝ p y₀ : ℝ) : EReal) - ((inner ℝ p y₀ : ℝ) : EReal) :=
            EReal.sub_le_sub hupper le_rfl
        _ = α := by rw [← EReal.coe_sub]; congr 1; ring
    · exact weak p hpA
  refine ⟨p, hpA, ?_, hval.symm⟩
  rw [hval]
  unfold imageFun
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨q, hq, rfl⟩
    exact weak q hq
  · rw [← hval]
    apply sInf_le
    exact ⟨p, hpA, rfl⟩

end FCA_chap_E_2_2_3
