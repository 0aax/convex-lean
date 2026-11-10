import ConvexStarLib.Defs

/-!
# `FCA_chap_E_2_3_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_2_3_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_2_3_2`, so the main result is `FCA_chap_E_2_3_2.FCA_chap_E_2_3_2`.
-/

namespace FCA_chap_E_2_3_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedSectionVars false

lemma aux_toReal_le {x : EReal} {r : ℝ} (h : x ≤ r) (hb : x ≠ ⊥) : x.toReal ≤ r := by
  have := EReal.toReal_le_toReal h hb (EReal.coe_ne_top r)
  simpa using this

lemma aux_conv_ineq {g : E → EReal} (hc : ConvexEReal g) {x y : E} {a b : ℝ}
    (hx : g x ≤ a) (hy : g y ≤ b) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (htu : t + u = 1) :
    g (t • x + u • y) ≤ ((t * a + u * b : ℝ) : EReal) := by
  have h1 : (x, a) ∈ epigraph g := hx
  have h2 : (y, b) ∈ epigraph g := hy
  have := hc h1 h2 ht hu htu
  simpa [epigraph] using this

lemma aux_ri_ball {s : Set E} {a : E} (ha : a ∈ intrinsicInterior ℝ s) :
    ∃ ε > 0, ∀ z ∈ affineSpan ℝ s, dist z a < ε → z ∈ s := by
  rw [mem_intrinsicInterior] at ha
  obtain ⟨y, hy, rfl⟩ := ha
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
  obtain ⟨ε, hε, hball⟩ := hy
  refine ⟨ε, hε, fun z hz hdist => ?_⟩
  have : (⟨z, hz⟩ : affineSpan ℝ s) ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    exact hdist
  exact hball this

lemma aux_ri_bdd {g : E → EReal} (hbot : ∀ x, ⊥ < g x) (hc : ConvexEReal g) {a : E}
    (ha : a ∈ intrinsicInterior ℝ (effDom g)) :
    ∃ δ > 0, ∃ M : ℝ, ∀ v ∈ (affineSpan ℝ (effDom g)).direction, ‖v‖ < δ → g (a + v) ≤ M := by
  set V := (affineSpan ℝ (effDom g)).direction with hV
  have haS : a ∈ affineSpan ℝ (effDom g) := mem_affineSpan ℝ (intrinsicInterior_subset ha)
  obtain ⟨ε, hε, hball⟩ := aux_ri_ball ha
  let C : Set V := {v | g (a + (v : E)) < ⊤}
  let f : V → ℝ := fun v => (g (a + (v : E))).toReal
  have hfC : ∀ v ∈ C, g (a + (v : E)) = (f v : EReal) := by
    intro v hv
    exact (EReal.coe_toReal (ne_of_lt hv) (ne_of_gt (hbot _))).symm
  have hconv : ConvexOn ℝ C f := by
    have key : ∀ v ∈ C, ∀ w ∈ C, ∀ t u : ℝ, 0 ≤ t → 0 ≤ u → t + u = 1 →
        g (a + ((t • v + u • w : V) : E)) ≤ ((t * f v + u * f w : ℝ) : EReal) := by
      intro v hv w hw t u ht hu htu
      have e : a + ((t • v + u • w : V) : E) = t • (a + (v : E)) + u • (a + (w : E)) := by
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
        rw [add_add_add_comm, ← add_smul, htu, one_smul]
      rw [e]
      exact aux_conv_ineq hc (hfC v hv).le (hfC w hw).le ht hu htu
    refine ⟨?_, ?_⟩
    · intro v hv w hw t u ht hu htu
      show g (a + ((t • v + u • w : V) : E)) < ⊤
      exact lt_of_le_of_lt (key v hv w hw t u ht hu htu) (EReal.coe_lt_top _)
    · intro v hv w hw t u ht hu htu
      simp only [smul_eq_mul]
      exact aux_toReal_le (key v hv w hw t u ht hu htu) (ne_of_gt (hbot _))
  have hballC : Metric.ball (0 : V) ε ⊆ C := by
    intro v hv
    rw [Metric.mem_ball, _root_.dist_zero_right] at hv
    have hmem : a + (v : E) ∈ affineSpan ℝ (effDom g) := by
      have := AffineSubspace.vadd_mem_of_mem_direction v.2 haS
      rw [vadd_eq_add, add_comm] at this
      exact this
    have hd : dist (a + (v : E)) a < ε := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hv
    exact hball _ hmem hd
  have h0 : (0 : V) ∈ interior C :=
    mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨ε, hε, hballC⟩)
  have hcont : ContinuousAt f 0 :=
    (hconv.continuousOn_interior).continuousAt (isOpen_interior.mem_nhds h0)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  refine ⟨min ε δ₁, lt_min hε hδ₁, f 0 + 1, fun v hv hvn => ?_⟩
  set v' : V := ⟨v, hv⟩
  have hv'C : v' ∈ C := hballC (by
    rw [Metric.mem_ball, _root_.dist_zero_right]
    exact lt_of_lt_of_le hvn (min_le_left _ _))
  have hfv : dist (f v') (f 0) < 1 := hδ₁' (by
    rw [_root_.dist_zero_right]
    exact lt_of_lt_of_le hvn (min_le_right _ _))
  have : g (a + v) = (f v' : EReal) := hfC v' hv'C
  rw [this, EReal.coe_le_coe_iff]
  rw [Real.dist_eq] at hfv
  linarith [le_abs_self (f v' - f 0)]

lemma aux_decomp (V₁ V₂ : Submodule ℝ E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ u ∈ V₁ ⊔ V₂, ‖u‖ < η →
      ∃ v₁ ∈ V₁, ∃ v₂ ∈ V₂, ‖v₁‖ < δ ∧ ‖v₂‖ < δ ∧ u = v₁ + v₂ := by
  let T : (V₁ × V₂) →ₗ[ℝ] E := V₁.subtype.coprod V₂.subtype
  have hT : LinearMap.range T = V₁ ⊔ V₂ := by
    simp [T, LinearMap.range_coprod]
  obtain ⟨S, hS⟩ := T.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict T)
  have hScont : Continuous S := LinearMap.continuous_of_finiteDimensional S
  have hS0 : ContinuousAt S 0 := hScont.continuousAt
  obtain ⟨η, hη, hη'⟩ := Metric.continuousAt_iff.mp hS0 δ hδ
  refine ⟨η, hη, fun u hu hun => ?_⟩
  have hu' : u ∈ LinearMap.range T := by rw [hT]; exact hu
  set w : LinearMap.range T := ⟨u, hu'⟩
  have hw : dist w 0 < η := by rw [_root_.dist_zero_right]; exact hun
  have h1 := hη' hw
  rw [map_zero, _root_.dist_zero_right] at h1
  have h2 : T.rangeRestrict (S w) = w := by
    rw [← LinearMap.comp_apply, hS, LinearMap.id_apply]
  have h3 : T (S w) = u := by
    have := congrArg Subtype.val h2
    simpa using this
  refine ⟨(S w).1, (S w).1.2, (S w).2, (S w).2.2, lt_of_le_of_lt (norm_fst_le (S w)) h1,
    lt_of_le_of_lt (by exact norm_snd_le (S w)) h1, ?_⟩
  rw [← h3]
  simp [T]

lemma aux_EI (g₁ g₂ : E → EReal) (h1 : ∀ x, ⊥ < g₁ x) (h2 : ∀ x, ⊥ < g₂ x) (p q : E) :
    conjugate (g₁ + g₂) (p + q) ≤ conjugate g₁ p + conjugate g₂ q := by
  unfold conjugate
  apply sSup_le
  rintro _ ⟨x, -, rfl⟩
  have hp : ((inner ℝ p x : ℝ) : EReal) - g₁ x ≤
      sSup (Set.image (fun x => ((inner ℝ p x : ℝ) : EReal) - g₁ x) Set.univ) :=
    le_sSup ⟨x, Set.mem_univ _, rfl⟩
  have hq : ((inner ℝ q x : ℝ) : EReal) - g₂ x ≤
      sSup (Set.image (fun x => ((inner ℝ q x : ℝ) : EReal) - g₂ x) Set.univ) :=
    le_sSup ⟨x, Set.mem_univ _, rfl⟩
  refine le_trans ?_ (add_le_add hp hq)
  simp only [Pi.add_apply]
  have ha := h1 x
  have hb := h2 x
  generalize g₁ x = a at ha ⊢
  generalize g₂ x = b at hb ⊢
  induction a using EReal.rec <;> induction b using EReal.rec
  all_goals first
    | exact absurd ha (lt_irrefl _)
    | exact absurd hb (lt_irrefl _)
    | skip
  · rename_i a b
    rw [inner_add_left]
    norm_cast
    linarith
  · simp
  · simp
  · simp

lemma aux_K_convex (g₁ g₂ : E → EReal) (hc1 : ConvexEReal g₁) (hc2 : ConvexEReal g₂)
    (W : Submodule ℝ E) (s : E) :
    Convex ℝ {p : E × ℝ | ∃ x y : E, ∃ a b : ℝ, g₁ x ≤ a ∧ g₂ y ≤ b ∧
      p.1 - (y - x) ∈ W ∧ a + b - inner ℝ s x < p.2} := by
  rintro p ⟨x, y, a, b, hxa, hyb, hWp, hlt⟩ p' ⟨x', y', a', b', hxa', hyb', hWp', hlt'⟩
    t u ht hu htu
  refine ⟨t • x + u • x', t • y + u • y', t * a + u * a', t * b + u * b',
    aux_conv_ineq hc1 hxa hxa' ht hu htu, aux_conv_ineq hc2 hyb hyb' ht hu htu, ?_, ?_⟩
  · have e : (t • p + u • p').1 - ((t • y + u • y') - (t • x + u • x')) =
        t • (p.1 - (y - x)) + u • (p'.1 - (y' - x')) := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_sub]
      abel
    rw [e]
    exact W.add_mem (W.smul_mem t hWp) (W.smul_mem u hWp')
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, inner_add_right, real_inner_smul_right]
    have key : t * (a + b - inner ℝ s x) + u * (a' + b' - inner ℝ s x') < t * p.2 + u * p'.2 := by
      rcases eq_or_lt_of_le ht with h0 | ht'
      · subst h0
        have hu1 : u = 1 := by linarith
        subst hu1
        linarith
      · have h1 := mul_lt_mul_of_pos_left hlt ht'
        have h2 := mul_le_mul_of_nonneg_left hlt'.le hu
        linarith
    linarith

lemma aux_sep (K : Set (E × ℝ)) (hK : Convex ℝ K) (A : ℝ) (hA : ((0 : E), -A) ∉ K)
    (η R : ℝ) (hη : 0 < η) (hU : ∀ p : E × ℝ, ‖p.1‖ < η → R < p.2 → p ∈ K) :
    ∃ ℓ : StrongDual ℝ E, ∃ μ : ℝ, μ < 0 ∧ ∀ p ∈ K, ℓ p.1 + p.2 * μ ≤ -A * μ := by
  have hUopen : IsOpen {p : E × ℝ | ‖p.1‖ < η ∧ R < p.2} := by
    apply IsOpen.inter
    · exact isOpen_lt (continuous_norm.comp continuous_fst) continuous_const
    · exact isOpen_lt continuous_const continuous_snd
  have hUint : ∀ p : E × ℝ, ‖p.1‖ < η → R < p.2 → p ∈ interior K := fun p hp1 hp2 =>
    interior_maximal (fun q hq => hU q hq.1 hq.2) hUopen ⟨hp1, hp2⟩
  have hnotint : ((0 : E), -A) ∉ interior K := fun h => hA (interior_subset h)
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.interior isOpen_interior hnotint
  have hintne : (interior K).Nonempty :=
    ⟨((0 : E), R + 1), hUint _ (by simp [hη]) (by simp)⟩
  have hfK : ∀ p ∈ K, f p ≤ f ((0 : E), -A) := by
    intro p hp
    have hcl : p ∈ closure (interior K) := by
      rw [hK.closure_interior_eq_closure_of_nonempty_interior hintne]
      exact subset_closure hp
    have hsub : closure (interior K) ⊆ {p | f p ≤ f ((0 : E), -A)} :=
      closure_minimal (fun p hp => (hf p hp).le) (isClosed_le f.continuous continuous_const)
    exact hsub hcl
  set μ := f ((0 : E), 1) with hμ_def
  set ℓ : StrongDual ℝ E := f.comp (ContinuousLinearMap.inl ℝ E ℝ) with hℓ_def
  have hfdec : ∀ z r, f (z, r) = ℓ z + r * μ := by
    intro z r
    have e : ((z, r) : E × ℝ) = ContinuousLinearMap.inl ℝ E ℝ z + r • ((0 : E), (1 : ℝ)) := by
      simp
    rw [e, map_add, map_smul, smul_eq_mul]
    rfl
  have hμ : μ < 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 := hf _ (hUint ((0 : E), max R (-A) + 1) (by simp [hη])
      (by simp only; linarith [le_max_left R (-A)]))
    rw [hfdec, hfdec] at h1
    simp only [map_zero, zero_add] at h1
    nlinarith [mul_nonneg (by linarith [le_max_right R (-A)] : (0:ℝ) ≤ max R (-A) + 1 + A) hcon]
  refine ⟨ℓ, μ, hμ, fun p hp => ?_⟩
  have := hfK p hp
  rw [hfdec, show p = (p.1, p.2) from rfl, hfdec] at this
  simpa using this

lemma aux_KL (g₁ g₂ : E → EReal)
    (hb1 : ∀ x, ⊥ < g₁ x) (hb2 : ∀ x, ⊥ < g₂ x)
    (hc1 : ConvexEReal g₁) (hc2 : ConvexEReal g₂)
    {a₀ : E} (ha1 : a₀ ∈ intrinsicInterior ℝ (effDom g₁))
    (ha2 : a₀ ∈ intrinsicInterior ℝ (effDom g₂))
    (s : E) (A : ℝ) (hA : conjugate (g₁ + g₂) s ≤ A) :
    ∃ q, conjugate g₁ (s - q) + conjugate g₂ q ≤ A := by
  have hdom1 : g₁ a₀ < ⊤ := (intrinsicInterior_subset ha1 : a₀ ∈ effDom g₁)
  have hdom2 : g₂ a₀ < ⊤ := (intrinsicInterior_subset ha2 : a₀ ∈ effDom g₂)
  obtain ⟨δ₁, hδ₁, M₁, hM₁⟩ := aux_ri_bdd hb1 hc1 ha1
  obtain ⟨δ₂, hδ₂, M₂, hM₂⟩ := aux_ri_bdd hb2 hc2 ha2
  have hmem1 : ∀ x, g₁ x < ⊤ → x - a₀ ∈ (affineSpan ℝ (effDom g₁)).direction := fun x hx =>
    AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hx) (mem_affineSpan ℝ hdom1)
  have hmem2 : ∀ y, g₂ y < ⊤ → y - a₀ ∈ (affineSpan ℝ (effDom g₂)).direction := fun y hy =>
    AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hy) (mem_affineSpan ℝ hdom2)
  generalize (affineSpan ℝ (effDom g₁)).direction = V₁ at hM₁ hmem1
  generalize (affineSpan ℝ (effDom g₂)).direction = V₂ at hM₂ hmem2
  obtain ⟨η, hη, hdec⟩ := aux_decomp V₁ V₂ (lt_min hδ₁ hδ₂)
  have hA' : ∀ x (a b : ℝ), g₁ x ≤ a → g₂ x ≤ b → inner ℝ s x - (a + b) ≤ A := by
    intro x a b ha hb
    have h1 : ((inner ℝ s x : ℝ) : EReal) - (g₁ + g₂) x ≤ conjugate (g₁ + g₂) s :=
      le_sSup ⟨x, Set.mem_univ _, rfl⟩
    have h2 : ((inner ℝ s x - (a + b) : ℝ) : EReal) ≤
        ((inner ℝ s x : ℝ) : EReal) - (g₁ + g₂) x := by
      rw [EReal.coe_sub, EReal.coe_add]
      exact EReal.sub_le_sub le_rfl (add_le_add ha hb)
    exact EReal.coe_le_coe_iff.mp (h2.trans (h1.trans hA))
  have hnotK : ((0 : E), -A) ∉ {p : E × ℝ | ∃ x y : E, ∃ a b : ℝ, g₁ x ≤ a ∧ g₂ y ≤ b ∧
      p.1 - (y - x) ∈ (V₁ ⊔ V₂)ᗮ ∧ a + b - inner ℝ s x < p.2} := by
    rintro ⟨x, y, a, b, hxa, hyb, hWp, hlt⟩
    have hx : g₁ x < ⊤ := lt_of_le_of_lt hxa (EReal.coe_lt_top a)
    have hy : g₂ y < ⊤ := lt_of_le_of_lt hyb (EReal.coe_lt_top b)
    have hyx : y - x ∈ V₁ ⊔ V₂ := by
      have e : y - x = (y - a₀) - (x - a₀) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (hmem2 y hy))
        (Submodule.mem_sup_left (hmem1 x hx))
    have hyx' : y - x ∈ (V₁ ⊔ V₂)ᗮ := by
      have := Submodule.neg_mem _ hWp
      simpa using this
    have hxy : y - x = 0 := by
      have hmem : y - x ∈ (V₁ ⊔ V₂) ⊓ (V₁ ⊔ V₂)ᗮ := ⟨hyx, hyx'⟩
      rw [Submodule.inf_orthogonal_eq_bot] at hmem
      exact (Submodule.mem_bot ℝ).mp hmem
    have hyx'' : y = x := sub_eq_zero.mp hxy
    subst hyx''
    have := hA' y a b hxa hyb
    simp only at hlt
    linarith
  have hUK : ∀ p : E × ℝ, ‖p.1‖ < η → M₁ + M₂ + ‖s‖ * (‖a₀‖ + min δ₁ δ₂) < p.2 →
      p ∈ {p : E × ℝ | ∃ x y : E, ∃ a b : ℝ, g₁ x ≤ a ∧ g₂ y ≤ b ∧
        p.1 - (y - x) ∈ (V₁ ⊔ V₂)ᗮ ∧ a + b - inner ℝ s x < p.2} := by
    intro p hp1 hp2
    have hu : (V₁ ⊔ V₂).starProjection p.1 ∈ V₁ ⊔ V₂ := (V₁ ⊔ V₂).starProjection_apply_mem p.1
    have hun : ‖(V₁ ⊔ V₂).starProjection p.1‖ < η :=
      lt_of_le_of_lt ((V₁ ⊔ V₂).norm_starProjection_apply_le p.1) hp1
    obtain ⟨v₁, hv₁, v₂, hv₂, hn₁, hn₂, huv⟩ := hdec _ hu hun
    refine ⟨a₀ - v₁, a₀ + v₂, M₁, M₂, ?_, ?_, ?_, ?_⟩
    · have := hM₁ (-v₁) (V₁.neg_mem hv₁)
        (by rw [norm_neg]; exact lt_of_lt_of_le hn₁ (min_le_left _ _))
      rwa [← sub_eq_add_neg] at this
    · exact hM₂ v₂ hv₂ (lt_of_lt_of_le hn₂ (min_le_right _ _))
    · have e : p.1 - ((a₀ + v₂) - (a₀ - v₁)) = p.1 - (V₁ ⊔ V₂).starProjection p.1 := by
        rw [huv]; abel
      rw [e]
      exact (V₁ ⊔ V₂).sub_starProjection_mem_orthogonal p.1
    · have h1 : -(inner ℝ s (a₀ - v₁)) ≤ ‖s‖ * (‖a₀‖ + min δ₁ δ₂) := by
        have h2 := neg_le_abs (inner ℝ s (a₀ - v₁))
        have h3 := abs_real_inner_le_norm s (a₀ - v₁)
        have h4 : ‖a₀ - v₁‖ ≤ ‖a₀‖ + min δ₁ δ₂ := by
          calc ‖a₀ - v₁‖ ≤ ‖a₀‖ + ‖v₁‖ := norm_sub_le _ _
            _ ≤ ‖a₀‖ + min δ₁ δ₂ := by linarith [hn₁.le]
        have h5 : ‖s‖ * ‖a₀ - v₁‖ ≤ ‖s‖ * (‖a₀‖ + min δ₁ δ₂) :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
        linarith
      linarith
  obtain ⟨ℓ, μ, hμ, hsep⟩ := aux_sep _ (aux_K_convex g₁ g₂ hc1 hc2 (V₁ ⊔ V₂)ᗮ s) A hnotK η _
    hη hUK
  have hmain : ∀ x y, g₁ x < ⊤ → g₂ y < ⊤ →
      ℓ (y - x) + ((g₁ x).toReal + (g₂ y).toReal - inner ℝ s x) * μ ≤ -A * μ := by
    intro x y hx hy
    have hle : ∀ ε > 0,
        ℓ (y - x) + ((g₁ x).toReal + (g₂ y).toReal - inner ℝ s x + ε) * μ ≤ -A * μ := by
      intro ε hε
      exact hsep (y - x, (g₁ x).toReal + (g₂ y).toReal - inner ℝ s x + ε)
        ⟨x, y, (g₁ x).toReal, (g₂ y).toReal, EReal.le_coe_toReal hx.ne,
          EReal.le_coe_toReal hy.ne, by simp, by simp only; linarith⟩
    by_contra hcon
    push_neg at hcon
    have hgap : 0 < ℓ (y - x) + ((g₁ x).toReal + (g₂ y).toReal - inner ℝ s x) * μ - (-A * μ) := by
      linarith
    have h1 := hle ((ℓ (y - x) + ((g₁ x).toReal + (g₂ y).toReal - inner ℝ s x) * μ - (-A * μ)) /
      (-2 * μ)) (div_pos hgap (by linarith))
    have e : (ℓ (y - x) + ((g₁ x).toReal + (g₂ y).toReal - inner ℝ s x) * μ - (-A * μ)) /
        (-2 * μ) * μ = -((ℓ (y - x) + ((g₁ x).toReal + (g₂ y).toReal - inner ℝ s x) * μ -
          (-A * μ)) / 2) := by
      have hμ0 : μ ≠ 0 := ne_of_lt hμ
      field_simp
    rw [add_mul, e] at h1
    linarith
  have hν : 0 < -μ := by linarith
  have hq : ∀ z, inner ℝ ((InnerProductSpace.toDual ℝ E).symm ((-μ)⁻¹ • ℓ)) z =
      (-μ)⁻¹ * ℓ z := by
    intro z
    rw [InnerProductSpace.toDual_symm_apply]
    simp
  generalize (InnerProductSpace.toDual ℝ E).symm ((-μ)⁻¹ • ℓ) = q at hq
  have hfin : ∀ x y, g₁ x < ⊤ → g₂ y < ⊤ →
      (inner ℝ (s - q) x - (g₁ x).toReal) + (inner ℝ q y - (g₂ y).toReal) ≤ A := by
    intro x y hx hy
    have h := hmain x y hx hy
    have h2 : inner ℝ q (y - x) = (-μ)⁻¹ * ℓ (y - x) := hq _
    rw [inner_sub_right] at h2
    rw [inner_sub_left]
    have h3 : (-μ)⁻¹ * ℓ (y - x) ≤ (g₁ x).toReal + (g₂ y).toReal - inner ℝ s x + A := by
      rw [inv_mul_le_iff₀ hν]
      nlinarith
    linarith
  refine ⟨q, ?_⟩
  have hB : ∀ x, g₁ x < ⊤ →
      conjugate g₂ q ≤ ((A - (inner ℝ (s - q) x - (g₁ x).toReal) : ℝ) : EReal) := by
    intro x hx
    unfold conjugate
    apply sSup_le
    rintro _ ⟨y, -, rfl⟩
    rcases lt_or_eq_of_le (le_top : g₂ y ≤ ⊤) with hy | hy
    · simp only
      rw [← EReal.coe_toReal hy.ne (hb2 y).ne', ← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith [hfin x y hx hy]
    · simp only
      rw [hy, EReal.sub_top]
      exact bot_le
  have hBtop : conjugate g₂ q ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hB a₀ hdom1)
  have hBbot : conjugate g₂ q ≠ ⊥ := by
    have h : ((inner ℝ q a₀ : ℝ) : EReal) - g₂ a₀ ≤ conjugate g₂ q :=
      le_sSup ⟨a₀, Set.mem_univ _, rfl⟩
    rw [← EReal.coe_toReal hdom2.ne (hb2 a₀).ne', ← EReal.coe_sub] at h
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h
  obtain ⟨b, hb⟩ : ∃ b : ℝ, conjugate g₂ q = b :=
    ⟨_, (EReal.coe_toReal hBtop hBbot).symm⟩
  have hB' : ∀ x, g₁ x < ⊤ → b ≤ A - (inner ℝ (s - q) x - (g₁ x).toReal) := by
    intro x hx
    have := hB x hx
    rw [hb, EReal.coe_le_coe_iff] at this
    exact this
  have h1 : conjugate g₁ (s - q) ≤ ((A - b : ℝ) : EReal) := by
    unfold conjugate
    apply sSup_le
    rintro _ ⟨x, -, rfl⟩
    rcases lt_or_eq_of_le (le_top : g₁ x ≤ ⊤) with hx | hx
    · simp only
      rw [← EReal.coe_toReal hx.ne (hb1 x).ne', ← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith [hB' x hx]
    · simp only
      rw [hx, EReal.sub_top]
      exact bot_le
  rw [hb]
  calc conjugate g₁ (s - q) + (b : EReal) ≤ ((A - b : ℝ) : EReal) + (b : EReal) :=
        add_le_add h1 le_rfl
    _ = A := by rw [← EReal.coe_add]; congr 1; ring

set_option linter.unusedVariables false in
theorem FCA_chap_E_2_3_2
  (g₁ g₂ : E → EReal)
  (hg_closed_convex : InClosedConvRn g₁ ∧ InClosedConvRn g₂)
  (hg_nondegenerate : IsNondegenerate g₁ ∧ IsNondegenerate g₂)
  (h_ri_intersect : Set.Nonempty (intrinsicInterior ℝ (effDom g₁) ∩
    intrinsicInterior ℝ (effDom g₂))) :
  let h := fun p q => conjugate g₁ p + conjugate g₂ q
  (∀ s, (conjugate (g₁ + g₂) s) =
  (infimalConv (conjugate g₁) (conjugate g₂) s)) ∧
  (∀ s ∈ effDom ((conjugate (g₁ + g₂))), ∃ p' q',
  (p' + q' = s) ∧
  ((h p' q') = sInf {v | ∃ p q, (p + q = s) ∧ (h p q = v)}) ∧
  ((h p' q') = infimalConv (conjugate g₁) (conjugate g₂) s) ∧
  (h p' q' = conjugate (g₁ + g₂) s)) := by
  intro h
  obtain ⟨⟨⟨hb1, -, hc1⟩, -⟩, ⟨⟨hb2, -, hc2⟩, -⟩⟩ := hg_closed_convex
  obtain ⟨a₀, ha1, ha2⟩ := h_ri_intersect
  have hEI : ∀ p q, conjugate (g₁ + g₂) (p + q) ≤ conjugate g₁ p + conjugate g₂ q :=
    aux_EI g₁ g₂ hb1 hb2
  have hatt : ∀ s, conjugate (g₁ + g₂) s ≠ ⊤ →
      ∃ q, conjugate g₁ (s - q) + conjugate g₂ q ≤ conjugate (g₁ + g₂) s := by
    intro s hs
    have hbot : conjugate (g₁ + g₂) s ≠ ⊥ := by
      have hdom1 : g₁ a₀ < ⊤ := (intrinsicInterior_subset ha1 : a₀ ∈ effDom g₁)
      have hdom2 : g₂ a₀ < ⊤ := (intrinsicInterior_subset ha2 : a₀ ∈ effDom g₂)
      have hle : ((inner ℝ s a₀ : ℝ) : EReal) - (g₁ + g₂) a₀ ≤ conjugate (g₁ + g₂) s :=
        le_sSup ⟨a₀, Set.mem_univ _, rfl⟩
      rw [Pi.add_apply, ← EReal.coe_toReal hdom1.ne (hb1 a₀).ne',
        ← EReal.coe_toReal hdom2.ne (hb2 a₀).ne', ← EReal.coe_add, ← EReal.coe_sub] at hle
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
    have hA : conjugate (g₁ + g₂) s ≤ (((conjugate (g₁ + g₂) s).toReal : ℝ) : EReal) :=
      EReal.le_coe_toReal hs
    obtain ⟨q, hq⟩ := aux_KL g₁ g₂ hb1 hb2 hc1 hc2 ha1 ha2 s _ hA
    refine ⟨q, ?_⟩
    rw [EReal.coe_toReal hs hbot] at hq
    exact hq
  have hpart1 : ∀ s, conjugate (g₁ + g₂) s = infimalConv (conjugate g₁) (conjugate g₂) s := by
    intro s
    unfold infimalConv
    apply le_antisymm
    · apply le_sInf
      rintro _ ⟨y, rfl⟩
      have := hEI y (s - y)
      rwa [show y + (s - y) = s by abel] at this
    · by_cases hs : conjugate (g₁ + g₂) s = ⊤
      · rw [hs]; exact le_top
      · obtain ⟨q, hq⟩ := hatt s hs
        refine le_trans (sInf_le ⟨s - q, ?_⟩) hq
        rw [show s - (s - q) = q by abel]
  refine ⟨hpart1, fun s hs => ?_⟩
  have hs' : conjugate (g₁ + g₂) s ≠ ⊤ := ne_of_lt hs
  obtain ⟨q, hq⟩ := hatt s hs'
  have heq : h (s - q) q = conjugate (g₁ + g₂) s := by
    apply le_antisymm hq
    have := hEI (s - q) q
    rwa [sub_add_cancel] at this
  refine ⟨s - q, q, sub_add_cancel s q, ?_, ?_, heq⟩
  · apply le_antisymm
    · apply le_sInf
      rintro _ ⟨p, p', hpp, rfl⟩
      rw [heq, ← hpp]
      exact hEI p p'
    · exact sInf_le ⟨s - q, q, sub_add_cancel s q, rfl⟩
  · exact heq.trans (hpart1 s)

end FCA_chap_E_2_3_2
