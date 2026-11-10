import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_4_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_4_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_4_4`, so the main result is `FCA_chap_D_4_4_4.FCA_chap_D_4_4_4`.
-/

namespace FCA_chap_D_4_4_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
open Filter in
lemma FCA_aux_slope_mono {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) {t s : ℝ}
    (ht : 0 < t) (hts : t ≤ s) :
    (f (x + t • d) - f x) / t ≤ (f (x + s • d) - f x) / s := by
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have key : f (x + t • d) ≤ (1 - t / s) * f x + (t / s) * f (x + s • d) := by
    have h : f ((1 - t / s) • x + (t / s) • (x + s • d)) ≤
        (1 - t / s) • f x + (t / s) • f (x + s • d) :=
      hf.2 (Set.mem_univ x) (Set.mem_univ (x + s • d))
        (by rw [sub_nonneg, div_le_one hs]; exact hts) (div_nonneg ht.le hs.le) (by ring)
    have e : (1 - t / s) • x + (t / s) • (x + s • d) = x + t • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ t hs.ne', ← add_assoc, ← add_smul, sub_add_cancel,
        one_smul]
    rw [e] at h
    simpa [smul_eq_mul] using h
  have key2 : s * f (x + t • d) ≤ (s - t) * f x + t * f (x + s • d) := by
    have := mul_le_mul_of_nonneg_left key hs.le
    calc s * f (x + t • d) ≤ s * ((1 - t / s) * f x + (t / s) * f (x + s • d)) := this
      _ = (s - t) * f x + t * f (x + s • d) := by field_simp
  rw [div_le_div_iff₀ ht hs]
  linarith

omit [FiniteDimensional ℝ E] in
open Filter in
lemma FCA_aux_tendsto_slope {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (d : E) :
    Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t) (𝓝[>] 0) (𝓝 (fderiv ℝ f x d)) := by
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • d) := by
    simpa using hf.hasFDerivAt
  have hcomp := hf'.comp_hasDerivAt (0:ℝ) hline
  have := hcomp.tendsto_slope_zero_right
  refine this.congr' ?_
  filter_upwards with t
  simp [div_eq_inv_mul, Function.comp]

omit [FiniteDimensional ℝ E] in
open Filter in
lemma FCA_aux_fderiv_le_slope {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x : E}
    (hd : DifferentiableAt ℝ f x) (d : E) {s : ℝ} (hs : 0 < s) :
    fderiv ℝ f x d ≤ (f (x + s • d) - f x) / s := by
  apply le_of_tendsto (FCA_aux_tendsto_slope hd d)
  filter_upwards [Ioo_mem_nhdsGT hs] with t ht
  exact FCA_aux_slope_mono hf x d ht.1 ht.2.le

open Filter in
lemma FCA_aux_isCompact_convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  set n := Module.finrank ℝ E
  let Φ : (k : ℕ) → (Fin k → ℝ) × (Fin k → E) → E := fun k p => ∑ i, p.1 i • p.2 i
  have hΦ : ∀ k, Continuous (Φ k) := fun k =>
    continuous_finset_sum _ (fun i _ =>
      ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd))
  let T : Fin (n + 2) → Set E := fun k =>
    Φ (k : ℕ) '' (stdSimplex ℝ (Fin (k : ℕ)) ×ˢ Set.univ.pi (fun _ => s))
  have hT : ∀ k, IsCompact (T k) := fun k =>
    ((isCompact_stdSimplex _).prod (isCompact_univ_pi (fun _ => hs))).image (hΦ k)
  have heq : convexHull ℝ s = ⋃ k, T k := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨ι, _, z, w, hz, hzi, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hy
      have hcard : Fintype.card ι ≤ n + 1 :=
        hzi.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
      let e := Fintype.equivFin ι
      refine Set.mem_iUnion.2 ⟨⟨Fintype.card ι, Nat.lt_succ_of_le hcard⟩,
        ⟨(w ∘ e.symm, z ∘ e.symm), ⟨?_, ?_⟩, ?_⟩⟩
      · refine ⟨fun i => (hw0 _).le, ?_⟩
        rw [← hw1]
        exact Equiv.sum_comp e.symm w
      · intro i _
        exact hz ⟨_, rfl⟩
      · show ∑ i, (w ∘ e.symm) i • (z ∘ e.symm) i = y
        rw [← hwz]
        exact Equiv.sum_comp e.symm (fun a => w a • z a)
    · apply Set.iUnion_subset
      rintro k _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw.1 i) hw.2
        (fun i _ => subset_convexHull ℝ s (hz i (Set.mem_univ i)))
  rw [heq]
  exact isCompact_iUnion hT

set_option linter.unusedVariables false in
theorem FCA_chap_D_4_4_4
  {J : Type*}
  [TopologicalSpace J]
  [CompactSpace J]
  [Nonempty J]
  [FirstCountableTopology J]
  (f : J → (E → ℝ))
  (x : E)
  (hf_convex : ∀ (i : J), ConvexOn ℝ Set.univ (f i))
  (hf_finite : ∀ z, ⨆ (j : J), (f j z : EReal) < ⊤)
  (hf_usc : ∀ z, ∀ j', UpperSemicontinuousAt (fun (j : J) => f j z) j')
  (hf_differentiable : ∀ (j : J), Differentiable ℝ (f j)) :
  let F_fun : E → EReal := fun z => ⨆ (j : J), (f j z)
  let Jx := {j | f j x = F_fun x}
  directionalSubdifferential F_fun x = convexHull ℝ (⋃ j ∈ Jx, {gradient (f j) x}) := by
  intro F_fun Jx
  have husc : ∀ z, UpperSemicontinuous (fun j : J => f j z) := fun z j' => hf_usc z j'
  have hmax : ∀ z, ∃ j, ∀ i, f i z ≤ f j z := by
    intro z
    obtain ⟨a, -, ha⟩ := ((husc z).upperSemicontinuousOn Set.univ).exists_isMaxOn
      Set.univ_nonempty isCompact_univ
    exact ⟨a, fun i => isMaxOn_iff.1 ha i (Set.mem_univ i)⟩
  choose jm hjm using hmax
  set F : E → ℝ := fun z => f (jm z) z with hF_def
  have hF_le : ∀ i z, f i z ≤ F z := fun i z => hjm z i
  have hF_eq : ∀ z, F_fun z = (F z : EReal) := by
    intro z
    apply le_antisymm
    · exact iSup_le fun i => EReal.coe_le_coe_iff.2 (hF_le i z)
    · exact le_iSup (fun j => ((f j z : ℝ) : EReal)) (jm z)
  have hJx : ∀ j, j ∈ Jx ↔ f j x = F x := by
    intro j
    show (f j x : EReal) = F_fun x ↔ _
    rw [hF_eq]
    exact EReal.coe_eq_coe_iff
  have hF_conv : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
    calc F (a • y + b • z) = f (jm (a • y + b • z)) (a • y + b • z) := rfl
      _ ≤ a • f (jm (a • y + b • z)) y + b • f (jm (a • y + b • z)) z :=
          (hf_convex _).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      _ ≤ a • F y + b • F z := by
          simp only [smul_eq_mul]
          have h1 := hF_le (jm (a • y + b • z)) y
          have h2 := hF_le (jm (a • y + b • z)) z
          nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  -- Key directional derivative facts
  have hdir : ∀ d : E, ∃ L : ℝ,
      Filter.Tendsto (fun t : ℝ => (F (x + t • d) - F x) / t) (𝓝[>] 0) (𝓝 L) ∧
      (∀ j ∈ Jx, fderiv ℝ (f j) x d ≤ L) ∧ (∃ j ∈ Jx, L ≤ fderiv ℝ (f j) x d) := by
    intro d
    set σ : ℝ → ℝ := fun t => (F (x + t • d) - F x) / t with hσ
    have hmono : MonotoneOn σ (Set.Ioi 0) := fun t ht s _ hts =>
      FCA_aux_slope_mono hF_conv x d ht hts
    -- lower bound
    have hlow : ∀ j ∈ Jx, ∀ t, 0 < t → fderiv ℝ (f j) x d ≤ σ t := by
      intro j hj t ht
      have hj' : f j x = F x := (hJx j).1 hj
      calc fderiv ℝ (f j) x d ≤ (f j (x + t • d) - f j x) / t :=
            FCA_aux_fderiv_le_slope (hf_convex _) ((hf_differentiable _) x) d ht
        _ ≤ σ t := by
            apply div_le_div_of_nonneg_right _ ht.le
            have := hF_le j (x + t • d)
            rw [hj']
            linarith
    have hjx : jm x ∈ Jx := (hJx _).2 rfl
    have hbdd : BddBelow (σ '' Set.Ioi 0) :=
      ⟨fderiv ℝ (f (jm x)) x d, by rintro _ ⟨t, ht, rfl⟩; exact hlow _ hjx t ht⟩
    have htend := hmono.tendsto_nhdsGT hbdd
    set L := sInf (σ '' Set.Ioi 0) with hL
    refine ⟨L, htend, ?_, ?_⟩
    · intro j hj
      apply ge_of_tendsto htend
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact hlow j hj t ht
    · have hLle : ∀ t, 0 < t → L ≤ σ t := fun t ht => csInf_le hbdd ⟨t, ht, rfl⟩
      let K : Set.Ioi (0:ℝ) → Set J := fun t => {j | F x + (t:ℝ) * L ≤ f j (x + (t:ℝ) • d)}
      have hK_closed : ∀ t, IsClosed (K t) := fun t =>
        (husc (x + (t:ℝ) • d)).isClosed_preimage (F x + (t:ℝ) * L)
      have hK_ne : ∀ t, (K t).Nonempty := by
        intro t
        refine ⟨jm (x + (t:ℝ) • d), ?_⟩
        show F x + (t:ℝ) * L ≤ F (x + (t:ℝ) • d)
        have := hLle t t.2
        rw [hσ, le_div_iff₀ t.2] at this
        linarith
      have hK_mono : ∀ t₁ t₂ : Set.Ioi (0:ℝ), (t₁:ℝ) ≤ t₂ → K t₁ ⊆ K t₂ := by
        intro t₁ t₂ h12 j hj
        have hj' : F x + (t₁:ℝ) * L ≤ f j (x + (t₁:ℝ) • d) := hj
        have hA := FCA_aux_slope_mono (hf_convex j) x d t₁.2 h12
        have ha := hF_le j x
        have hpos1 : (0:ℝ) < t₁ := t₁.2
        have hpos2 : (0:ℝ) < t₂ := t₂.2
        rw [div_le_div_iff₀ hpos1 hpos2] at hA
        show F x + (t₂:ℝ) * L ≤ f j (x + (t₂:ℝ) • d)
        have hkey : 0 ≤ (t₁:ℝ) * (f j (x + (t₂:ℝ) • d) - F x - t₂ * L) := by
          nlinarith [mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 ha)]
        have := (mul_nonneg_iff_of_pos_left hpos1).1 hkey
        linarith
      have hK_dir : Directed (· ⊇ ·) K := by
        intro t₁ t₂
        exact ⟨⟨min (t₁:ℝ) t₂, Set.mem_Ioi.2 (lt_min t₁.2 t₂.2)⟩, hK_mono _ _ (min_le_left _ _),
          hK_mono _ _ (min_le_right _ _)⟩
      haveI : Nonempty (Set.Ioi (0:ℝ)) := ⟨⟨1, Set.mem_Ioi.2 one_pos⟩⟩
      obtain ⟨j₀, hj₀⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K
        hK_dir hK_ne (fun t => (hK_closed t).isCompact) hK_closed
      rw [Set.mem_iInter] at hj₀
      have hj₀' : ∀ t : ℝ, 0 < t → F x + t * L ≤ f j₀ (x + t • d) := fun t ht => hj₀ ⟨t, ht⟩
      have hcont0 : Filter.Tendsto (fun t : ℝ => f j₀ (x + t • d)) (𝓝[>] 0) (𝓝 (f j₀ x)) := by
        have hc : Continuous (fun t : ℝ => f j₀ (x + t • d)) :=
          (hf_differentiable j₀).continuous.comp
            (continuous_const.add (continuous_id.smul continuous_const))
        have h2 := hc.tendsto 0
        simp only [zero_smul, add_zero] at h2
        exact h2.mono_left nhdsWithin_le_nhds
      have hlim2 : Filter.Tendsto (fun t : ℝ => F x + t * L) (𝓝[>] 0) (𝓝 (F x)) := by
        have h3 : Filter.Tendsto (fun t : ℝ => F x + t * L) (𝓝 0) (𝓝 (F x + 0 * L)) :=
          tendsto_const_nhds.add (Filter.tendsto_id.mul_const L)
        simp only [zero_mul, add_zero] at h3
        exact h3.mono_left nhdsWithin_le_nhds
      have hFle : F x ≤ f j₀ x := le_of_tendsto_of_tendsto hlim2 hcont0
        (by filter_upwards [self_mem_nhdsWithin] with t ht; exact hj₀' t ht)
      have hj₀x : f j₀ x = F x := le_antisymm (hF_le j₀ x) hFle
      refine ⟨j₀, (hJx j₀).2 hj₀x, ?_⟩
      apply ge_of_tendsto (FCA_aux_tendsto_slope ((hf_differentiable j₀) x) d)
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [hj₀x, le_div_iff₀ ht]
      linarith [hj₀' t ht]
  choose L hL_tend hL_le hL_ex using hdir
  have hDD : ∀ d, directionalDeriv F_fun x d = (L d : EReal) := by
    intro d
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    have : (fun t => differenceQuotient F_fun x d t) =
        fun t : ℝ => (((F (x + t • d) - F x) / t : ℝ) : EReal) := by
      funext t
      simp only [differenceQuotient, hF_eq]
      rfl
    rw [this]
    exact EReal.tendsto_coe.2 (hL_tend d)
  have hgrad : ∀ j v, inner ℝ (gradient (f j) x) v = fderiv ℝ (f j) x v := fun j v => by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  -- compactness of G
  have hG_eq : (⋃ j ∈ Jx, {gradient (f j) x}) = (fun j => gradient (f j) x) '' Jx :=
    (Set.image_eq_iUnion _ _).symm
  have hJx_closed : IsClosed Jx := by
    have : Jx = (fun j => f j x) ⁻¹' Set.Ici (F x) := by
      ext j
      rw [hJx j]
      simp only [Set.mem_preimage, Set.mem_Ici]
      exact ⟨fun h => h.symm.le, fun h => le_antisymm (hF_le j x) h⟩
    rw [this]
    exact (husc x).isClosed_preimage (F x)
  have hcont : ContinuousOn (fun j => gradient (f j) x) Jx := by
    intro j₀ hj₀
    have hj₀x := (hJx j₀).1 hj₀
    have hup : ∀ e : E, ∀ a, fderiv ℝ (f j₀) x e < a →
        ∀ᶠ j in 𝓝[Jx] j₀, fderiv ℝ (f j) x e < a := by
      intro e a ha
      set ε := a - fderiv ℝ (f j₀) x e with hε
      have hεpos : 0 < ε := sub_pos.2 ha
      have htend := FCA_aux_tendsto_slope ((hf_differentiable j₀) x) e
      have hev : ∀ᶠ t in 𝓝[>] (0:ℝ),
          (f j₀ (x + t • e) - f j₀ x) / t < fderiv ℝ (f j₀) x e + ε / 2 :=
        htend.eventually (eventually_lt_nhds (by linarith))
      obtain ⟨s, hs1, hs2⟩ := (hev.and self_mem_nhdsWithin).exists
      have hspos : 0 < s := hs2
      have husc' := hf_usc (x + s • e) j₀ (f j₀ (x + s • e) + s * (ε / 2))
        (by linarith [mul_pos hspos (half_pos hεpos)])
      filter_upwards [nhdsWithin_le_nhds husc', self_mem_nhdsWithin] with j hj1 hj2
      have hjx := (hJx j).1 hj2
      have hC := FCA_aux_fderiv_le_slope (hf_convex j) ((hf_differentiable j) x) e hspos
      rw [hjx] at hC
      rw [hj₀x] at hs1
      have h4 : (f j (x + s • e) - F x) / s < (f j₀ (x + s • e) - F x) / s + ε / 2 := by
        rw [div_add' _ _ _ hspos.ne', div_lt_div_iff_of_pos_right hspos]
        linarith
      linarith
    have hcoord : ∀ e : E, Filter.Tendsto (fun j => fderiv ℝ (f j) x e) (𝓝[Jx] j₀)
        (𝓝 (fderiv ℝ (f j₀) x e)) := by
      intro e
      rw [tendsto_order]
      refine ⟨fun a ha => ?_, fun a ha => hup e a ha⟩
      have := hup (-e) (-a) (by simp only [map_neg]; linarith)
      filter_upwards [this] with j hj
      simp only [map_neg] at hj
      linarith
    set b := stdOrthonormalBasis ℝ E
    have hsum : ∀ j, gradient (f j) x = ∑ i, (fderiv ℝ (f j) x (b i)) • b i := by
      intro j
      conv_lhs => rw [← b.sum_repr' (gradient (f j) x)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_comm, hgrad]
    show Filter.Tendsto (fun j => gradient (f j) x) (𝓝[Jx] j₀) (𝓝 (gradient (f j₀) x))
    simp_rw [hsum]
    exact tendsto_finset_sum _ (fun i _ => (hcoord (b i)).smul_const (b i))
  have hG_cpt : IsCompact (⋃ j ∈ Jx, {gradient (f j) x}) := by
    rw [hG_eq]
    exact hJx_closed.isCompact.image_of_continuousOn hcont
  have hconv_cpt : IsCompact (convexHull ℝ (⋃ j ∈ Jx, {gradient (f j) x})) :=
    FCA_aux_isCompact_convexHull hG_cpt
  -- final
  ext s
  simp only [directionalSubdifferential, Set.mem_setOf_eq, hDD, EReal.coe_le_coe_iff]
  constructor
  · intro hs
    by_contra hns
    obtain ⟨ℓ, u, hℓ, hu⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hconv_cpt.isClosed hns
    set d := (InnerProductSpace.toDual ℝ E).symm ℓ with hd
    have hℓd : ∀ y, ℓ y = inner ℝ d y := fun y => InnerProductSpace.toDual_symm_apply.symm
    obtain ⟨j, hj, hjL⟩ := hL_ex d
    have h1 := hs d
    have h2 : inner ℝ (gradient (f j) x) d < u := by
      have hmem : gradient (f j) x ∈ convexHull ℝ (⋃ j ∈ Jx, {gradient (f j) x}) :=
        subset_convexHull ℝ _ (Set.mem_biUnion hj (Set.mem_singleton _))
      have := hℓ _ hmem
      rw [hℓd, real_inner_comm] at this
      exact this
    have h3 : u < inner ℝ s d := by
      rw [hℓd, real_inner_comm] at hu
      exact hu
    rw [hgrad] at h2
    linarith
  · intro hs d
    have hsub : (⋃ j ∈ Jx, {gradient (f j) x}) ⊆ {y | inner ℝ y d ≤ L d} := by
      intro y hy
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      simp only [Set.mem_setOf_eq, hgrad]
      exact hL_le d j hj
    have hconv : Convex ℝ {y : E | inner ℝ y d ≤ L d} :=
      convex_halfSpace_le ⟨fun y z => inner_add_left y z d,
        fun c y => by rw [real_inner_smul_left, smul_eq_mul]⟩ (L d)
    exact convexHull_min hsub hconv hs

end FCA_chap_D_4_4_4
