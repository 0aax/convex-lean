import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_5_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_5_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_5_2`, so the main result is `FCA_chap_B_2_5_2.FCA_chap_B_2_5_2`.
-/

namespace FCA_chap_B_2_5_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma FCA_aux_upClosed_epigraph {F : Type*} (g : F → EReal) :
    ∀ (x : F) (r r' : ℝ), (x, r) ∈ epigraph g → r ≤ r' → (x, r') ∈ epigraph g := by
  intro x r r' h hr
  exact le_trans h (EReal.coe_le_coe_iff.mpr hr)

lemma FCA_aux_upClosed_convexHull {F : Type*} [AddCommGroup F] [Module ℝ F] {S : Set (F × ℝ)}
    (hS : ∀ (x : F) (r r' : ℝ), (x, r) ∈ S → r ≤ r' → (x, r') ∈ S) :
    ∀ (x : F) (r r' : ℝ), (x, r) ∈ convexHull ℝ S → r ≤ r' → (x, r') ∈ convexHull ℝ S := by
  intro x r r' h hr
  have hv : ((0 : F), r' - r) +ᵥ (x, r) ∈ ((0 : F), r' - r) +ᵥ convexHull ℝ S :=
    Set.vadd_mem_vadd_set h
  rw [← convexHull_vadd] at hv
  have heq : ((0 : F), r' - r) +ᵥ (x, r) = (x, r') := by
    simp [vadd_eq_add]
  rw [heq] at hv
  refine convexHull_mono ?_ hv
  rintro _ ⟨⟨y, t⟩, hyt, rfl⟩
  have : ((0 : F), r' - r) +ᵥ (y, t) = (y, r' - r + t) := by simp [vadd_eq_add]
  show ((0 : F), r' - r) +ᵥ (y, t) ∈ S
  rw [this]
  exact hS y t _ hyt (by linarith)

lemma FCA_aux_upClosed_closure {F : Type*} [TopologicalSpace F] {S : Set (F × ℝ)}
    (hS : ∀ (x : F) (r r' : ℝ), (x, r) ∈ S → r ≤ r' → (x, r') ∈ S) :
    ∀ (x : F) (r r' : ℝ), (x, r) ∈ closure S → r ≤ r' → (x, r') ∈ closure S := by
  intro x r r' h hr
  have hc : Continuous (fun p : F × ℝ => (p.1, p.2 + (r' - r))) := by fun_prop
  have hm : Set.MapsTo (fun p : F × ℝ => (p.1, p.2 + (r' - r))) S S := by
    rintro ⟨y, t⟩ hyt
    exact hS y t _ hyt (by linarith)
  have := map_mem_closure hc h hm
  simpa using this

lemma FCA_aux_funFromSet_le_of_mem {F : Type*} {S : Set (F × ℝ)} {x : F} {r : ℝ}
    (h : (x, r) ∈ S) : funFromSet S x ≤ r :=
  sInf_le ⟨r, h, rfl⟩

lemma FCA_aux_mem_of_funFromSet_le {F : Type*} [TopologicalSpace F] {S : Set (F × ℝ)}
    (hS : ∀ (x : F) (r r' : ℝ), (x, r) ∈ S → r ≤ r' → (x, r') ∈ S) (hc : IsClosed S)
    {x : F} {r : ℝ} (h : funFromSet S x ≤ r) : (x, r) ∈ S := by
  have hT : IsClosed {t : ℝ | (x, t) ∈ S} :=
    hc.preimage (Continuous.prodMk_right x)
  have hIoi : Set.Ioi r ⊆ {t : ℝ | (x, t) ∈ S} := by
    intro t ht
    have hlt : funFromSet S x < t := lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr ht)
    obtain ⟨_, ⟨t', ht', rfl⟩, ht'lt⟩ := sInf_lt_iff.mp hlt
    exact hS x t' t ht' (EReal.coe_lt_coe_iff.mp ht'lt).le
  have : Set.Ici r ⊆ {t : ℝ | (x, t) ∈ S} := by
    rw [← closure_Ioi]
    exact hT.closure_subset_iff.mpr hIoi
  exact this Set.self_mem_Ici

lemma FCA_aux_epigraph_funFromSet {F : Type*} [TopologicalSpace F] {S : Set (F × ℝ)}
    (hS : ∀ (x : F) (r r' : ℝ), (x, r) ∈ S → r ≤ r' → (x, r') ∈ S) (hc : IsClosed S) :
    epigraph (funFromSet S) = S := by
  ext ⟨x, r⟩
  exact ⟨fun h => FCA_aux_mem_of_funFromSet_le hS hc h,
    fun h => FCA_aux_funFromSet_le_of_mem h⟩

lemma FCA_aux_lsc_funFromSet {F : Type*} [TopologicalSpace F] {S : Set (F × ℝ)}
    (hS : ∀ (x : F) (r r' : ℝ), (x, r) ∈ S → r ≤ r' → (x, r') ∈ S) (hc : IsClosed S) :
    LowerSemicontinuous (funFromSet S) := by
  intro x y hy
  obtain ⟨r, hyr, hrx⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hnot : (x, r) ∉ S := fun h => absurd (FCA_aux_funFromSet_le_of_mem h) (not_le.mpr hrx)
  have hopen : IsOpen {x' : F | (x', r) ∉ S} :=
    hc.isOpen_compl.preimage (Continuous.prodMk_left r)
  filter_upwards [hopen.mem_nhds hnot] with x' hx'
  exact lt_trans hyr (not_le.mp (fun h => hx' (FCA_aux_mem_of_funFromSet_le hS hc h)))

lemma FCA_aux_isClosed_epigraph_of_lsc {F : Type*} [TopologicalSpace F] {h : F → EReal}
    (hh : LowerSemicontinuous h) : IsClosed (epigraph h) := by
  have h1 : IsClosed {p : F × EReal | h p.1 ≤ p.2} := hh.isClosed_epigraph
  have h2 : Continuous (fun p : F × ℝ => (p.1, (p.2 : EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  exact h1.preimage h2

lemma FCA_aux_convex_affine_epi {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : F) (b : ℝ) : Convex ℝ {p : F × ℝ | inner ℝ s p.1 - b ≤ p.2} := by
  intro p hp q hq a c ha hc hac
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, inner_add_right, real_inner_smul_right] at hp hq ⊢
  have hb : b = a * b + c * b := by rw [← add_mul, hac, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hq hc]

lemma FCA_aux_isClosed_affine_epi {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : F) (b : ℝ) : IsClosed {p : F × ℝ | inner ℝ s p.1 - b ≤ p.2} :=
  isClosed_le ((continuous_const.inner continuous_fst).sub continuous_const) continuous_snd

lemma FCA_aux_affine_InClosedConvRn {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : F) (b : ℝ) :
    InClosedConvRn (fun y => ((inner ℝ s y : ℝ) : EReal) - (b : EReal)) := by
  refine ⟨⟨fun x => ?_, ⟨0, ?_⟩, ?_⟩, ?_⟩
  · exact EReal.bot_lt_coe _
  · exact EReal.coe_lt_top _
  · unfold ConvexEReal
    have : epigraph (fun y => ((inner ℝ s y : ℝ) : EReal) - (b : EReal)) =
        {p : F × ℝ | inner ℝ s p.1 - b ≤ p.2} := by
      ext p
      simp only [epigraph, Set.mem_setOf_eq]
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [this]
    exact FCA_aux_convex_affine_epi s b
  · apply Continuous.lowerSemicontinuous
    exact continuous_coe_real_ereal.comp
      ((continuous_const.inner continuous_id).sub continuous_const)

lemma FCA_aux_exists_affine_sep {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {S : Set (F × ℝ)}
    (hS : ∀ (x : F) (r r' : ℝ), (x, r) ∈ S → r ≤ r' → (x, r') ∈ S)
    (hc : IsClosed S) (hconv : Convex ℝ S) (hne : S.Nonempty) (s₀ : F) (b₀ : ℝ)
    (hmin : ∀ p ∈ S, inner ℝ s₀ p.1 - b₀ ≤ p.2) {x₀ : F} {r₀ : ℝ} (hx : (x₀, r₀) ∉ S) :
    ∃ (s : F) (b : ℝ), (∀ p ∈ S, inner ℝ s p.1 - b ≤ p.2) ∧ r₀ < inner ℝ s x₀ - b := by
  obtain ⟨L, u, hLx, hLS⟩ := geometric_hahn_banach_point_closed hconv hc hx
  obtain ⟨w, α, hdec⟩ : ∃ (w : F) (α : ℝ), ∀ (y : F) (t : ℝ),
      L (y, t) = inner ℝ w y + t * α := by
    refine ⟨(InnerProductSpace.toDual ℝ F).symm (L.comp (ContinuousLinearMap.inl ℝ F ℝ)),
      L (0, 1), ?_⟩
    intro y t
    rw [InnerProductSpace.toDual_symm_apply]
    have : ((y, t) : F × ℝ) = (y, 0) + t • ((0 : F), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    simp
  have hα0 : 0 ≤ α := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨⟨y₁, t₁⟩, h₁⟩ := hne
    have hmem : (y₁, max t₁ ((inner ℝ w y₁ - u) / (-α))) ∈ S :=
      hS y₁ t₁ _ h₁ (le_max_left _ _)
    have h2 := hLS _ hmem
    rw [hdec] at h2
    have h3 : (inner ℝ w y₁ - u) / (-α) ≤ max t₁ ((inner ℝ w y₁ - u) / (-α)) :=
      le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at h3
    linarith
  have hS' : ∀ p ∈ S, u - inner ℝ w p.1 < p.2 * α := by
    rintro ⟨y, t⟩ hp
    have := hLS _ hp
    rw [hdec] at this
    simp only
    linarith
  have hx' : r₀ * α < u - inner ℝ w x₀ := by
    rw [hdec] at hLx
    linarith
  obtain ⟨lam, hlam0, hlamδ⟩ : ∃ lam : ℝ, 0 ≤ lam ∧
      lam * (u - inner ℝ w x₀ - r₀ * α) = |r₀ - (inner ℝ s₀ x₀ - b₀)| + 1 := by
    refine ⟨(|r₀ - (inner ℝ s₀ x₀ - b₀)| + 1) / (u - inner ℝ w x₀ - r₀ * α), ?_, ?_⟩
    · exact div_nonneg (by positivity) (by linarith)
    · exact div_mul_cancel₀ _ (by linarith)
  have hcpos : 0 < lam * α + 1 := by positivity
  refine ⟨(lam * α + 1)⁻¹ • (s₀ - lam • w), (lam * α + 1)⁻¹ * (b₀ - lam * u), ?_, ?_⟩
  · rintro ⟨y, t⟩ hp
    have h1 := hS' _ hp
    have h2 := hmin _ hp
    simp only at h1 h2 ⊢
    rw [real_inner_smul_left, inner_sub_left, real_inner_smul_left, ← mul_sub,
      inv_mul_le_iff₀ hcpos]
    nlinarith [mul_le_mul_of_nonneg_left h1.le hlam0]
  · rw [real_inner_smul_left, inner_sub_left, real_inner_smul_left, ← mul_sub,
      lt_inv_mul_iff₀ hcpos]
    have : r₀ - (inner ℝ s₀ x₀ - b₀) ≤ |r₀ - (inner ℝ s₀ x₀ - b₀)| := le_abs_self _
    nlinarith

theorem FCA_chap_B_2_5_2
  (g : E → EReal)
  (hg_nondegenerate : IsNondegenerate g)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  let f₁ := closedConvexHullFun g
  let f₂ := fun x => sSup {z : EReal |
    ∃ (h : E → EReal),
      InClosedConvRn h ∧ Minorizes h g ∧ z = h x}
  let f₃ := fun x => sSup {z : EReal |
    ∃ (s : E) (b : ℝ),
      (∀ y, inner ℝ s y - b ≤ g y) ∧ z = inner ℝ s x - b}
  (InClosedConvRn f₁) ∧ (InClosedConvRn f₂) ∧
  (InClosedConvRn f₃) ∧
  (∀ x, (f₁ x = f₂ x) ∧ (f₂ x = f₃ x)) ∧
  (∀ x, f₁ x = lscHull (convexHullFun g) x) := by
  intro f₁ f₂ f₃
  obtain ⟨⟨x₀, hx₀⟩, s₀, b₀, hsb₀⟩ := hg_nondegenerate
  set C := closure (convexHull ℝ (epigraph g)) with hC
  have hCclosed : IsClosed C := isClosed_closure
  have hCconv : Convex ℝ C := (convex_convexHull ℝ _).closure
  have hCup : ∀ (x : E) (r r' : ℝ), (x, r) ∈ C → r ≤ r' → (x, r') ∈ C :=
    FCA_aux_upClosed_closure (FCA_aux_upClosed_convexHull (FCA_aux_upClosed_epigraph g))
  have hepiC : epigraph g ⊆ C := fun p hp => subset_closure (subset_convexHull ℝ _ hp)
  have hCmin : ∀ p ∈ C, inner ℝ s₀ p.1 - b₀ ≤ p.2 := by
    have hsub : epigraph g ⊆ {p : E × ℝ | inner ℝ s₀ p.1 - b₀ ≤ p.2} := by
      intro p hp
      have h1 : ((inner ℝ s₀ p.1 - b₀ : ℝ) : EReal) ≤ (p.2 : EReal) := le_trans (hsb₀ p.1) hp
      exact EReal.coe_le_coe_iff.mp h1
    exact closure_minimal (convexHull_min hsub (FCA_aux_convex_affine_epi s₀ b₀))
      (FCA_aux_isClosed_affine_epi s₀ b₀)
  have hx₀C : (x₀, (g x₀).toReal) ∈ C := hepiC (EReal.le_coe_toReal hx₀)
  have hf₁def : f₁ = funFromSet C := rfl
  have hf₁_ge : ∀ x, ((inner ℝ s₀ x - b₀ : ℝ) : EReal) ≤ f₁ x := by
    intro x
    apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hCmin _ hr)
  have hf₁_lsc : LowerSemicontinuous f₁ := FCA_aux_lsc_funFromSet hCup hCclosed
  have hf₁_cc : InClosedConvRn f₁ := by
    refine ⟨⟨fun x => lt_of_lt_of_le (EReal.bot_lt_coe _) (hf₁_ge x),
      ⟨x₀, lt_of_le_of_lt (FCA_aux_funFromSet_le_of_mem hx₀C) (EReal.coe_lt_top _)⟩, ?_⟩,
      hf₁_lsc⟩
    unfold ConvexEReal
    rw [hf₁def, FCA_aux_epigraph_funFromSet hCup hCclosed]
    exact hCconv
  have h32 : ∀ x, f₃ x ≤ f₂ x := by
    intro x
    apply sSup_le_sSup
    rintro z ⟨s, b, hsb, rfl⟩
    exact ⟨fun y => ((inner ℝ s y : ℝ) : EReal) - (b : EReal),
      FCA_aux_affine_InClosedConvRn s b, hsb, rfl⟩
  have h21 : ∀ x, f₂ x ≤ f₁ x := by
    intro x
    apply sSup_le
    rintro z ⟨h, hh, hhg, rfl⟩
    apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    have hsub : C ⊆ epigraph h :=
      closure_minimal (convexHull_min (fun p hp => le_trans (hhg p.1) hp) hh.1.2.2)
        (FCA_aux_isClosed_epigraph_of_lsc hh.2)
    exact hsub hr
  have h13 : ∀ x, f₁ x ≤ f₃ x := by
    intro x
    apply le_of_forall_lt
    intro c hc
    obtain ⟨r, hcr, hrx⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    have hnot : (x, r) ∉ C := fun h => absurd (FCA_aux_funFromSet_le_of_mem h) (not_le.mpr hrx)
    obtain ⟨s, b, hsbC, hrsb⟩ :=
      FCA_aux_exists_affine_sep hCup hCclosed hCconv ⟨_, hx₀C⟩ s₀ b₀ hCmin hnot
    refine lt_of_lt_of_le hcr
      (le_trans (EReal.coe_lt_coe_iff.mpr hrsb).le (le_sSup ⟨s, b, ?_, rfl⟩))
    intro y
    by_cases hy : g y = ⊤
    · rw [hy]; exact le_top
    · have hmem : (y, (g y).toReal) ∈ C := hepiC (EReal.le_coe_toReal hy)
      have := hsbC _ hmem
      rw [← EReal.coe_toReal hy (g_ne_bot y).ne']
      exact EReal.coe_le_coe_iff.mpr this
  have e12 : ∀ x, f₁ x = f₂ x := fun x => le_antisymm ((h13 x).trans (h32 x)) (h21 x)
  have e23 : ∀ x, f₂ x = f₃ x := fun x => le_antisymm ((h21 x).trans (h13 x)) (h32 x)
  have hf₂eq : f₂ = f₁ := funext fun x => (e12 x).symm
  have hf₃eq : f₃ = f₁ := funext fun x => ((e12 x).trans (e23 x)).symm
  refine ⟨hf₁_cc, hf₂eq ▸ hf₁_cc, hf₃eq ▸ hf₁_cc, fun x => ⟨e12 x, e23 x⟩, ?_⟩
  intro x
  unfold lscHull
  have hf₁φ : ∀ y, f₁ y ≤ convexHullFun g y := by
    intro y
    apply sInf_le_sInf
    exact Set.image_mono (fun r hr => subset_closure hr)
  apply le_antisymm
  · exact (hf₁_lsc.le_liminf x).trans
      (Filter.liminf_le_liminf (Filter.Eventually.of_forall hf₁φ))
  · refine Filter.liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    have h1 : ∃ᶠ p in 𝓝 (x, r), p ∈ convexHull ℝ (epigraph g) :=
      mem_closure_iff_frequently.mp hr
    have h2 : ∀ᶠ p in 𝓝 (x, r), b ≤ convexHullFun g p.1 :=
      (continuous_fst.tendsto (x, r)).eventually hb
    have h3 : ∃ᶠ p in 𝓝 (x, r), b ≤ ((p.2 : ℝ) : EReal) :=
      (h1.and_eventually h2).mono fun p ⟨hp1, hp2⟩ =>
        hp2.trans (FCA_aux_funFromSet_le_of_mem hp1)
    have hA : IsClosed {p : E × ℝ | b ≤ ((p.2 : ℝ) : EReal)} :=
      isClosed_le continuous_const (continuous_coe_real_ereal.comp continuous_snd)
    exact hA.closure_subset (mem_closure_iff_frequently.mpr h3)

end FCA_chap_B_2_5_2
