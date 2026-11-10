import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_4_6`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_4_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_4_6`, so the main result is `CAMA_chap_3_2_4_6.CAMA_chap_3_2_4_6`.
-/

namespace CAMA_chap_3_2_4_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Minkowski

open Set

/-- Supporting hyperplane: if the ray from `a ∈ C` in a direction `d` of the affine span of `C`
immediately leaves `C`, then some continuous linear functional is maximized over `C` at `a`
without being constant on `C`. -/
lemma exists_support_of_ray_notMem {C : Set E} (hC : Convex ℝ C) {a d : E} (ha : a ∈ C)
    (hd : d ∈ vectorSpan ℝ C) (hray : ∀ t : ℝ, 0 < t → a + t • d ∉ C) :
    ∃ f : StrongDual ℝ E, (∀ c ∈ C, f c ≤ f a) ∧ ∃ c ∈ C, f c < f a := by
  set V := vectorSpan ℝ C with hV
  set W := Vᗮ with hW
  set D : Set E := C + (W : Set E) with hD
  have hCD : C ⊆ D := fun c hc => ⟨c, hc, 0, W.zero_mem, add_zero c⟩
  have hDconv : Convex ℝ D := hC.add W.convex
  have hspan : affineSpan ℝ D = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E ⟨a, hCD ha⟩]
    refine eq_top_iff.2 ?_
    rw [← Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := V)]
    refine sup_le (vectorSpan_mono ℝ hCD) ?_
    intro w hw
    have h1 : a + w ∈ D := ⟨a, ha, w, hw, rfl⟩
    have := vsub_mem_vectorSpan ℝ h1 (hCD ha)
    simpa using this
  have hint : (interior D).Nonempty := (hDconv.interior_nonempty_iff_affineSpan_eq_top).2 hspan
  have hmemD : ∀ y ∈ D, y - a ∈ V → y ∈ C := by
    rintro y ⟨c, hc, w, hw, rfl⟩ hy
    have hwV : w ∈ V := by
      have : c + w - a - (c - a) = w := by abel
      rw [← this]
      exact V.sub_mem hy (vsub_mem_vectorSpan ℝ hc ha)
    have : w = 0 := by
      have := Submodule.inner_right_of_mem_orthogonal hwV hw
      exact inner_self_eq_zero.1 this
    simpa [this] using hc
  have hd0 : d ≠ 0 := by
    intro h0
    exact hray 1 one_pos (by simpa [h0] using ha)
  have ha' : a ∉ interior D := by
    intro h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior a h
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd0
    set t := ε / (2 * ‖d‖) with ht_def
    have ht : 0 < t := by positivity
    have hmem : a + t • d ∈ interior D := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have : a + t • d - a = t • d := by abel
      rw [this, norm_smul, Real.norm_of_nonneg ht.le, ht_def]
      field_simp
      linarith
    exact hray t ht (hmemD _ (interior_subset hmem) (by simpa using V.smul_mem t hd))
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hDconv.interior isOpen_interior ha'
  have hclos : ∀ y ∈ D, f y ≤ f a := by
    have hsub1 : D ⊆ closure (interior D) := by
      rw [hDconv.closure_interior_eq_closure_of_nonempty_interior hint]
      exact subset_closure
    have hsub : closure (interior D) ⊆ {z | f z ≤ f a} :=
      closure_minimal (fun z hz => (hf z hz).le) (isClosed_le f.continuous continuous_const)
    intro y hy
    exact hsub (hsub1 hy)
  refine ⟨f, fun c hc => hclos c (hCD hc), ?_⟩
  obtain ⟨y, hy⟩ := hint
  obtain ⟨c, hc, w, hw, rfl⟩ := interior_subset hy
  have hfw : f w = 0 := by
    by_contra hne
    have key : ∀ s : ℝ, f c + s * f w ≤ f a := by
      intro s
      have := hclos (c + s • w) ⟨c, hc, s • w, W.smul_mem s hw, rfl⟩
      simpa [map_add, map_smul] using this
    have := key ((f a - f c + 1) / f w)
    rw [div_mul_cancel₀ _ hne] at this
    linarith
  refine ⟨c, hc, ?_⟩
  have := hf _ hy
  simpa [map_add, hfw] using this

/-- A proper exposed face has smaller dimension. -/
lemma finrank_vectorSpan_toExposed_lt {C : Set E} (f : StrongDual ℝ E) {a c : E}
    (hc : c ∈ C) (ha : a ∈ f.toExposed C) (hlt : f c < f a) :
    Module.finrank ℝ (vectorSpan ℝ (f.toExposed C)) < Module.finrank ℝ (vectorSpan ℝ C) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (vectorSpan_mono ℝ (fun x hx => hx.1)) ?_
  intro heq
  have hmem : a - c ∈ vectorSpan ℝ (f.toExposed C) := by
    rw [heq]; exact vsub_mem_vectorSpan ℝ ha.1 hc
  have hker : vectorSpan ℝ (f.toExposed C) ≤ LinearMap.ker (f : E →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have h1 := hx.2 y hy.1
    have h2 := hy.2 x hx.1
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub,
      ContinuousLinearMap.coe_coe]
    linarith
  have := hker hmem
  simp only [LinearMap.mem_ker, map_sub, ContinuousLinearMap.coe_coe] at this
  linarith

omit [FiniteDimensional ℝ E] in
/-- Along a nonzero direction, a ray starting in a compact set has a last point in the set. -/
lemma exists_ray_end {C : Set E} (hC : IsCompact C) {x d : E} (hx : x ∈ C) (hd : d ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ x + t • d ∈ C ∧ ∀ s : ℝ, 0 < s → (x + t • d) + s • d ∉ C := by
  set T := {t : ℝ | x + t • d ∈ C} with hT
  have hTc : IsCompact T := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hC.isClosed.preimage (continuous_const.add (continuous_id.smul continuous_const))
    · obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨(R + ‖x‖) / ‖d‖, fun t ht => ?_⟩
      have h1 := hR ht
      rw [Metric.mem_closedBall, _root_.dist_zero_right] at h1 ⊢
      have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
      rw [le_div_iff₀ hdpos]
      have : ‖t • d‖ ≤ ‖x + t • d‖ + ‖x‖ := by
        calc ‖t • d‖ = ‖(x + t • d) - x‖ := by rw [add_sub_cancel_left]
          _ ≤ ‖x + t • d‖ + ‖x‖ := norm_sub_le _ _
      rw [norm_smul] at this
      rw [Real.norm_eq_abs] at this ⊢
      linarith
  have h0 : (0 : ℝ) ∈ T := by simpa [hT] using hx
  obtain ⟨t, ht, htmax⟩ := hTc.exists_isGreatest ⟨0, h0⟩
  refine ⟨t, htmax h0, ht, fun s hs hmem => ?_⟩
  have : t + s ∈ T := by
    show x + (t + s) • d ∈ C
    rwa [add_smul, ← add_assoc]
  have := htmax this
  linarith

/-- **Minkowski's theorem**: in finite dimension, a compact convex set is contained in (hence equal
to) the convex hull of its extreme points. -/
theorem subset_convexHull_extremePoints {C : Set E} (hCc : IsCompact C) (hCv : Convex ℝ C) :
    C ⊆ convexHull ℝ (C.extremePoints ℝ) := by
  induction h : Module.finrank ℝ (vectorSpan ℝ C) using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    have key : ∀ a ∈ C, ∀ d ∈ vectorSpan ℝ C, (∀ s : ℝ, 0 < s → a + s • d ∉ C) →
        a ∈ convexHull ℝ (C.extremePoints ℝ) := by
      intro a ha d hd hray
      obtain ⟨f, hf, c, hc, hlt⟩ := exists_support_of_ray_notMem hCv ha hd hray
      have hexp : IsExposed ℝ C (f.toExposed C) := ContinuousLinearMap.toExposed.isExposed
      have haF : a ∈ f.toExposed C := ⟨ha, hf⟩
      have hlt' := finrank_vectorSpan_toExposed_lt f hc haF hlt
      rw [h] at hlt'
      have := ih _ hlt' (hexp.isCompact hCc) (hexp.convex hCv) rfl haF
      exact convexHull_mono hexp.isExtreme.extremePoints_subset_extremePoints this
    intro x hx
    by_cases hext : x ∈ C.extremePoints ℝ
    · exact subset_convexHull ℝ _ hext
    have : ∃ x₁ ∈ C, ∃ x₂ ∈ C, x ∈ openSegment ℝ x₁ x₂ ∧ x₁ ≠ x := by
      by_contra hcon
      push_neg at hcon
      exact hext ⟨hx, fun x₁ hx₁ x₂ hx₂ hseg => hcon x₁ hx₁ x₂ hx₂ hseg⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, hseg, hne⟩ := this
    have h12 : x₁ ≠ x₂ := by
      rintro rfl
      rw [openSegment_same] at hseg
      exact hne hseg.symm
    set d := x₂ - x₁ with hd_def
    have hd0 : d ≠ 0 := sub_ne_zero.2 h12.symm
    have hdV : d ∈ vectorSpan ℝ C := vsub_mem_vectorSpan ℝ hx₂ hx₁
    obtain ⟨t₁, ht₁0, ht₁C, ht₁⟩ := exists_ray_end hCc hx hd0
    obtain ⟨t₂, ht₂0, ht₂C, ht₂⟩ := exists_ray_end hCc hx (neg_ne_zero.2 hd0)
    have ha := key _ ht₁C d hdV ht₁
    have hb := key _ ht₂C (-d) (Submodule.neg_mem _ hdV) ht₂
    rcases eq_or_lt_of_le (add_nonneg ht₁0 ht₂0) with hsum | hsum
    · have : t₁ = 0 := by linarith
      simpa [this] using ha
    · refine (convex_convexHull ℝ _).segment_subset hb ha ?_
      rw [mem_segment_iff_div]
      refine ⟨t₁, t₂, ht₁0, ht₂0, hsum, ?_⟩
      have e1 : t₁ / (t₁ + t₂) + t₂ / (t₁ + t₂) = 1 := by
        field_simp
      calc (t₁ / (t₁ + t₂)) • (x + t₂ • -d) + (t₂ / (t₁ + t₂)) • (x + t₁ • d)
          = (t₁ / (t₁ + t₂) + t₂ / (t₁ + t₂)) • x
            + (t₂ / (t₁ + t₂) * t₁ - t₁ / (t₁ + t₂) * t₂) • d := by module
        _ = x := by rw [e1]; ring_nf; simp

end Minkowski

theorem CAMA_chap_3_2_4_6
  (C : Set E)
  (s : E)
  (hC₀ : IsCompact C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  (sSup (Set.image (fun x ↦ inner ℝ s x) C) =
  sSup (Set.image (fun x ↦ inner ℝ s x) (Set.extremePoints ℝ C))) ∧
  (argmax (fun x ↦ inner ℝ s x) C =
  convexHull ℝ (argmax (fun x ↦ inner ℝ s x) (Set.extremePoints ℝ C))) := by
  set l : StrongDual ℝ E := innerSL ℝ s with hl
  have hlapp : ∀ x, l x = inner ℝ s x := fun x => innerSL_apply_apply ℝ s x
  set F := l.toExposed C with hF
  have hFeq : argmax (fun x ↦ inner ℝ s x) C = F := by
    ext x
    simp only [argmax, F, ContinuousLinearMap.toExposed, hlapp, Set.mem_setOf_eq]
  have hexp : IsExposed ℝ C F := ContinuousLinearMap.toExposed.isExposed
  have hFc : IsCompact F := hexp.isCompact hC₀
  have hFv : Convex ℝ F := hexp.convex hC₁
  obtain ⟨x₀, hx₀C, hx₀max⟩ := hC₀.exists_isMaxOn hC₂ l.continuous.continuousOn
  have hx₀F : x₀ ∈ F := ⟨hx₀C, fun y hy => hx₀max hy⟩
  have hmink := subset_convexHull_extremePoints hFc hFv
  obtain ⟨e, he⟩ : (F.extremePoints ℝ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have := hmink hx₀F
    rw [hne, convexHull_empty] at this
    exact this
  have heC : e ∈ C.extremePoints ℝ := hexp.isExtreme.extremePoints_subset_extremePoints he
  have heF : e ∈ F := he.1
  have hmax : ∀ y ∈ C, inner ℝ s y ≤ inner ℝ s e := by
    intro y hy
    rw [← hlapp, ← hlapp]
    exact heF.2 y hy
  have hargext : argmax (fun x ↦ inner ℝ s x) (C.extremePoints ℝ) = F.extremePoints ℝ := by
    rw [hexp.isExtreme.extremePoints_eq]
    ext x
    simp only [argmax, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hxC, hxmax⟩
      refine ⟨⟨hxC.1, fun y hy => ?_⟩, hxC⟩
      rw [hlapp, hlapp]
      exact (hmax y hy).trans (hxmax e heC)
    · rintro ⟨hxF, hxC⟩
      refine ⟨hxC, fun y hy => ?_⟩
      rw [← hlapp, ← hlapp]
      exact hxF.2 y hy.1
  constructor
  · have h1 : IsGreatest ((fun x ↦ inner ℝ s x) '' C) (inner ℝ s e) :=
      ⟨⟨e, heF.1, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmax y hy⟩
    have h2 : IsGreatest ((fun x ↦ inner ℝ s x) '' C.extremePoints ℝ) (inner ℝ s e) :=
      ⟨⟨e, heC, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmax y hy.1⟩
    rw [h1.csSup_eq, h2.csSup_eq]
  · rw [hFeq, hargext]
    exact Set.Subset.antisymm hmink (convexHull_min (fun x hx => hx.1) hFv)

end CAMA_chap_3_2_4_6
