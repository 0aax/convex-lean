import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_1_2`, so the main result is `FCA_chap_B_3_1_2.FCA_chap_B_3_1_2`.
-/

namespace FCA_chap_B_3_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FCA_chap_B_3_1_2
  [FiniteDimensional ℝ E]
  (f : E → EReal)
  (S : Set E)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x)
  (hS_convex : Convex ℝ S)
  (hS_compact : IsCompact S)
  (hS_subset : S ⊆ intrinsicInterior ℝ (effDom f)) :
  ∃ L ≥ 0, ∀ x ∈ S, ∀ x' ∈ S,
  abs ((f x).toReal - (f x').toReal) ≤ L * ‖x - x'‖ := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀S⟩
  · exact ⟨0, le_rfl, by simp⟩
  set A : AffineSubspace ℝ E := affineSpan ℝ (effDom f) with hA_def
  have hx₀dom : x₀ ∈ effDom f := intrinsicInterior_subset (hS_subset hx₀S)
  have hx₀A : x₀ ∈ A := subset_affineSpan ℝ _ hx₀dom
  have hmemA : ∀ v : A.direction, (v : E) + x₀ ∈ A := fun v => by
    simpa [vadd_eq_add] using AffineSubspace.vadd_mem_of_mem_direction v.2 hx₀A
  let Φ : A.direction → A := fun v => ⟨(v : E) + x₀, hmemA v⟩
  have hΦc : Continuous Φ :=
    Continuous.subtype_mk (continuous_subtype_val.add continuous_const) _
  let g : A.direction → ℝ := fun v => (f ((v : E) + x₀)).toReal
  let D : Set A.direction := {v | (v : E) + x₀ ∈ effDom f}
  let K : Set A.direction := {v | (v : E) + x₀ ∈ S}
  -- convexity
  have hepi : Convex ℝ (epigraph f) := hf_convex.2.2
  have hcoe : ∀ x ∈ effDom f, ((f x).toReal : EReal) = f x := fun x hx =>
    EReal.coe_toReal (ne_of_lt hx) (ne_of_gt (f_ne_bot x))
  have key : ∀ u ∈ D, ∀ v ∈ D, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (((a • u + b • v : A.direction) : E) + x₀) ≤ ((a * g u + b * g v : ℝ) : EReal) := by
    intro u hu v hv a b ha hb hab
    have h1 : ((u : E) + x₀, g u) ∈ epigraph f := by
      show f ((u : E) + x₀) ≤ ((f ((u : E) + x₀)).toReal : EReal)
      rw [hcoe _ hu]
    have h2 : ((v : E) + x₀, g v) ∈ epigraph f := by
      show f ((v : E) + x₀) ≤ ((f ((v : E) + x₀)).toReal : EReal)
      rw [hcoe _ hv]
    have h3 := hepi h1 h2 ha hb hab
    have h4 : ((a • u + b • v : A.direction) : E) + x₀
        = a • ((u : E) + x₀) + b • ((v : E) + x₀) := by
      have hx₀' : x₀ = a • x₀ + b • x₀ := by rw [← add_smul, hab, one_smul]
      simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
      conv_lhs => rw [hx₀']
      abel
    rw [h4]
    simpa only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd, smul_eq_mul] using h3
  have hgconv : ConvexOn ℝ D g := by
    refine ⟨?_, ?_⟩
    · intro u hu v hv a b ha hb hab
      show f (((a • u + b • v : A.direction) : E) + x₀) < ⊤
      exact lt_of_le_of_lt (key u hu v hv a b ha hb hab) (EReal.coe_lt_top _)
    · intro u hu v hv a b ha hb hab
      have := key u hu v hv a b ha hb hab
      show (f (((a • u + b • v : A.direction) : E) + x₀)).toReal ≤ a * g u + b * g v
      have h := EReal.toReal_le_toReal this (ne_of_gt (f_ne_bot _)) (EReal.coe_ne_top _)
      simpa using h
  have hgLL : LocallyLipschitzOn (interior D) g := hgconv.locallyLipschitzOn_interior
  have hKD : K ⊆ interior D := by
    intro v hv
    obtain ⟨y, hy, hyx⟩ := hS_subset hv
    have hΦv : Φ v = y := Subtype.ext hyx.symm
    have hsub : Φ ⁻¹' interior (((↑) : A → E) ⁻¹' effDom f) ⊆ interior D := by
      apply interior_maximal
      · intro w hw
        exact interior_subset (s := ((↑) : A → E) ⁻¹' effDom f) hw
      · exact isOpen_interior.preimage hΦc
    apply hsub
    rw [Set.mem_preimage, hΦv]
    exact hy
  have hKc : IsCompact K := by
    have hiso : Isometry (fun v : A.direction => (v : E) + x₀) := by
      refine Isometry.of_dist_eq fun u v => ?_
      rw [dist_add_right]
      rfl
    exact hiso.isClosedEmbedding.isCompact_preimage hS_compact
  obtain ⟨L, hL⟩ := (hgLL.mono hKD).exists_lipschitzOnWith_of_compact hKc
  refine ⟨L, L.2, ?_⟩
  intro x hx x' hx'
  have hxA : x ∈ A := subset_affineSpan ℝ _ (intrinsicInterior_subset (hS_subset hx))
  have hx'A : x' ∈ A := subset_affineSpan ℝ _ (intrinsicInterior_subset (hS_subset hx'))
  let v : A.direction :=
    ⟨x - x₀, by simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxA hx₀A⟩
  let v' : A.direction :=
    ⟨x' - x₀, by simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hx'A hx₀A⟩
  have hv : (v : E) + x₀ = x := sub_add_cancel x x₀
  have hv' : (v' : E) + x₀ = x' := sub_add_cancel x' x₀
  have hvK : v ∈ K := by show (v : E) + x₀ ∈ S; rw [hv]; exact hx
  have hv'K : v' ∈ K := by show (v' : E) + x₀ ∈ S; rw [hv']; exact hx'
  have hmain := hL.dist_le_mul v hvK v' hv'K
  have hgv : g v = (f x).toReal := by show (f ((v : E) + x₀)).toReal = _; rw [hv]
  have hgv' : g v' = (f x').toReal := by show (f ((v' : E) + x₀)).toReal = _; rw [hv']
  rw [Real.dist_eq, hgv, hgv'] at hmain
  have hd : dist v v' = ‖x - x'‖ := by
    rw [dist_eq_norm]
    show ‖((v - v' : A.direction) : E)‖ = _
    simp [v, v']
  rw [hd] at hmain
  exact hmain

end FCA_chap_B_3_1_2
