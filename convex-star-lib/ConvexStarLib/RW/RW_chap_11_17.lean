import ConvexStarLib.Defs

/-!
# `RW_chap_11_17`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_11_17` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_11_17`, so the main result is `RW_chap_11_17.RW_chap_11_17`.
-/

namespace RW_chap_11_17

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

set_option linter.unusedSectionVars false

namespace RWAux

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem fm_step (s : Finset (Module.Dual ℝ W)) (v : W) :
    ∃ s' : Finset (Module.Dual ℝ W), ∀ y : W,
      (∀ f ∈ s', f y ≤ 0) ↔ ∃ t : ℝ, 0 ≤ t ∧ ∀ f ∈ s, f (y - t • v) ≤ 0 := by
  classical
  refine ⟨s.filter (fun f => f v ≤ 0) ∪
    ((s.filter (fun f => 0 < f v)) ×ˢ (s.filter (fun f => f v < 0))).image
      (fun p => p.1 v • p.2 - p.2 v • p.1), ?_⟩
  intro y
  constructor
  · intro h
    have h1 : ∀ f ∈ s, f v ≤ 0 → f y ≤ 0 := fun f hf hfv =>
      h f (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hf, hfv⟩))
    have h2 : ∀ g ∈ s, ∀ f ∈ s, 0 < g v → f v < 0 → g v * f y - f v * g y ≤ 0 := by
      intro g hg f hf hgv hfv
      have := h (g v • f - f v • g) (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(g, f), Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hg, hgv⟩,
          Finset.mem_filter.2 ⟨hf, hfv⟩⟩, rfl⟩))
      simpa using this
    obtain ⟨L, hL⟩ : ∃ L : Finset ℝ,
        L = insert (0:ℝ) ((s.filter (fun f => 0 < f v)).image (fun f => f y / f v)) := ⟨_, rfl⟩
    have hLne : L.Nonempty := by rw [hL]; exact Finset.insert_nonempty _ _
    obtain ⟨t, htL, hmax⟩ : ∃ t ∈ L, ∀ x ∈ L, x ≤ t :=
      ⟨L.max' hLne, L.max'_mem hLne, fun x hx => L.le_max' x hx⟩
    rw [hL] at htL hmax
    have ht0 : 0 ≤ t := hmax 0 (Finset.mem_insert_self _ _)
    refine ⟨t, ht0, ?_⟩
    intro f hf
    simp only [map_sub, map_smul, smul_eq_mul]
    rcases lt_trichotomy (f v) 0 with hneg | hzero | hpos
    · rw [Finset.mem_insert, Finset.mem_image] at htL
      rcases htL with h0 | ⟨g, hg, hgt⟩
      · rw [h0]; simpa using h1 f hf hneg.le
      · rw [Finset.mem_filter] at hg
        rw [← hgt]
        have key := h2 g hg.1 f hf hg.2 hneg
        have hgv := hg.2
        have : f y - g y / g v * f v = (g v * f y - f v * g y) / g v := by
          field_simp
        rw [this]
        exact div_nonpos_of_nonpos_of_nonneg key hgv.le
    · rw [hzero]; simpa using h1 f hf hzero.le
    · have hle : f y / f v ≤ t :=
        hmax _ (Finset.mem_insert_of_mem (Finset.mem_image.2
          ⟨f, Finset.mem_filter.2 ⟨hf, hpos⟩, rfl⟩))
      have : f y = f y / f v * f v := by field_simp
      have h3 : f y / f v * f v ≤ t * f v := mul_le_mul_of_nonneg_right hle hpos.le
      linarith
  · rintro ⟨t, ht, h⟩ f hf
    have h' : ∀ g ∈ s, g y ≤ t * g v := by
      intro g hg
      have := h g hg
      simp only [map_sub, map_smul, smul_eq_mul] at this
      linarith
    rcases Finset.mem_union.1 hf with hf | hf
    · rw [Finset.mem_filter] at hf
      have := h' f hf.1
      have : t * f v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hf.2
      linarith
    · obtain ⟨⟨g, k⟩, hp, rfl⟩ := Finset.mem_image.1 hf
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨hg, hgv⟩, ⟨hk, hkv⟩⟩ := hp
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      have e1 := h' g hg
      have e2 := h' k hk
      nlinarith [mul_le_mul_of_nonneg_left e2 hgv.le, mul_le_mul_of_nonneg_left e1 (neg_nonneg.2 hkv.le)]

theorem span_nonpos (T : Set W) (l : Module.Dual ℝ W) (h : ∀ v ∈ T, l v ≤ 0) :
    ∀ x ∈ Submodule.span ℝ≥0 T, l x ≤ 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; linarith
  | smul a x _ hx =>
    rw [NNReal.smul_def, map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos a.2 hx

theorem weyl [FiniteDimensional ℝ W] (T : Finset W) :
    ∃ s : Finset (Module.Dual ℝ W), ∀ x,
      x ∈ Submodule.span ℝ≥0 (T : Set W) ↔ ∀ f ∈ s, f x ≤ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    let b := Module.finBasis ℝ W
    refine ⟨Finset.univ.image (fun i => b.coord i) ∪ Finset.univ.image (fun i => -b.coord i), ?_⟩
    intro x
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot]
    constructor
    · rintro rfl; simp
    · intro h
      rw [← b.forall_coord_eq_zero_iff]
      intro i
      have h1 := h (b.coord i) (Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
      have h2 := h (-b.coord i) (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
      simp only [LinearMap.neg_apply] at h2
      linarith
  | insert v T hv ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨s', hs'⟩ := fm_step s v
    refine ⟨s', fun y => ?_⟩
    rw [hs', Finset.coe_insert, Submodule.span_insert, Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [Submodule.mem_span_singleton] at ha
      obtain ⟨t, rfl⟩ := ha
      refine ⟨t, t.2, fun f hf => ?_⟩
      have := (hs b).1 hb f hf
      rw [NNReal.smul_def]
      simpa using this
    · rintro ⟨t, ht, h⟩
      refine ⟨(⟨t, ht⟩ : ℝ≥0) • v, Submodule.mem_span_singleton.2 ⟨_, rfl⟩, y - t • v, (hs _).2 h, ?_⟩
      rw [NNReal.smul_def]
      simp

theorem minkowski [FiniteDimensional ℝ W] (s : Finset (Module.Dual ℝ W)) :
    ∃ T : Finset W, ∀ x, (∀ f ∈ s, f x ≤ 0) ↔ x ∈ Submodule.span ℝ≥0 (T : Set W) := by
  classical
  obtain ⟨S, hS⟩ := weyl (W := Module.Dual ℝ W) s
  let e := Module.evalEquiv ℝ W
  have key : ∀ l : Module.Dual ℝ W, l ∈ Submodule.span ℝ≥0 (s : Set _) ↔
      ∀ w ∈ S.image e.symm, l w ≤ 0 := by
    intro l
    rw [hS]
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    apply forall₂_congr
    intro Ψ _
    have : Ψ l = l (e.symm Ψ) := by
      conv_lhs => rw [← e.apply_symm_apply Ψ]
      rw [Module.evalEquiv_apply, Module.Dual.eval_apply]
    rw [this]
  refine ⟨S.image e.symm, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨G, hG⟩ := weyl (S.image e.symm)
    rw [hG]
    intro g hg
    have hgT : ∀ w ∈ S.image e.symm, g w ≤ 0 := fun w hw =>
      (hG w).1 (Submodule.subset_span (by exact_mod_cast hw)) g hg
    have hgs : g ∈ Submodule.span ℝ≥0 (s : Set _) := (key g).2 hgT
    exact span_nonpos (W := Module.Dual ℝ W) (s : Set _) (Module.Dual.eval ℝ W x)
      (fun f hf => by rw [Module.Dual.eval_apply]; exact hx f hf) g hgs
  · intro hx f hf
    have hfT := (key f).1 (Submodule.subset_span hf)
    exact span_nonpos _ f (fun w hw => hfT w (by exact_mod_cast hw)) x hx

end RWAux

namespace RWAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem riesz (f : Module.Dual ℝ E) : ∃ c : E, ∀ x, f x = inner ℝ c x := by
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap f), fun x => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']

theorem riesz' (f : E →L[ℝ] ℝ) : ∃ c : E, ∀ x, f x = inner ℝ c x :=
  ⟨(InnerProductSpace.toDual ℝ E).symm f, fun x => by rw [InnerProductSpace.toDual_symm_apply]⟩

theorem isPolyhedral_fintype {ι : Type*} [Fintype ι] (a : ι → E) (b : ι → ℝ) :
    IsPolyhedral {x : E | ∀ i, inner ℝ (a i) x ≤ b i} := by
  let e := Fintype.equivFin ι
  refine ⟨⟨Fintype.card ι, fun j => a (e.symm j), fun j => b (e.symm j)⟩, ?_⟩
  ext x
  simp only [Polytope.carrier, Set.mem_setOf_eq]
  constructor
  · intro h i; simpa using h (e i)
  · intro h j; exact h _

theorem isPolyhedral_of_dual (s : Finset (Module.Dual ℝ E)) :
    IsPolyhedral {x : E | ∀ f ∈ s, f x ≤ 0} := by
  choose c hc using fun f : s => riesz (f : Module.Dual ℝ E)
  have := isPolyhedral_fintype (ι := s) c (fun _ => 0)
  convert this using 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h f; rw [← hc]; exact h f f.2
  · intro h f hf; have := h ⟨f, hf⟩; rw [← hc] at this; exact this

theorem span_iff_weyl {ι : Type*} [Fintype ι] (a : ι → E) :
    ∃ s : Finset (Module.Dual ℝ E), ∀ y,
      y ∈ Submodule.span ℝ≥0 (Set.range a) ↔ ∀ f ∈ s, f y ≤ 0 := by
  classical
  obtain ⟨s, hs⟩ := weyl (Finset.univ.image a)
  refine ⟨s, fun y => ?_⟩
  rw [← hs y]
  simp

theorem isPolyhedral_span {ι : Type*} [Fintype ι] (a : ι → E) :
    IsPolyhedral (Submodule.span ℝ≥0 (Set.range a) : Set E) := by
  obtain ⟨s, hs⟩ := span_iff_weyl a
  have : (Submodule.span ℝ≥0 (Set.range a) : Set E) = {x | ∀ f ∈ s, f x ≤ 0} := by
    ext x
    rw [SetLike.mem_coe, hs x]
    rfl
  rw [this]; exact isPolyhedral_of_dual s

theorem polar_eq_span {ι : Type*} [Fintype ι] (a : ι → E) :
    polarCone {x : E | ∀ i, inner ℝ (a i) x ≤ 0} = (Submodule.span ℝ≥0 (Set.range a) : Set E) := by
  obtain ⟨s, hspan⟩ := span_iff_weyl a
  ext y
  simp only [polarCone, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hy
    rw [hspan]
    intro f hf
    obtain ⟨c, hc⟩ := riesz f
    have hcK : ∀ i, inner ℝ (a i) c ≤ 0 := by
      intro i
      have := (hspan (a i)).1 (Submodule.subset_span ⟨i, rfl⟩) f hf
      rw [hc, real_inner_comm] at this
      exact this
    have := hy c hcK
    rw [hc, real_inner_comm]; exact this
  · intro hy x hx
    have := span_nonpos (Set.range a) (innerₗ E x)
      (by rintro _ ⟨i, rfl⟩; rw [innerₗ_apply_apply, real_inner_comm]; exact hx i) y hy
    rw [innerₗ_apply_apply, real_inner_comm] at this
    exact this

theorem cone_homog (K : Set E) (hK : IsPointedCone K) (Q : Polytope E) (hQ : Q.carrier = K) :
    K = {x : E | ∀ i, inner ℝ (Q.a i) x ≤ 0} := by
  ext x
  constructor
  · intro hx i
    by_contra hpos
    push_neg at hpos
    have hb : ∀ t : ℝ, 0 ≤ t → t * inner ℝ (Q.a i) x ≤ Q.b i := by
      intro t ht
      have : t • x ∈ K := hK.2 x hx t ht
      rw [← hQ] at this
      have := this i
      rwa [real_inner_smul_right] at this
    have := hb ((|Q.b i| + 1) / inner ℝ (Q.a i) x) (by positivity)
    rw [div_mul_cancel₀ _ hpos.ne'] at this
    linarith [le_abs_self (Q.b i)]
  · intro hx
    rw [← hQ]
    intro i
    have h0 : (0 : E) ∈ Q.carrier := hQ ▸ hK.1
    have := h0 i
    rw [inner_zero_right] at this
    linarith [hx i]

theorem polar_isPointedCone (S : Set E) : IsPointedCone (polarCone S) := by
  refine ⟨fun x _ => by simp, fun s hs t ht x hx => ?_⟩
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos ht (hs x hx)

theorem bipolar (K : Set E) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK : IsPointedCone K) : polarCone (polarCone K) = K := by
  ext x
  constructor
  · intro hx
    by_contra hxK
    obtain ⟨f, u, hfK, hfx⟩ := geometric_hahn_banach_closed_point hK_convex hK_closed hxK
    have hu : 0 < u := by have := hfK 0 hK.1; simpa using this
    have hf0 : ∀ a ∈ K, f a ≤ 0 := by
      intro a ha
      by_contra hpos
      push_neg at hpos
      have := hfK (((u + 1) / f a) • a) (hK.2 a ha _ (by positivity))
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    obtain ⟨c, hc⟩ := riesz' f
    have hcpolar : c ∈ polarCone K := fun a ha => by rw [← hc]; exact hf0 a ha
    have := hx c hcpolar
    rw [real_inner_comm, ← hc] at this
    linarith
  · intro hx s hs
    rw [real_inner_comm]
    exact hs x hx

theorem part2 (K : Set E) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K)
    (hK_cone : IsPointedCone K) : IsPolyhedral K ↔ IsPolyhedral (polarCone K) := by
  constructor
  · rintro ⟨Q, hQ⟩
    rw [cone_homog K hK_cone Q hQ, polar_eq_span]
    exact isPolyhedral_span _
  · rintro ⟨Q, hQ⟩
    have h1 := cone_homog (polarCone K) (polar_isPointedCone K) Q hQ
    have h2 := bipolar K hK_closed hK_convex hK_cone
    rw [← h2, h1, polar_eq_span]
    exact isPolyhedral_span _

end RWAux

namespace RWAux

section Homog

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

theorem cone_ineq (T : Set (W × ℝ)) (L : Module.Dual ℝ W) (c : ℝ)
    (h : ∀ z ∈ T, L z.1 ≤ c * z.2) :
    ∀ y s, (y, s) ∈ Submodule.span ℝ≥0 T → L y ≤ c * s := by
  intro y s hys
  have := span_nonpos T (L ∘ₗ LinearMap.fst ℝ W ℝ - c • LinearMap.snd ℝ W ℝ)
    (fun z hz => by
      simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_fst, LinearMap.smul_apply, LinearMap.coe_snd, smul_eq_mul]
      linarith [h z hz]) (y, s) hys
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_fst, LinearMap.smul_apply, LinearMap.coe_snd, smul_eq_mul] at this
  linarith

end Homog

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem homog (Q : Polytope E) :
    ∃ T : Finset (E × ℝ), ∀ x : E, ∀ t : ℝ,
      (0 ≤ t ∧ ∀ i, inner ℝ (Q.a i) x ≤ Q.b i * t) ↔
        (x, t) ∈ Submodule.span ℝ≥0 (T : Set (E × ℝ)) := by
  classical
  obtain ⟨T, hT⟩ := minkowski (insert (-(LinearMap.snd ℝ E ℝ))
    (Finset.univ.image (fun i => (innerₗ E (Q.a i)) ∘ₗ LinearMap.fst ℝ E ℝ -
      Q.b i • LinearMap.snd ℝ E ℝ)))
  refine ⟨T, fun x t => ?_⟩
  rw [← hT]
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
    forall_eq_or_imp, forall_exists_index, forall_apply_eq_imp_iff]
  simp only [LinearMap.neg_apply, LinearMap.coe_snd, LinearMap.sub_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_fst, innerₗ_apply_apply, LinearMap.smul_apply,
    smul_eq_mul, neg_nonpos, sub_nonpos]

theorem isPolyhedral_finset {α : Type*} (T : Finset α) (a : α → E) (b : α → ℝ) :
    IsPolyhedral {x : E | ∀ z ∈ T, inner ℝ (a z) x ≤ b z} := by
  have := isPolyhedral_fintype (ι := T) (fun z => a z.1) (fun z => b z.1)
  convert this using 1
  ext x
  simp

theorem isPolyhedral_iInter {n : ℕ} (S : Fin n → Set E) (h : ∀ i, IsPolyhedral (S i)) :
    IsPolyhedral (⋂ i, S i) := by
  choose Q hQ using h
  have := isPolyhedral_fintype (ι := Σ i, Fin (Q i).m) (fun p => (Q p.1).a p.2)
    (fun p => (Q p.1).b p.2)
  convert this using 1
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Sigma.forall]
  constructor
  · intro hx i j
    have := hx i
    rw [← hQ i] at this
    exact this j
  · intro hx i
    rw [← hQ i]
    exact fun j => hx i j

theorem bdd_of_lt_top (C : Set E) (w : E) (h : supportFunction C w < ⊤) :
    ∃ M : ℝ, ∀ x ∈ C, inner ℝ x w ≤ M := by
  refine ⟨(supportFunction C w).toReal, fun x hx => ?_⟩
  have h1 : ((inner ℝ x w : ℝ) : EReal) ≤ supportFunction C w := le_sSup ⟨x, hx, rfl⟩
  have hne : supportFunction C w ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
  rw [← EReal.coe_toReal h.ne hne] at h1
  exact EReal.coe_le_coe_iff.1 h1

theorem sf_le (C : Set E) (w : E) (r : ℝ) (h : ∀ x ∈ C, inner ℝ x w ≤ r) :
    supportFunction C w ≤ r := by
  apply sSup_le
  rintro _ ⟨x, hx, rfl⟩
  exact EReal.coe_le_coe_iff.2 (h x hx)

theorem sf_ge (C : Set E) (w : E) (x : E) (hx : x ∈ C) :
    ((inner ℝ x w : ℝ) : EReal) ≤ supportFunction C w := le_sSup ⟨x, hx, rfl⟩

end RWAux

namespace RWAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem part1_bwd (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hPL : IsPiecewiseLinear (supportFunction C)) : IsPolyhedral C := by
  obtain ⟨g, ⟨n, P, A, α, hdom, hpoly, haff⟩, hg⟩ := hPL
  have hCeq : C = ⋂ i, {x : E | ∀ w ∈ P i, inner ℝ x w ≤ A i w + α i} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx i w hw
      have hwdom : w ∈ effDom (supportFunction C) := by
        rw [hdom]; exact Set.mem_iUnion.2 ⟨i, hw⟩
      have h1 := sf_ge C w x hx
      rw [hg w hwdom, haff i w hw] at h1
      exact EReal.coe_le_coe_iff.1 h1
    · intro h
      by_contra hxC
      obtain ⟨f, u, hfC, hfx⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hxC
      obtain ⟨c, hc⟩ := riesz' f
      have hσ : supportFunction C c ≤ u := by
        apply sf_le
        intro y hy
        rw [real_inner_comm, ← hc]
        exact (hfC y hy).le
      have hcdom : c ∈ effDom (supportFunction C) := lt_of_le_of_lt hσ (EReal.coe_lt_top u)
      have hcdom' := hcdom
      rw [hdom, Set.mem_iUnion] at hcdom'
      obtain ⟨i, hci⟩ := hcdom'
      have h1 := h i c hci
      rw [← haff i c hci] at h1
      rw [hg c hcdom] at hσ
      have h3 : g c ≤ u := EReal.coe_le_coe_iff.1 hσ
      have h4 : f x = inner ℝ x c := by rw [hc, real_inner_comm]
      linarith
  rw [hCeq]
  apply isPolyhedral_iInter
  intro i
  by_cases hPi : (P i).Nonempty
  · obtain ⟨Q, hQ⟩ := hpoly i
    obtain ⟨T, hT⟩ := homog Q
    obtain ⟨p, hp⟩ := hPi
    have hTprop : ∀ z ∈ T, 0 ≤ z.2 ∧ ∀ j, inner ℝ (Q.a j) z.1 ≤ Q.b j * z.2 := by
      intro z hz
      exact (hT z.1 z.2).2 (Submodule.subset_span hz)
    have hset : {x : E | ∀ w ∈ P i, inner ℝ x w ≤ A i w + α i} =
        {x : E | ∀ z ∈ T, inner ℝ z.1 x ≤ A i z.1 + α i * z.2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx z hz
        obtain ⟨hz2, hzQ⟩ := hTprop z hz
        rcases hz2.lt_or_eq with hpos | hzero
        · have hv : z.2⁻¹ • z.1 ∈ P i := by
            rw [← hQ]
            intro j
            rw [real_inner_smul_right]
            calc z.2⁻¹ * inner ℝ (Q.a j) z.1 ≤ z.2⁻¹ * (Q.b j * z.2) :=
                  mul_le_mul_of_nonneg_left (hzQ j) (inv_nonneg.2 hpos.le)
              _ = Q.b j := by field_simp
          have := hx _ hv
          rw [real_inner_smul_right, map_smul, smul_eq_mul] at this
          have key : inner ℝ x z.1 ≤ A i z.1 + α i * z.2 := by
            have h5 := mul_le_mul_of_nonneg_left this hpos.le
            rw [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul,
              one_mul] at h5
            linarith
          rw [real_inner_comm]; exact key
        · have hline : ∀ r : ℝ, 0 ≤ r → p + r • z.1 ∈ P i := by
            intro r hr
            have hp' := hp
            rw [← hQ] at hp' ⊢
            intro j
            rw [inner_add_right, real_inner_smul_right]
            have h6 := hzQ j
            rw [← hzero, mul_zero] at h6
            have := hp' j
            nlinarith [mul_nonpos_of_nonneg_of_nonpos hr h6]
          rw [← hzero, mul_zero, add_zero, real_inner_comm]
          by_contra hcon
          push_neg at hcon
          have hd : 0 < inner ℝ x z.1 - A i z.1 := by linarith
          set K0 := A i p + α i - inner ℝ x p with hK0
          have hr : 0 ≤ (|K0| + 1) / (inner ℝ x z.1 - A i z.1) := by positivity
          have := hx _ (hline _ hr)
          rw [inner_add_right, real_inner_smul_right, map_add, map_smul, smul_eq_mul] at this
          have h7 : (|K0| + 1) / (inner ℝ x z.1 - A i z.1) * (inner ℝ x z.1 - A i z.1) =
              |K0| + 1 := div_mul_cancel₀ _ hd.ne'
          nlinarith [le_abs_self K0]
      · intro hx w hw
        have hw1 : (w, (1:ℝ)) ∈ Submodule.span ℝ≥0 (T : Set (E × ℝ)) := by
          rw [← hT]
          refine ⟨zero_le_one, fun j => ?_⟩
          rw [mul_one]
          rw [← hQ] at hw
          exact hw j
        have := cone_ineq (T : Set (E × ℝ)) (innerₗ E x - (A i : E →ₗ[ℝ] ℝ)) (α i)
          (fun z hz => by
            simp only [LinearMap.sub_apply, innerₗ_apply_apply, ContinuousLinearMap.coe_coe]
            have := hx z hz
            rw [real_inner_comm] at this
            linarith) w 1 hw1
        simp only [LinearMap.sub_apply, innerₗ_apply_apply, ContinuousLinearMap.coe_coe,
          mul_one] at this
        linarith
    rw [hset]
    exact isPolyhedral_finset T (fun z => z.1) (fun z => A i z.1 + α i * z.2)
  · rw [Set.not_nonempty_iff_eq_empty] at hPi
    rw [hPi]
    refine ⟨⟨0, Fin.elim0, Fin.elim0⟩, ?_⟩
    ext x
    simp [Polytope.carrier]

end RWAux

namespace RWAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem part1_fwd (C : Set E) (hC : C.Nonempty) (hpoly : IsPolyhedral C) :
    IsPiecewiseLinear (supportFunction C) := by
  classical
  obtain ⟨Q, hQ⟩ := hpoly
  obtain ⟨T, hT⟩ := homog Q
  have hmemC : ∀ x, x ∈ C ↔ (x, (1:ℝ)) ∈ Submodule.span ℝ≥0 (T : Set (E × ℝ)) := by
    intro x
    rw [← hT, ← hQ]
    simp only [Polytope.carrier, Set.mem_setOf_eq, mul_one, zero_le_one, true_and]
  have hTprop : ∀ z ∈ T, 0 ≤ z.2 ∧ ∀ i, inner ℝ (Q.a i) z.1 ≤ Q.b i * z.2 := by
    intro z hz
    exact (hT z.1 z.2).2 (Submodule.subset_span hz)
  have hH4 : ∀ z ∈ T, 0 < z.2 → z.2⁻¹ • z.1 ∈ C := by
    intro z hz hpos
    rw [← hQ]
    intro i
    rw [real_inner_smul_right]
    calc z.2⁻¹ * inner ℝ (Q.a i) z.1 ≤ z.2⁻¹ * (Q.b i * z.2) :=
          mul_le_mul_of_nonneg_left ((hTprop z hz).2 i) (inv_nonneg.2 hpos.le)
      _ = Q.b i := by field_simp
  have hH3 : ∀ z ∈ T, z.2 = 0 → ∀ x ∈ C, ∀ r : ℝ, 0 ≤ r → x + r • z.1 ∈ C := by
    intro z hz h0 x hx r hr
    rw [← hQ] at hx ⊢
    intro i
    rw [inner_add_right, real_inner_smul_right]
    have h6 := (hTprop z hz).2 i
    rw [h0, mul_zero] at h6
    have := hx i
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hr h6]
  obtain ⟨x0, hx0⟩ := hC
  obtain ⟨Tp, hTp⟩ : ∃ Tp : Finset (E × ℝ), Tp = T.filter (fun z => 0 < z.2) := ⟨_, rfl⟩
  have hmemTp : ∀ z, z ∈ Tp ↔ z ∈ T ∧ 0 < z.2 := by
    intro z; rw [hTp, Finset.mem_filter]
  have hTpne : Tp.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hle : ∀ z ∈ (T : Set (E × ℝ)), (0 : Module.Dual ℝ E) z.1 ≤ (-1) * z.2 := by
      intro z hz
      have hzn : z ∉ Tp := by rw [hne]; exact Finset.notMem_empty z
      rw [hmemTp] at hzn
      push_neg at hzn
      have := hzn hz
      simp only [LinearMap.zero_apply]
      linarith
    have := cone_ineq _ _ _ hle x0 1 ((hmemC x0).1 hx0)
    simp only [LinearMap.zero_apply] at this
    linarith
  have hpiece : ∀ z ∈ Tp, ∀ w, (∀ z' ∈ T, inner ℝ (z.2 • z'.1 - z'.2 • z.1) w ≤ 0) →
      ∀ x ∈ C, inner ℝ x w ≤ inner ℝ (z.2⁻¹ • z.1) w := by
    intro z hz w hw x hx
    have hz2 : 0 < z.2 := ((hmemTp z).1 hz).2
    have := cone_ineq (T : Set (E × ℝ)) (z.2 • innerₗ E w) (inner ℝ z.1 w) (fun z' hz' => by
        have h8 := hw z' hz'
        rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
          ← real_inner_comm z'.1 w] at h8
        simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
        linarith) x 1 ((hmemC x).1 hx)
    simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul, mul_one] at this
    rw [real_inner_comm x w] at this
    rw [real_inner_smul_left, le_inv_mul_iff₀ hz2]
    exact this
  have hdir : ∀ w, supportFunction C w < ⊤ → ∀ z' ∈ T, z'.2 = 0 → inner ℝ z'.1 w ≤ 0 := by
    intro w hw z' hz' h0
    obtain ⟨M, hM⟩ := bdd_of_lt_top C w hw
    by_contra hpos
    push_neg at hpos
    have hx0M := hM x0 hx0
    have hr : 0 ≤ (M - inner ℝ x0 w + 1) / inner ℝ z'.1 w := by
      apply div_nonneg _ hpos.le; linarith
    have := hM _ (hH3 z' hz' h0 x0 hx0 _ hr)
    rw [inner_add_left, real_inner_smul_left, div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  let e := Tp.equivFin
  let zf : Fin Tp.card → E × ℝ := fun j => (e.symm j).1
  have hzf : ∀ j, zf j ∈ Tp := fun j => (e.symm j).2
  refine ⟨fun w => (supportFunction C w).toReal, ⟨Tp.card,
    fun j => {w | ∀ z' ∈ T, inner ℝ ((zf j).2 • z'.1 - z'.2 • (zf j).1) w ≤ 0},
    fun j => innerSL ℝ ((zf j).2⁻¹ • (zf j).1), fun _ => 0, ?_, ?_, ?_⟩, ?_⟩
  · ext w
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hw
      have hw' : supportFunction C w < ⊤ := hw
      obtain ⟨z, hz, hzmax⟩ :=
        Finset.exists_max_image Tp (fun z => inner ℝ (z.2⁻¹ • z.1) w) hTpne
      refine ⟨e ⟨z, hz⟩, ?_⟩
      have hzz : zf (e ⟨z, hz⟩) = z := by simp [zf]
      rw [hzz]
      intro z' hz'
      have hz2 : 0 < z.2 := ((hmemTp z).1 hz).2
      rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
      rcases (hTprop z' hz').1.lt_or_eq with hpos' | hzero'
      · have := hzmax z' ((hmemTp z').2 ⟨hz', hpos'⟩)
        simp only [real_inner_smul_left] at this
        have key : z.2 * inner ℝ z'.1 w - z'.2 * inner ℝ z.1 w =
            z.2 * z'.2 * (z'.2⁻¹ * inner ℝ z'.1 w - z.2⁻¹ * inner ℝ z.1 w) := by
          field_simp
        rw [key]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      · rw [← hzero', zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos hz2.le (hdir w hw' z' hz' hzero'.symm)
    · rintro ⟨j, hj⟩
      show supportFunction C w < ⊤
      exact lt_of_le_of_lt (sf_le C w _ (hpiece (zf j) (hzf j) w hj)) (EReal.coe_lt_top _)
  · intro j
    exact isPolyhedral_finset T (fun z' => (zf j).2 • z'.1 - z'.2 • (zf j).1) (fun _ => 0)
  · intro j w hw
    have hz2 : 0 < (zf j).2 := ((hmemTp _).1 (hzf j)).2
    have heq : supportFunction C w = ((inner ℝ ((zf j).2⁻¹ • (zf j).1) w : ℝ) : EReal) :=
      le_antisymm (sf_le C w _ (hpiece (zf j) (hzf j) w hw))
        (sf_ge C w _ (hH4 (zf j) ((hmemTp _).1 (hzf j)).1 hz2))
    simp only [heq, EReal.toReal_coe, innerSL_apply_apply, add_zero]
  · intro w hw
    have hw' : supportFunction C w < ⊤ := hw
    have hne : supportFunction C w ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (sf_ge C w x0 hx0)
    exact (EReal.coe_toReal hw'.ne hne).symm

end RWAux

theorem RW_chap_11_17
  (C K : Set E)
  (hC_nonempty : C.Nonempty)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hK_closed : IsClosed K)
  (hK_convex : Convex ℝ K)
  (hK_cone : IsPointedCone K) :
  ((IsPolyhedral C ↔ IsPiecewiseLinear (supportFunction C)) ∧
    (IsPolyhedral K ↔ IsPolyhedral (polarCone K))) := by
  exact ⟨⟨RWAux.part1_fwd C hC_nonempty, RWAux.part1_bwd C hC_closed hC_convex⟩,
    RWAux.part2 K hK_closed hK_convex hK_cone⟩

end RW_chap_11_17
