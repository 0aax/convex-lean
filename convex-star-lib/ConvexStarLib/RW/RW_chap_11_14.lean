import ConvexStarLib.Defs

/-!
# `RW_chap_11_14`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_11_14` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_11_14`, so the main result is `RW_chap_11_14.RW_chap_11_14`.
-/

namespace RW_chap_11_14

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

namespace RW1114

/-! ### General polyhedral sets (finitely many linear inequalities) -/

/-- Polyhedral set in a real vector space. -/
def IsPolyD {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (ℓ : ι → (V →ₗ[ℝ] ℝ)) (c : ι → ℝ), S = {p | ∀ i, ℓ i p ≤ c i}

section PolyD
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

-- BEGIN polyBasic
theorem isPolyD_univ : IsPolyD (Set.univ : Set V) := by
  refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, ?_⟩
  ext p
  simp

theorem isPolyD_empty : IsPolyD (∅ : Set V) := by
  refine ⟨Unit, inferInstance, fun _ => 0, fun _ => -1, ?_⟩
  ext p
  simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, LinearMap.zero_apply, false_iff,
    not_forall, not_le]
  exact ⟨(), by norm_num⟩

theorem isPolyD_halfspace (ℓ : V →ₗ[ℝ] ℝ) (c : ℝ) : IsPolyD {p : V | ℓ p ≤ c} := by
  refine ⟨Unit, inferInstance, fun _ => ℓ, fun _ => c, ?_⟩
  ext p
  simp

theorem IsPolyD.inter {S T : Set V} (hS : IsPolyD S) (hT : IsPolyD T) : IsPolyD (S ∩ T) := by
  obtain ⟨ι, _, ℓ, c, rfl⟩ := hS
  obtain ⟨ι', _, ℓ', c', rfl⟩ := hT
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim ℓ ℓ', Sum.elim c c', ?_⟩
  ext p
  simp [Sum.forall]

theorem isPolyD_iInter {ι : Type} [Fintype ι] {S : ι → Set V} (h : ∀ i, IsPolyD (S i)) :
    IsPolyD (⋂ i, S i) := by
  choose κ hκ ℓ c hS using h
  letI : ∀ i, Fintype (κ i) := hκ
  refine ⟨Σ i, κ i, inferInstance, fun x => ℓ x.1 x.2, fun x => c x.1 x.2, ?_⟩
  ext p
  simp only [Set.mem_iInter, Set.mem_setOf_eq, hS, Sigma.forall]

theorem IsPolyD.preimage_affine {S : Set W} (hS : IsPolyD S) (L : V →ₗ[ℝ] W) (w : W) :
    IsPolyD {p | L p + w ∈ S} := by
  obtain ⟨ι, _, ℓ, c, rfl⟩ := hS
  refine ⟨ι, inferInstance, fun i => (ℓ i).comp L, fun i => c i - ℓ i w, ?_⟩
  ext p
  simp only [Set.mem_setOf_eq, LinearMap.comp_apply, map_add, le_sub_iff_add_le]

theorem IsPolyD.convex {S : Set V} (hS : IsPolyD S) : Convex ℝ S := by
  obtain ⟨ι, _, ℓ, c, rfl⟩ := hS
  have h : {p : V | ∀ i, ℓ i p ≤ c i} = ⋂ i, {p | ℓ i p ≤ c i} := by
    ext p; simp
  rw [h]
  exact convex_iInter fun i => convex_halfSpace_le (ℓ i).isLinear (c i)
-- END polyBasic

-- BEGIN fourierMotzkin
theorem fm_step {X : Type*} [AddCommGroup X] [Module ℝ X] {S : Set X} (hS : IsPolyD S)
    (u : X) : IsPolyD {p | ∃ t : ℝ, p + t • u ∈ S} := by
  classical
  obtain ⟨ι, hι, ℓ, c, rfl⟩ := hS
  refine ⟨{k : ι // ℓ k u = 0} ⊕ {ij : ι × ι // 0 < ℓ ij.1 u ∧ ℓ ij.2 u < 0}, inferInstance,
    Sum.elim (fun k => ℓ k.1) (fun ij => (ℓ ij.1.1 u) • ℓ ij.1.2 - (ℓ ij.1.2 u) • ℓ ij.1.1),
    Sum.elim (fun k => c k.1) (fun ij => (ℓ ij.1.1 u) * c ij.1.2 - (ℓ ij.1.2 u) * c ij.1.1),
    ?_⟩
  ext p
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul]
  constructor
  · rintro ⟨t, ht⟩ i
    rcases i with ⟨k, hk⟩ | ⟨⟨i, j⟩, hi, hj⟩
    · simp only [Sum.elim_inl]
      have := ht k
      rw [hk, mul_zero, add_zero] at this
      exact this
    · simp only [Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      have h1 := ht i
      have h2 := ht j
      nlinarith [mul_le_mul_of_nonneg_left h2 hi.le,
        mul_le_mul_of_nonneg_left h1 (neg_nonneg.mpr hj.le)]
  · intro h
    have hinl : ∀ k, ℓ k u = 0 → ℓ k p ≤ c k := fun k hk => by
      have := h (Sum.inl ⟨k, hk⟩)
      simpa using this
    have hinr : ∀ i j, 0 < ℓ i u → ℓ j u < 0 →
        ℓ i u * ℓ j p - ℓ j u * ℓ i p ≤ ℓ i u * c j - ℓ j u * c i := fun i j hi hj => by
      have := h (Sum.inr ⟨(i, j), hi, hj⟩)
      simpa using this
    by_cases hN : ∃ j, ℓ j u < 0
    · have hne : (Finset.univ.filter (fun j => ℓ j u < 0)).Nonempty := by
        obtain ⟨j, hj⟩ := hN
        exact ⟨j, by simp [hj]⟩
      obtain ⟨j0, hj0mem, hj0max⟩ :=
        Finset.exists_max_image _ (fun j => (c j - ℓ j p) / ℓ j u) hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj0mem hj0max
      refine ⟨(c j0 - ℓ j0 p) / ℓ j0 u, fun k => ?_⟩
      have ht : (c j0 - ℓ j0 p) / ℓ j0 u * ℓ j0 u = c j0 - ℓ j0 p := by
        field_simp [hj0mem.ne]
      rcases lt_trichotomy (ℓ k u) 0 with hk | hk | hk
      · have := hj0max k hk
        rw [div_le_iff_of_neg hk] at this
        linarith
      · rw [hk, mul_zero, add_zero]; exact hinl k hk
      · have h3 := hinr k j0 hk hj0mem
        by_contra hcon
        push_neg at hcon
        have h4 := mul_lt_mul_of_pos_left hcon (neg_pos.mpr hj0mem)
        nlinarith
    · push_neg at hN
      refine ⟨-∑ i, |(c i - ℓ i p) / ℓ i u|, fun k => ?_⟩
      rcases lt_trichotomy (ℓ k u) 0 with hk | hk | hk
      · exact absurd (hN k) (not_le.mpr hk)
      · rw [hk, mul_zero, add_zero]; exact hinl k hk
      · have h1 : |(c k - ℓ k p) / ℓ k u| ≤ ∑ i, |(c i - ℓ i p) / ℓ i u| :=
          Finset.single_le_sum (f := fun i => |(c i - ℓ i p) / ℓ i u|)
            (fun i _ => abs_nonneg _) (Finset.mem_univ k)
        have h2 : -∑ i, |(c i - ℓ i p) / ℓ i u| ≤ (c k - ℓ k p) / ℓ k u := by
          have := neg_abs_le ((c k - ℓ k p) / ℓ k u)
          linarith
        rw [le_div_iff₀ hk] at h2
        linarith

theorem fm_multi {X : Type*} [AddCommGroup X] [Module ℝ X] (n : ℕ) :
    ∀ (u : Fin n → X) {S : Set X}, IsPolyD S →
      IsPolyD {p | ∃ t : Fin n → ℝ, p + ∑ i, t i • u i ∈ S} := by
  induction n with
  | zero =>
    intro u S hS
    simpa using hS
  | succ n ih =>
    intro u S hS
    have h := fm_step (ih (fun i => u i.succ) hS) (u 0)
    convert h using 1
    ext p
    simp only [Set.mem_setOf_eq, Fin.sum_univ_succ]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t 0, fun i => t i.succ, by rwa [add_assoc]⟩
    · rintro ⟨a, t, ht⟩
      refine ⟨Fin.cons a t, ?_⟩
      simp only [Fin.cons_zero, Fin.cons_succ]
      rwa [← add_assoc]

/-- Fourier–Motzkin elimination: projections of polyhedral sets are polyhedral. -/
theorem IsPolyD.image_snd [FiniteDimensional ℝ V] {S : Set (V × W)} (hS : IsPolyD S) :
    IsPolyD (Prod.snd '' S) := by
  set b := Module.finBasis ℝ V
  have hT := fm_multi (Module.finrank ℝ V) (fun i => ((b i, 0) : V × W)) hS
  have h := hT.preimage_affine (LinearMap.inr ℝ V W) 0
  convert h using 1
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq, LinearMap.inr_apply, add_zero]
  constructor
  · rintro ⟨⟨v, w'⟩, hv, rfl⟩
    refine ⟨fun i => b.repr v i, ?_⟩
    have : ((0 : V), w') + ∑ i, b.repr v i • ((b i, 0) : V × W) = (v, w') := by
      ext
      · simp [Prod.fst_sum, b.sum_repr v]
      · simp [Prod.snd_sum]
    rw [this]; exact hv
  · rintro ⟨t, ht⟩
    exact ⟨_, ht, by simp [Prod.snd_sum]⟩

theorem IsPolyD.image_fst [FiniteDimensional ℝ W] {S : Set (V × W)} (hS : IsPolyD S) :
    IsPolyD (Prod.fst '' S) := by
  have h := hS.preimage_affine ((LinearMap.snd ℝ W V).prod (LinearMap.fst ℝ W V)) 0
  have h2 := IsPolyD.image_snd h
  convert h2 using 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, LinearMap.prod_apply, LinearMap.snd_apply,
    LinearMap.fst_apply, add_zero, Pi.prod]
  constructor
  · rintro ⟨⟨v', w⟩, hv, rfl⟩
    exact ⟨(w, v'), hv, rfl⟩
  · rintro ⟨⟨w, v'⟩, hv, rfl⟩
    exact ⟨(v', w), hv, rfl⟩
-- END fourierMotzkin

end PolyD

-- BEGIN polyTopo
theorem IsPolyD.isClosed {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {S : Set V} (hS : IsPolyD S) : IsClosed S := by
  obtain ⟨ι, _, ℓ, c, rfl⟩ := hS
  have h : {p : V | ∀ i, ℓ i p ≤ c i} = ⋂ i, {p | ℓ i p ≤ c i} := by
    ext p; simp
  rw [h]
  exact isClosed_iInter fun i =>
    isClosed_le (LinearMap.continuous_of_finiteDimensional (ℓ i)) continuous_const

theorem isPolyD_iff_isPolyhedral (S : Set E) : IsPolyD S ↔ IsPolyhedral S := by
  constructor
  · rintro ⟨ι, _, ℓ, c, rfl⟩
    let e := Fintype.equivFin ι
    refine ⟨⟨Fintype.card ι, fun k => (InnerProductSpace.toDual ℝ E).symm
      (LinearMap.toContinuousLinearMap (ℓ (e.symm k))), fun k => c (e.symm k)⟩, ?_⟩
    ext x
    simp only [Polytope.carrier, Set.mem_setOf_eq, InnerProductSpace.toDual_symm_apply,
      LinearMap.coe_toContinuousLinearMap']
    constructor
    · intro h i
      have := h (e i)
      simpa using this
    · intro h k
      exact h (e.symm k)
  · rintro ⟨P, rfl⟩
    refine ⟨Fin P.m, inferInstance, fun i => innerₛₗ ℝ (P.a i), P.b, ?_⟩
    ext x
    simp [Polytope.carrier]

/-- closure of a convex set cut by finitely many strict halfspaces -/
theorem subset_closure_inter_strict {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {S : Set V} (hS : Convex ℝ S) {ι : Type*} [Finite ι]
    (ℓ : ι → V →ₗ[ℝ] ℝ) (c : ι → ℝ) {z : V} (hz : z ∈ S) (hzl : ∀ i, c i < ℓ i z) :
    S ∩ {p | ∀ i, c i ≤ ℓ i p} ⊆ closure (S ∩ {p | ∀ i, c i < ℓ i p}) := by
  rintro y ⟨hyS, hyl⟩
  have hcont : Continuous (fun t : ℝ => y + t • (z - y)) := by fun_prop
  have htend : Filter.Tendsto (fun t : ℝ => y + t • (z - y)) (𝓝[>] 0) (𝓝 y) :=
    (hcont.tendsto' 0 y (by simp)).mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto htend
  have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 := nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, h1] with t ht0 ht1
  have ht0' : (0:ℝ) < t := ht0
  refine ⟨hS.add_smul_sub_mem hyS hz ⟨le_of_lt ht0', le_of_lt ht1⟩, ?_⟩
  intro i
  simp only [map_add, map_smul, map_sub, smul_eq_mul]
  have h1 := hyl i
  have h2 := hzl i
  nlinarith [mul_pos ht0' (sub_pos.mpr h2), mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr h1)]
-- END polyTopo

/-! ### Farkas lemma / normal cones of polyhedra -/

-- BEGIN farkas
theorem fk_isPolyD_eq {V : Type*} [AddCommGroup V] [Module ℝ V] (ℓ : V →ₗ[ℝ] ℝ) (c : ℝ) :
    IsPolyD {p : V | ℓ p = c} := by
  have : {p : V | ℓ p = c} = {p : V | ℓ p ≤ c} ∩ {p : V | (-ℓ) p ≤ -c} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, LinearMap.neg_apply, neg_le_neg_iff]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  rw [this]
  exact (isPolyD_halfspace _ _).inter (isPolyD_halfspace _ _)

theorem isPolyD_cone {m : ℕ} (a : Fin m → E) (J : Finset (Fin m)) :
    IsPolyD {w : E | ∃ μ : Fin m → ℝ, (∀ k, 0 ≤ μ k) ∧ (∀ k, k ∉ J → μ k = 0) ∧
      w = ∑ k, μ k • a k} := by
  classical
  set b := Module.finBasis ℝ E with hb
  set L : E × (Fin m → ℝ) →ₗ[ℝ] E :=
    LinearMap.fst ℝ E (Fin m → ℝ) - (Fintype.linearCombination ℝ a) ∘ₗ LinearMap.snd ℝ E (Fin m → ℝ)
    with hL
  have hLapp : ∀ p : E × (Fin m → ℝ), L p = p.1 - ∑ k, p.2 k • a k := by
    intro p
    simp [hL, Fintype.linearCombination_apply]
  set T : Set (E × (Fin m → ℝ)) :=
    (⋂ k, {p | (-(LinearMap.proj k ∘ₗ LinearMap.snd ℝ E (Fin m → ℝ))) p ≤ 0}) ∩
    ((⋂ k, {p | ((if k ∈ J then (0:ℝ) else 1) • (LinearMap.proj k ∘ₗ LinearMap.snd ℝ E (Fin m → ℝ))) p ≤ 0}) ∩
    (⋂ i, {p | (b.coord i ∘ₗ L) p = 0})) with hT
  have hTpoly : IsPolyD T := by
    refine IsPolyD.inter (isPolyD_iInter fun k => isPolyD_halfspace _ _)
      (IsPolyD.inter (isPolyD_iInter fun k => isPolyD_halfspace _ _)
        (isPolyD_iInter fun i => fk_isPolyD_eq _ _))
  have heq : {w : E | ∃ μ : Fin m → ℝ, (∀ k, 0 ≤ μ k) ∧ (∀ k, k ∉ J → μ k = 0) ∧
      w = ∑ k, μ k • a k} = Prod.fst '' T := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image, hT, Set.mem_inter_iff, Set.mem_iInter,
      LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      LinearMap.snd_apply, Function.eval, LinearMap.smul_apply, smul_eq_mul, Prod.exists,
      neg_nonpos]
    constructor
    · rintro ⟨μ, h0, hJ, rfl⟩
      refine ⟨_, μ, ⟨h0, fun k => ?_, fun i => ?_⟩, rfl⟩
      · by_cases hk : k ∈ J
        · simp [hk]
        · simp [hk, hJ k hk]
      · rw [hLapp]; simp
    · rintro ⟨w', μ, ⟨h0, hJ, hE⟩, rfl⟩
      refine ⟨μ, h0, fun k hk => ?_, ?_⟩
      · have := hJ k
        simp only [hk, if_false, one_mul] at this
        exact le_antisymm this (h0 k)
      · have : L (w', μ) = 0 := by
          rw [← b.forall_coord_eq_zero_iff]
          exact hE
        rw [hLapp, sub_eq_zero] at this
        exact this
  rw [heq]
  exact hTpoly.image_fst

theorem normal_cone_polytope (P : Polytope E) {x w : E} (hx : x ∈ P.carrier)
    (hw : ∀ y ∈ P.carrier, inner ℝ w (y - x) ≤ 0) :
    ∃ μ : Fin P.m → ℝ, (∀ k, 0 ≤ μ k) ∧ (∀ k, μ k ≠ 0 → inner ℝ (P.a k) x = P.b k) ∧
      w = ∑ k, μ k • P.a k := by
  classical
  set J : Finset (Fin P.m) := Finset.univ.filter (fun k => inner ℝ (P.a k) x = P.b k) with hJdef
  have hmemJ : ∀ k, k ∈ J ↔ inner ℝ (P.a k) x = P.b k := by
    intro k; simp [hJdef]
  obtain ⟨ι, hι, ℓ, c, hC⟩ := isPolyD_cone P.a J
  suffices hwC : w ∈ {w : E | ∃ μ : Fin P.m → ℝ, (∀ k, 0 ≤ μ k) ∧ (∀ k, k ∉ J → μ k = 0) ∧
      w = ∑ k, μ k • P.a k} by
    obtain ⟨μ, h0, hJ, hsum⟩ := hwC
    refine ⟨μ, h0, fun k hk => ?_, hsum⟩
    by_contra hne
    exact hk (hJ k (fun h => hne ((hmemJ k).1 h)))
  rw [hC]
  intro i
  by_contra hlt
  push_neg at hlt
  -- 0 ∈ cone
  have hc0 : 0 ≤ c i := by
    have h0mem : (0 : E) ∈ {w : E | ∃ μ : Fin P.m → ℝ, (∀ k, 0 ≤ μ k) ∧ (∀ k, k ∉ J → μ k = 0) ∧
        w = ∑ k, μ k • P.a k} := ⟨0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩
    rw [hC] at h0mem
    simpa using h0mem i
  -- generators
  have hgen : ∀ k ∈ J, ℓ i (P.a k) ≤ 0 := by
    intro k hk
    have hmem : ∀ t : ℝ, 0 ≤ t → t • P.a k ∈ {w : E | ∃ μ : Fin P.m → ℝ, (∀ k, 0 ≤ μ k) ∧
        (∀ k, k ∉ J → μ k = 0) ∧ w = ∑ k, μ k • P.a k} := by
      intro t ht
      refine ⟨fun j => if j = k then t else 0, fun j => ?_, fun j hj => ?_, ?_⟩
      · by_cases hjk : j = k <;> simp [hjk, ht]
      · have : j ≠ k := fun h => hj (h ▸ hk)
        simp [this]
      · simp [ite_smul]
    by_contra hpos
    push_neg at hpos
    have := hmem ((c i + 1) / ℓ i (P.a k)) (div_nonneg (by linarith) hpos.le)
    rw [hC] at this
    have h2 := this i
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at h2
    linarith
  -- Riesz vector
  set d : E := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap (ℓ i)) with hd
  have hdapp : ∀ y : E, inner ℝ d y = ℓ i y := by
    intro y
    rw [hd, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  have key : ∀ k, ∀ᶠ ε in 𝓝[>] (0:ℝ), inner ℝ (P.a k) (x + ε • d) ≤ P.b k := by
    intro k
    by_cases hk : k ∈ J
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [inner_add_right, inner_smul_right, real_inner_comm d (P.a k), hdapp]
      have h1 := hgen k hk
      have h2 := (hmemJ k).1 hk
      have h3 : (0:ℝ) < ε := hε
      nlinarith
    · have hlt' : inner ℝ (P.a k) x < P.b k :=
        lt_of_le_of_ne (hx k) (fun h => hk ((hmemJ k).2 h))
      have hcont : Continuous (fun ε : ℝ => inner ℝ (P.a k) (x + ε • d)) := by fun_prop
      have h0 : inner ℝ (P.a k) (x + (0:ℝ) • d) < P.b k := by simpa using hlt'
      have hev : ∀ᶠ ε in 𝓝 (0:ℝ), inner ℝ (P.a k) (x + ε • d) < P.b k :=
        hcont.continuousAt.eventually_lt continuousAt_const h0
      exact (hev.filter_mono nhdsWithin_le_nhds).mono (fun ε h => h.le)
  obtain ⟨ε, hε, hεpos⟩ := ((Filter.eventually_all.2 key).and self_mem_nhdsWithin).exists
  have hy : x + ε • d ∈ P.carrier := hε
  have h1 := hw _ hy
  rw [add_sub_cancel_left, inner_smul_right, real_inner_comm d w, hdapp] at h1
  have h3 : (0:ℝ) < ε := hεpos
  nlinarith
-- END farkas

/-! ### Subgradients -/

/-- `v` is a subgradient of `f` at `x` (and `f x` is finite). -/
def IsSubgrad (f : E → EReal) (x v : E) : Prop :=
  ∃ r : ℝ, f x = (r : EReal) ∧ ∀ y, ((r + inner ℝ v (y - x) : ℝ) : EReal) ≤ f y

/-- gradient of `x ↦ 1/2 ⟪x, A x⟫ + ⟪a, x⟫`. -/
noncomputable def gradQ (A : E →L[ℝ] E) (a x : E) : E :=
  (1 / 2 : ℝ) • (A x + (ContinuousLinearMap.adjoint A) x) + a

-- BEGIN subgradBasic
/-- Fenchel–Young equality. -/
theorem conjugate_eq_of_isSubgrad {f : E → EReal} {x v : E} {r : ℝ} (hx : f x = (r : EReal))
    (h : ∀ y, ((r + inner ℝ v (y - x) : ℝ) : EReal) ≤ f y) :
    conjugate f v = ((inner ℝ v x - r : ℝ) : EReal) := by
  unfold conjugate
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨y, -, rfl⟩
    have hy := h y
    have hin : inner ℝ v (y - x) = inner ℝ v y - inner ℝ v x := inner_sub_right _ _ _
    dsimp only
    generalize f y = t at hy ⊢
    induction t using EReal.rec with
    | bot => exact absurd hy (by simp)
    | coe t =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      rw [EReal.coe_le_coe_iff] at hy
      linarith
    | top => simp
  · apply le_sSup
    refine ⟨x, Set.mem_univ _, ?_⟩
    simp only [hx]
    rw [EReal.coe_sub]

theorem isClosed_subgrad_graph (f : E → EReal) (hf_proper : IsProper f)
    (hf_lsc : LowerSemicontinuous f) : IsClosed {p : E × E | IsSubgrad f p.1 p.2} := by
  obtain ⟨hbot, y0, hy0⟩ := hf_proper
  have hT : {p : E × E | IsSubgrad f p.1 p.2} =
      ⋂ y ∈ effDom f, {q : E × E | f q.1 ≤
        (((f y).toReal - inner ℝ q.2 (y - q.1) : ℝ) : EReal)} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨r, hr, hineq⟩ y hy
      have hy' : f y < ⊤ := hy
      have hfy : f y = (((f y).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal hy'.ne (hbot y).ne').symm
      have := hineq y
      rw [hfy, EReal.coe_le_coe_iff] at this
      rw [hr, EReal.coe_le_coe_iff]
      linarith
    · intro hq
      have hlt : f q.1 < ⊤ := lt_of_le_of_lt (hq y0 hy0) (EReal.coe_lt_top _)
      refine ⟨(f q.1).toReal, (EReal.coe_toReal hlt.ne (hbot q.1).ne').symm, fun y => ?_⟩
      by_cases hy : y ∈ effDom f
      · have hy' : f y < ⊤ := hy
        have hfy : f y = (((f y).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal hy'.ne (hbot y).ne').symm
        have := hq y hy
        rw [← EReal.coe_toReal hlt.ne (hbot q.1).ne', EReal.coe_le_coe_iff] at this
        rw [hfy, EReal.coe_le_coe_iff]
        linarith
      · have : f y = ⊤ := by
          simp only [effDom, Set.mem_setOf_eq, not_lt, top_le_iff] at hy
          exact hy
        rw [this]; exact le_top
  rw [hT]
  apply isClosed_biInter
  intro y _
  have hepi := (hf_lsc.comp (continuous_fst : Continuous (Prod.fst : E × E → E))).isClosed_epigraph
  have hcont : Continuous (fun q : E × E =>
      (q, (((f y).toReal - inner ℝ q.2 (y - q.1) : ℝ) : EReal))) := by
    refine continuous_id.prodMk (continuous_coe_real_ereal.comp ?_)
    fun_prop
  exact hepi.preimage hcont
-- END subgradBasic

-- BEGIN coverage
theorem cv_le_of_forall (a C : ℝ) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → a ≤ t * C) : a ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have hC : 0 < C := by have := h 1 one_pos le_rfl; linarith
  set t : ℝ := min 1 (a / (2 * C)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hcon (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ a / (2 * C) := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : t * C ≤ a / (2 * C) * C := mul_le_mul_of_nonneg_right ht2 hC.le
  have h3 : a / (2 * C) * C = a / 2 := by field_simp
  linarith

omit [FiniteDimensional ℝ E] in
theorem cv_conj_bound (f : E → EReal) {v : E} (hv : conjugate f v < ⊤) :
    ∃ c : ℝ, ∀ y (s : ℝ), f y = s → inner ℝ v y - s ≤ c := by
  obtain ⟨c, hc1, -⟩ := EReal.lt_iff_exists_real_btwn.mp hv
  refine ⟨c, fun y s hy => ?_⟩
  have h1 : ((inner ℝ v y : ℝ) : EReal) - f y ≤ conjugate f v :=
    le_sSup (Set.mem_image_of_mem _ (Set.mem_univ y))
  rw [hy, ← EReal.coe_sub] at h1
  exact (EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt h1 hc1)).le

omit [FiniteDimensional ℝ E] in
theorem cv_convex_ineq (f : E → EReal) (hf_convex : ConvexEReal f) {x y : E} {r s t : ℝ}
    (hx : f x = r) (hy : f y = s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (x + t • (y - x)) ≤ (((1 - t) * r + t * s : ℝ) : EReal) := by
  have hp : (x, r) ∈ epigraph f := by simp [epigraph, hx]
  have hq : (y, s) ∈ epigraph f := by simp [epigraph, hy]
  have := hf_convex hp hq (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
  have heq : (1 - t) • x + t • y = x + t • (y - x) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [heq] at this
  exact this

theorem cv_exists_min (f : E → EReal) (hf_bot : ∀ x, ⊥ < f x) (hf_lsc : LowerSemicontinuous f)
    (v : E) (c : ℝ) (hc : ∀ y (s : ℝ), f y = s → inner ℝ v y - s ≤ c)
    (x0 : E) (r0 : ℝ) (hx0 : f x0 = r0) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : E, ∃ r : ℝ, f x = r ∧ ∀ y (s : ℝ), f y = s →
      r + (ε / 2 * ‖x‖ ^ 2 - inner ℝ v x) ≤ s + (ε / 2 * ‖y‖ ^ 2 - inner ℝ v y) := by
  have hq_cont : Continuous (fun x : E => ε / 2 * ‖x‖ ^ 2 - inner ℝ v x) := by fun_prop
  have hg_lsc : LowerSemicontinuous
      (fun x : E => f x + (((ε / 2 * ‖x‖ ^ 2 - inner ℝ v x : ℝ)) : EReal)) := by
    apply LowerSemicontinuous.add' hf_lsc
    · exact (continuous_coe_real_ereal.comp hq_cont).lowerSemicontinuous
    · intro x
      apply EReal.continuousAt_add
      · right; exact EReal.coe_ne_bot _
      · right; exact EReal.coe_ne_top _
  set M : ℝ := r0 + (ε / 2 * ‖x0‖ ^ 2 - inner ℝ v x0) + c with hM
  set R : ℝ := 2 * (|M| + 1) / ε + 1 + ‖x0‖ with hR
  have hK : IsCompact (Metric.closedBall (0 : E) R) := isCompact_closedBall 0 R
  have hx0K : x0 ∈ Metric.closedBall (0:E) R := by
    rw [mem_closedBall_zero_iff, hR]
    have : 0 ≤ 2 * (|M| + 1) / ε := by positivity
    linarith
  obtain ⟨x, hxK, hxmin⟩ := (hg_lsc.lowerSemicontinuousOn _).exists_isMinOn ⟨x0, hx0K⟩ hK
  have hgx_le := isMinOn_iff.mp hxmin x0 hx0K
  have hfx_ne_top : f x ≠ ⊤ := by
    intro h
    simp only [h, hx0, EReal.top_add_coe, ← EReal.coe_add] at hgx_le
    exact EReal.coe_ne_top _ (top_le_iff.mp hgx_le)
  set r := (f x).toReal with hr
  have hfx : f x = r := (EReal.coe_toReal hfx_ne_top (hf_bot x).ne').symm
  refine ⟨x, r, hfx, ?_⟩
  intro y s hy
  have h1 : r + (ε / 2 * ‖x‖ ^ 2 - inner ℝ v x) ≤ r0 + (ε / 2 * ‖x0‖ ^ 2 - inner ℝ v x0) := by
    simp only [hfx, hx0, ← EReal.coe_add] at hgx_le
    exact EReal.coe_le_coe_iff.mp hgx_le
  by_cases hyK : y ∈ Metric.closedBall (0:E) R
  · have := isMinOn_iff.mp hxmin y hyK
    simp only [hfx, hy, ← EReal.coe_add] at this
    exact EReal.coe_le_coe_iff.mp this
  · have h2 : inner ℝ v y - s ≤ c := hc y s hy
    have hyR : R < ‖y‖ := by
      rw [mem_closedBall_zero_iff, not_le] at hyK; exact hyK
    have hpos : 0 ≤ 2 * (|M| + 1) / ε := by positivity
    have hy1 : 1 ≤ ‖y‖ := by rw [hR] at hyR; have := norm_nonneg x0; linarith
    have hy2 : 2 * (|M| + 1) / ε ≤ ‖y‖ := by rw [hR] at hyR; have := norm_nonneg x0; linarith
    have hy3 : 2 * (|M| + 1) ≤ ε * ‖y‖ := by
      rw [div_le_iff₀ hε] at hy2; linarith
    have hy4 : ‖y‖ ≤ ‖y‖ ^ 2 := by nlinarith
    have hy5 : ε * ‖y‖ ≤ ε * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_left hy4 hε.le
    have hMabs : M ≤ |M| := le_abs_self M
    rw [hM] at hMabs
    nlinarith

omit [FiniteDimensional ℝ E] in
theorem cv_subgrad_of_min (f : E → EReal) (hf_convex : ConvexEReal f) (hf_bot : ∀ x, ⊥ < f x)
    (v x : E) (r ε : ℝ) (hfx : f x = r)
    (hmin : ∀ y (s : ℝ), f y = s →
      r + (ε / 2 * ‖x‖ ^ 2 - inner ℝ v x) ≤ s + (ε / 2 * ‖y‖ ^ 2 - inner ℝ v y)) :
    IsSubgrad f x (v - ε • x) := by
  refine ⟨r, hfx, fun y => ?_⟩
  induction hfy : f y using EReal.rec with
  | bot => exact absurd hfy (hf_bot y).ne'
  | top => exact le_top
  | coe s =>
    rw [EReal.coe_le_coe_iff]
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
        r + inner ℝ (v - ε • x) (y - x) - s ≤ t * (ε / 2 * ‖y - x‖ ^ 2) := by
      intro t ht0 ht1
      have hconv := cv_convex_ineq f hf_convex hfx hfy ht0.le ht1
      have hne_top : f (x + t • (y - x)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hconv
      have hu : f (x + t • (y - x)) = ((f (x + t • (y - x))).toReal : EReal) :=
        (EReal.coe_toReal hne_top (hf_bot _).ne').symm
      have hu_le : (f (x + t • (y - x))).toReal ≤ (1 - t) * r + t * s := by
        rw [hu] at hconv; exact EReal.coe_le_coe_iff.mp hconv
      have hm := hmin (x + t • (y - x)) _ hu
      have hnorm : ‖x + t • (y - x)‖ ^ 2
          = ‖x‖ ^ 2 + 2 * t * inner ℝ x (y - x) + t ^ 2 * ‖y - x‖ ^ 2 := by
        rw [norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      have hinner : inner ℝ v (x + t • (y - x)) = inner ℝ v x + t * inner ℝ v (y - x) := by
        rw [inner_add_right, real_inner_smul_right]
      have hinner2 : inner ℝ (v - ε • x) (y - x) = inner ℝ v (y - x) - ε * inner ℝ x (y - x) := by
        rw [inner_sub_left, real_inner_smul_left]
      rw [hnorm, hinner] at hm
      rw [hinner2]
      have h3 : t * (r + (inner ℝ v (y - x) - ε * inner ℝ x (y - x)) - s)
          ≤ t * (t * (ε / 2 * ‖y - x‖ ^ 2)) := by nlinarith
      exact le_of_mul_le_mul_left h3 ht0
    have := cv_le_of_forall _ _ key
    linarith

/-- every point of the domain of `f*` is a limit of subgradients of `f`. -/
theorem mem_closure_range_subgrad (f : E → EReal) (hf_proper : IsProper f)
    (hf_lsc : LowerSemicontinuous f) (hf_convex : ConvexEReal f) {v : E}
    (hv : conjugate f v < ⊤) : v ∈ closure {w : E | ∃ x, IsSubgrad f x w} := by
  obtain ⟨hf_bot, x0, hx0⟩ := hf_proper
  have hx0' : f x0 < ⊤ := hx0
  have hr0 : f x0 = ((f x0).toReal : EReal) := (EReal.coe_toReal hx0'.ne (hf_bot x0).ne').symm
  set r0 := (f x0).toReal with hr0_def
  obtain ⟨c, hc⟩ := cv_conj_bound f hv
  have hA : 0 ≤ r0 - inner ℝ v x0 + c := by have := hc x0 r0 hr0; linarith
  set K : ℝ := r0 - inner ℝ v x0 + c + ‖x0‖ ^ 2 / 2 with hK
  have hK0 : 0 ≤ K := by have := sq_nonneg ‖x0‖; linarith
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have hden : 0 < 4 * (K + 1) + δ ^ 2 := by positivity
  set ε : ℝ := δ ^ 2 / (4 * (K + 1) + δ ^ 2) with hε_def
  have hε : 0 < ε := div_pos (by positivity) hden
  have hε1 : ε ≤ 1 := by rw [hε_def, div_le_one hden]; linarith
  have hε_eq : ε * (4 * (K + 1) + δ ^ 2) = δ ^ 2 := div_mul_cancel₀ _ hden.ne'
  obtain ⟨x, r, hfx, hmin⟩ := cv_exists_min f hf_bot hf_lsc v c hc x0 r0 hr0 ε hε
  refine ⟨v - ε • x, ⟨x, cv_subgrad_of_min f hf_convex hf_bot v x r ε hfx hmin⟩, ?_⟩
  rw [dist_eq_norm, _root_.sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have h1 := hmin x0 r0 hr0
  have h2 := hc x r hfx
  have h3 : ε * ‖x‖ ^ 2 ≤ 2 * K := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hε1) (sq_nonneg ‖x0‖)]
  have h4 : (ε * ‖x‖) ^ 2 < δ ^ 2 := by
    have : (ε * ‖x‖) ^ 2 = ε * (ε * ‖x‖ ^ 2) := by ring
    rw [this]
    calc ε * (ε * ‖x‖ ^ 2) ≤ ε * (2 * K) := mul_le_mul_of_nonneg_left h3 hε.le
      _ < δ ^ 2 := by nlinarith [mul_pos hε (show 0 < 2 * K + 4 + δ ^ 2 by positivity)]
  nlinarith [norm_nonneg x, mul_nonneg hε.le (norm_nonneg x)]
-- END coverage

-- BEGIN subgradPLQ
theorem sp_quad_expand (A : E →L[ℝ] E) (a x d : E) (α t : ℝ) :
    (1 / 2 : ℝ) * inner ℝ (x + t • d) (A (x + t • d)) + inner ℝ a (x + t • d) + α
      = ((1 / 2 : ℝ) * inner ℝ x (A x) + inner ℝ a x + α) + t * inner ℝ (gradQ A a x) d
        + t ^ 2 / 2 * inner ℝ d (A d) := by
  simp only [gradQ, map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm (A x) d]
  ring

omit [FiniteDimensional ℝ E] in
theorem sp_convex_ineq {f : E → EReal} (hf : ConvexEReal f) {x y : E} {r s : ℝ}
    (hx : f x ≤ r) (hy : f y ≤ s) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • x + t • y) ≤ (((1 - t) * r + t * s : ℝ) : EReal) := by
  have h := hf (show (x, r) ∈ epigraph f from hx) (show (y, s) ∈ epigraph f from hy)
    (sub_nonneg.2 ht1) ht0 (by ring)
  simpa [epigraph] using h

omit [FiniteDimensional ℝ E] in
theorem sp_poly_convex {S : Set E} (h : IsPolyhedral S) : Convex ℝ S := by
  obtain ⟨Q, rfl⟩ := h
  intro x hx y hy s t hs ht hst
  simp only [Polytope.carrier, Set.mem_setOf_eq] at hx hy ⊢
  intro i
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have h1 := hx i
  have h2 := hy i
  have h3 : s * Q.b i + t * Q.b i = Q.b i := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]

omit [FiniteDimensional ℝ E] in
theorem sp_poly_closed {S : Set E} (h : IsPolyhedral S) : IsClosed S := by
  obtain ⟨Q, rfl⟩ := h
  have : Q.carrier = ⋂ i, {x : E | inner ℝ (Q.a i) x ≤ Q.b i} := by
    ext x; simp [Polytope.carrier]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (continuous_const.inner continuous_id) continuous_const

theorem sp_le_zero_of_forall {c k : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → c ≤ t * k) : c ≤ 0 := by
  by_contra hc
  push_neg at hc
  have hpos : 0 < c + |k| := add_pos_of_pos_of_nonneg hc (abs_nonneg k)
  have ht0 : 0 < c / (c + |k|) := div_pos hc hpos
  have ht1 : c / (c + |k|) ≤ 1 := (div_le_one hpos).2 (by linarith [abs_nonneg k])
  have h1 := h _ ht0 ht1
  have h2 : c / (c + |k|) * k ≤ c / (c + |k|) * |k| :=
    mul_le_mul_of_nonneg_left (le_abs_self k) ht0.le
  have h3 : c / (c + |k|) * |k| < c := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith
  linarith

/-- local characterization of subgradients of a convex PLQ function. -/
theorem isSubgrad_iff_of_PLQ (f : E → EReal) (hf_proper : IsProper f)
    (hf_convex : ConvexEReal f)
    {n : ℕ} (P : Fin n → Set E) (A : Fin n → E →L[ℝ] E) (a : Fin n → E) (α : Fin n → ℝ)
    (hdom : effDom f = ⋃ i, P i) (hpoly : ∀ i, IsPolyhedral (P i))
    (hval : ∀ i : Fin n, ∀ x ∈ P i,
      f x = (((1 / 2 : ℝ) * inner ℝ x (A i x) + inner ℝ (a i) x + α i) : EReal))
    (x v : E) :
    IsSubgrad f x v ↔ (x ∈ effDom f ∧ ∀ j, x ∈ P j → ∀ y ∈ P j,
      inner ℝ (v - gradQ (A j) (a j) x) (y - x) ≤ 0) := by
  have hval' : ∀ i : Fin n, ∀ z ∈ P i,
      f z = ((((1 / 2 : ℝ) * inner ℝ z (A i z) + inner ℝ (a i) z + α i : ℝ)) : EReal) := by
    intro i z hz
    rw [hval i z hz]
    norm_cast
  clear hval
  have hzeq : ∀ (t : ℝ) (y : E), (1 - t) • x + t • y = x + t • (y - x) := by
    intro t y
    rw [smul_sub, sub_smul, one_smul]; abel
  constructor
  · rintro ⟨r, hfx, hsub⟩
    refine ⟨?_, ?_⟩
    · show f x < ⊤
      rw [hfx]; exact EReal.coe_lt_top r
    · intro j hxj y hyj
      have hconv := sp_poly_convex (hpoly j)
      have hr : r = (1 / 2 : ℝ) * inner ℝ x (A j x) + inner ℝ (a j) x + α j := by
        have := hval' j x hxj
        rw [hfx] at this
        exact_mod_cast this
      apply sp_le_zero_of_forall (k := inner ℝ (y - x) (A j (y - x)) / 2)
      intro t ht0 ht1
      have hz : x + t • (y - x) ∈ P j := by
        rw [← hzeq]
        exact hconv hxj hyj (sub_nonneg.2 ht1) ht0.le (by ring)
      have h1 := hsub (x + t • (y - x))
      rw [hval' j _ hz] at h1
      have h2 : r + inner ℝ v (x + t • (y - x) - x) ≤ (1 / 2 : ℝ) * inner ℝ (x + t • (y - x))
          (A j (x + t • (y - x))) + inner ℝ (a j) (x + t • (y - x)) + α j := by
        exact_mod_cast h1
      rw [sp_quad_expand, ← hr, add_sub_cancel_left, real_inner_smul_right] at h2
      have h3 : t * (inner ℝ v (y - x) - inner ℝ (gradQ (A j) (a j) x) (y - x)) ≤
          t * (t * (inner ℝ (y - x) (A j (y - x)) / 2)) := by
        nlinarith
      rw [inner_sub_left]
      exact le_of_mul_le_mul_left h3 ht0
  · rintro ⟨hx, hfo⟩
    have hxtop : f x < ⊤ := hx
    have hxbot : ⊥ < f x := hf_proper.1 x
    have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hxtop.ne hxbot.ne').symm
    set r : ℝ := (f x).toReal with hr_def
    refine ⟨r, hfx, ?_⟩
    -- Step 1: inside pieces containing x
    have step1 : ∀ j, x ∈ P j → ∀ y ∈ P j, ((r + inner ℝ v (y - x) : ℝ) : EReal) ≤ f y := by
      intro j hxj y hyj
      have hr : r = (1 / 2 : ℝ) * inner ℝ x (A j x) + inner ℝ (a j) x + α j := by
        have := hval' j x hxj
        rw [hfx] at this
        exact_mod_cast this
      have hy' := sp_quad_expand (A j) (a j) x (y - x) (α j) 1
      rw [one_smul, add_sub_cancel] at hy'
      have hK : 0 ≤ inner ℝ (y - x) (A j (y - x)) := by
        have hmid : (1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y ∈ P j :=
          sp_poly_convex (hpoly j) hxj hyj (by norm_num) (by norm_num) (by norm_num)
        have hc := sp_convex_ineq hf_convex (le_of_eq (hval' j x hxj)) (le_of_eq (hval' j y hyj))
          (t := 1 / 2) (by norm_num) (by norm_num)
        rw [hval' j _ hmid] at hc
        have hc' := (EReal.coe_le_coe_iff).1 hc
        rw [hzeq, sp_quad_expand] at hc'
        nlinarith
      have hg := hfo j hxj y hyj
      rw [inner_sub_left] at hg
      rw [hval' j y hyj]
      have : r + inner ℝ v (y - x) ≤ (1 / 2 : ℝ) * inner ℝ y (A j y) + inner ℝ (a j) y + α j := by
        nlinarith
      exact_mod_cast this
    -- Step 2: local
    have hSclosed : IsClosed (⋃ j ∈ {j : Fin n | x ∉ P j}, P j) :=
      Set.Finite.isClosed_biUnion (Set.toFinite _) (fun j _ => sp_poly_closed (hpoly j))
    have hxS : x ∉ ⋃ j ∈ {j : Fin n | x ∉ P j}, P j := by
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
      intro j hj hxj; exact hj hxj
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hSclosed.isOpen_compl x hxS
    have step2 : ∀ y, f y < ⊤ → dist y x < δ → ((r + inner ℝ v (y - x) : ℝ) : EReal) ≤ f y := by
      intro y hy hyx
      have hy' : y ∈ effDom f := hy
      rw [hdom] at hy'
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hy'
      by_cases hxj : x ∈ P j
      · exact step1 j hxj y hyj
      · exfalso
        exact hball (Metric.mem_ball.2 hyx) (Set.mem_biUnion (x := j) hxj hyj)
    -- Step 3: global
    intro y
    by_cases hytop : f y = ⊤
    · rw [hytop]; exact le_top
    have hybot : ⊥ < f y := hf_proper.1 y
    have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hytop hybot.ne').symm
    set s : ℝ := (f y).toReal with hs_def
    have hpos : 0 < δ + ‖y - x‖ := add_pos_of_pos_of_nonneg hδ (norm_nonneg _)
    have ht0 : 0 < δ / (δ + ‖y - x‖) := div_pos hδ hpos
    have ht1 : δ / (δ + ‖y - x‖) ≤ 1 := (div_le_one hpos).2 (by linarith [norm_nonneg (y - x)])
    have htd : δ / (δ + ‖y - x‖) * ‖y - x‖ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith [norm_nonneg (y - x)]
    set t := δ / (δ + ‖y - x‖) with ht_def
    have hc := sp_convex_ineq hf_convex (le_of_eq hfx) (le_of_eq hfy) ht0.le ht1
    rw [hzeq] at hc
    have hztop : f (x + t • (y - x)) < ⊤ := lt_of_le_of_lt hc (EReal.coe_lt_top _)
    have hzdist : dist (x + t • (y - x)) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      exact htd
    have h3 := le_trans (step2 _ hztop hzdist) hc
    have h4 : r + inner ℝ v (x + t • (y - x) - x) ≤ (1 - t) * r + t * s := by exact_mod_cast h3
    rw [add_sub_cancel_left, real_inner_smul_right] at h4
    rw [hfy]
    have h5 : t * (r + inner ℝ v (y - x)) ≤ t * s := by linarith
    exact_mod_cast le_of_mul_le_mul_left h5 ht0
-- END subgradPLQ

-- BEGIN graphDecomp
/-- linear functional `p ↦ ⟪u, p.1⟫` on `E × E`. -/
noncomputable def gd_lin (u : E) : E × E →ₗ[ℝ] ℝ := (innerₛₗ ℝ u).comp (LinearMap.fst ℝ E E)

omit [FiniteDimensional ℝ E] in
theorem gd_lin_apply (u : E) (p : E × E) : gd_lin u p = inner ℝ u p.1 := by
  simp [gd_lin]

theorem gd_polyD_ge {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type} [Fintype ι]
    (ℓ : ι → V →ₗ[ℝ] ℝ) (c : ι → ℝ) : IsPolyD {p : V | ∀ i, c i ≤ ℓ i p} :=
  ⟨ι, inferInstance, fun i => -ℓ i, fun i => -c i, by ext p; simp⟩

theorem gd_gradQ_affine (A : E →L[ℝ] E) (a : E) :
    ∃ L : E × E →ₗ[ℝ] E, ∃ w : E, ∀ p : E × E, L p + w = p.2 - gradQ A a p.1 := by
  refine ⟨LinearMap.snd ℝ E E - ((1 / 2 : ℝ) • (A.toLinearMap +
    (ContinuousLinearMap.adjoint A).toLinearMap)) ∘ₗ LinearMap.fst ℝ E E, -a, fun p => ?_⟩
  simp [gradQ]
  abel

/-- the polyhedral piece of the graph attached to an active set `J`. -/
def gd_N (Q : Polytope E) (A : E →L[ℝ] E) (a : E) (J : Finset (Fin Q.m)) : Set (E × E) :=
  {p | p.1 ∈ Q.carrier ∧ (∀ k ∈ J, Q.b k ≤ inner ℝ (Q.a k) p.1) ∧
    p.2 - gradQ A a p.1 ∈ {w : E | ∃ μ : Fin Q.m → ℝ, (∀ k, 0 ≤ μ k) ∧
      (∀ k, k ∉ J → μ k = 0) ∧ w = ∑ k, μ k • Q.a k}}

theorem gd_N_polyD (Q : Polytope E) (A : E →L[ℝ] E) (a : E) (J : Finset (Fin Q.m)) :
    IsPolyD (gd_N Q A a J) := by
  obtain ⟨L, w, hL⟩ := gd_gradQ_affine A a
  have h1 : IsPolyD {p : E × E | ∀ k, gd_lin (Q.a k) p ≤ Q.b k} :=
    ⟨Fin Q.m, inferInstance, fun k => gd_lin (Q.a k), Q.b, rfl⟩
  have h2 := gd_polyD_ge (V := E × E) (ι := J) (fun k => gd_lin (Q.a k)) (fun k => Q.b k)
  have h3 := (isPolyD_cone Q.a J).preimage_affine L w
  have : gd_N Q A a J = {p : E × E | ∀ k, gd_lin (Q.a k) p ≤ Q.b k} ∩
      {p : E × E | ∀ k : J, Q.b k ≤ gd_lin (Q.a k) p} ∩
      {p | L p + w ∈ {w : E | ∃ μ : Fin Q.m → ℝ, (∀ k, 0 ≤ μ k) ∧
      (∀ k, k ∉ J → μ k = 0) ∧ w = ∑ k, μ k • Q.a k}} := by
    ext p
    simp only [gd_N, Polytope.carrier, gd_lin_apply, hL, Set.mem_setOf_eq, Set.mem_inter_iff,
      Subtype.forall, and_assoc]
  rw [this]
  exact (h1.inter h2).inter h3

theorem gd_N_normal {Q : Polytope E} {A : E →L[ℝ] E} {a : E} {J : Finset (Fin Q.m)}
    {p : E × E} (hp : p ∈ gd_N Q A a J) :
    ∀ y ∈ Q.carrier, inner ℝ (p.2 - gradQ A a p.1) (y - p.1) ≤ 0 := by
  obtain ⟨_, hJ, μ, hμ0, hμJ, hμeq⟩ := hp
  intro y hy
  rw [hμeq, sum_inner]
  apply Finset.sum_nonpos
  intro k _
  rw [real_inner_smul_left, inner_sub_right]
  by_cases hk : k ∈ J
  · have h1 := hJ k hk
    have h2 : inner ℝ (Q.a k) y ≤ Q.b k := hy k
    exact mul_nonpos_of_nonneg_of_nonpos (hμ0 k) (by linarith)
  · rw [hμJ k hk]; simp

theorem gd_N_of_normal (Q : Polytope E) (A : E →L[ℝ] E) (a : E) {p : E × E}
    (hx : p.1 ∈ Q.carrier)
    (h : ∀ y ∈ Q.carrier, inner ℝ (p.2 - gradQ A a p.1) (y - p.1) ≤ 0) :
    ∃ J, p ∈ gd_N Q A a J := by
  classical
  obtain ⟨μ, hμ0, hμact, hμeq⟩ := normal_cone_polytope Q hx h
  refine ⟨Finset.univ.filter (fun k => μ k ≠ 0), hx, ?_, μ, hμ0, ?_, hμeq⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact (hμact k hk).ge
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hk
    exact hk

/-- per-piece constraint sets, indexed by a violated inequality or an active set. -/
def gd_S (Q : Polytope E) (A : E →L[ℝ] E) (a : E) :
    Fin Q.m ⊕ Finset (Fin Q.m) → Set (E × E)
  | Sum.inl _ => Set.univ
  | Sum.inr J => gd_N Q A a J

noncomputable def gd_ℓ (Q : Polytope E) : Fin Q.m ⊕ Finset (Fin Q.m) → (E × E →ₗ[ℝ] ℝ)
  | Sum.inl k => gd_lin (Q.a k)
  | Sum.inr _ => 0

def gd_c (Q : Polytope E) : Fin Q.m ⊕ Finset (Fin Q.m) → ℝ
  | Sum.inl k => Q.b k
  | Sum.inr _ => -1

theorem gd_S_polyD (Q : Polytope E) (A : E →L[ℝ] E) (a : E) (s : Fin Q.m ⊕ Finset (Fin Q.m)) :
    IsPolyD (gd_S Q A a s) := by
  cases s with
  | inl k => exact isPolyD_univ
  | inr J => exact gd_N_polyD Q A a J

theorem gd_exists_s (Q : Polytope E) (A : E →L[ℝ] E) (a : E) (p : E × E)
    (H : p.1 ∈ Q.carrier → ∀ y ∈ Q.carrier, inner ℝ (p.2 - gradQ A a p.1) (y - p.1) ≤ 0) :
    ∃ s, p ∈ gd_S Q A a s ∧ gd_c Q s < gd_ℓ Q s p ∧
      (p.1 ∈ Q.carrier → ∃ J, s = Sum.inr J) := by
  by_cases hx : p.1 ∈ Q.carrier
  · obtain ⟨J, hJ⟩ := gd_N_of_normal Q A a hx (H hx)
    exact ⟨Sum.inr J, hJ, by simp [gd_c, gd_ℓ], fun _ => ⟨J, rfl⟩⟩
  · have : ∃ k, Q.b k < inner ℝ (Q.a k) p.1 := by
      simp only [Polytope.carrier, Set.mem_setOf_eq, not_forall, not_le] at hx
      exact hx
    obtain ⟨k, hk⟩ := this
    exact ⟨Sum.inl k, Set.mem_univ _, by simpa [gd_c, gd_ℓ, gd_lin_apply] using hk,
      fun h => absurd h hx⟩

theorem gd_strict_normal {Q : Polytope E} {A : E →L[ℝ] E} {a : E}
    {s : Fin Q.m ⊕ Finset (Fin Q.m)} {p : E × E} (hS : p ∈ gd_S Q A a s)
    (hc : gd_c Q s < gd_ℓ Q s p) (hx : p.1 ∈ Q.carrier) :
    ∀ y ∈ Q.carrier, inner ℝ (p.2 - gradQ A a p.1) (y - p.1) ≤ 0 := by
  cases s with
  | inl k =>
    have h1 : Q.b k < inner ℝ (Q.a k) p.1 := by simpa [gd_c, gd_ℓ, gd_lin_apply] using hc
    have h2 : inner ℝ (Q.a k) p.1 ≤ Q.b k := hx k
    exact absurd h2 (not_le.mpr h1)
  | inr J => exact gd_N_normal hS

/-- closed constraint set attached to a choice `σ` for every piece. -/
def gd_K {n : ℕ} (Q : Fin n → Polytope E) (A : Fin n → E →L[ℝ] E) (a : Fin n → E)
    (σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m)) : Set (E × E) :=
  (⋂ j, gd_S (Q j) (A j) (a j) (σ j)) ∩ {p | ∀ j, gd_c (Q j) (σ j) ≤ gd_ℓ (Q j) (σ j) p}

/-- strict version of `gd_K`. -/
def gd_K' {n : ℕ} (Q : Fin n → Polytope E) (A : Fin n → E →L[ℝ] E) (a : Fin n → E)
    (σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m)) : Set (E × E) :=
  (⋂ j, gd_S (Q j) (A j) (a j) (σ j)) ∩ {p | ∀ j, gd_c (Q j) (σ j) < gd_ℓ (Q j) (σ j) p}

theorem gd_K_polyD {n : ℕ} (Q : Fin n → Polytope E) (A : Fin n → E →L[ℝ] E) (a : Fin n → E)
    (σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m)) : IsPolyD (gd_K Q A a σ) :=
  (isPolyD_iInter fun j => gd_S_polyD (Q j) (A j) (a j) (σ j)).inter
    (gd_polyD_ge (fun j => gd_ℓ (Q j) (σ j)) (fun j => gd_c (Q j) (σ j)))

theorem gd_K'_subset {n : ℕ} (Q : Fin n → Polytope E) (A : Fin n → E →L[ℝ] E) (a : Fin n → E)
    (σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m)) : gd_K' Q A a σ ⊆ gd_K Q A a σ :=
  fun _ hp => ⟨hp.1, fun j => (hp.2 j).le⟩

theorem gd_K_subset_closure {n : ℕ} (Q : Fin n → Polytope E) (A : Fin n → E →L[ℝ] E)
    (a : Fin n → E) (σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m)) {z : E × E}
    (hz : z ∈ gd_K' Q A a σ) : gd_K Q A a σ ⊆ closure (gd_K' Q A a σ) :=
  subset_closure_inter_strict
    (isPolyD_iInter fun j => gd_S_polyD (Q j) (A j) (a j) (σ j)).convex
    (fun j => gd_ℓ (Q j) (σ j)) (fun j => gd_c (Q j) (σ j)) hz.1 hz.2

theorem gd_K_fst {n : ℕ} {Q : Fin n → Polytope E} {A : Fin n → E →L[ℝ] E} {a : Fin n → E}
    {σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m)} {j : Fin n}
    {J : Finset (Fin (Q j).m)} (hj : σ j = Sum.inr J) {p : E × E} (hp : p ∈ gd_K Q A a σ) :
    p.1 ∈ (Q j).carrier := by
  have h := Set.mem_iInter.mp hp.1 j
  rw [hj] at h
  exact h.1

/-- the graph of the subdifferential of a convex PLQ function is a finite union of
polyhedral sets. -/
theorem subgrad_graph_decomp (f : E → EReal) (hf_proper : IsProper f)
    (hf_lsc : LowerSemicontinuous f) (hf_convex : ConvexEReal f)
    {n : ℕ} (P : Fin n → Set E) (A : Fin n → E →L[ℝ] E) (a : Fin n → E) (α : Fin n → ℝ)
    (hdom : effDom f = ⋃ i, P i) (hpoly : ∀ i, IsPolyhedral (P i))
    (hval : ∀ i : Fin n, ∀ x ∈ P i,
      f x = (((1 / 2 : ℝ) * inner ℝ x (A i x) + inner ℝ (a i) x + α i) : EReal)) :
    ∃ (N : ℕ) (G : Fin N → Set (E × E)) (j : Fin N → Fin n),
      (∀ k, IsPolyD (G k)) ∧ (∀ k, ∀ p ∈ G k, p.1 ∈ P (j k)) ∧
      {p : E × E | IsSubgrad f p.1 p.2} = ⋃ k, G k := by
  classical
  have hpoly' := hpoly
  choose Q hQ using hpoly'
  have hiff := isSubgrad_iff_of_PLQ f hf_proper hf_convex P A a α hdom hpoly hval
  set gph : Set (E × E) := {p : E × E | IsSubgrad f p.1 p.2} with hgph
  have hclosed : IsClosed gph := isClosed_subgrad_graph f hf_proper hf_lsc
  -- strict sets with an active piece lie in the graph
  have hstrict : ∀ σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m),
      (∃ j J, σ j = Sum.inr J) → gd_K' Q A a σ ⊆ gph := by
    rintro σ ⟨j0, J0, hj0⟩ p hp
    show IsSubgrad f p.1 p.2
    rw [hiff]
    refine ⟨?_, fun j hx y hy => ?_⟩
    · rw [hdom, Set.mem_iUnion]
      refine ⟨j0, ?_⟩
      rw [← hQ j0]
      exact gd_K_fst hj0 (gd_K'_subset Q A a σ hp)
    · rw [← hQ j] at hx hy
      exact gd_strict_normal (Set.mem_iInter.mp hp.1 j) (hp.2 j) hx y hy
  -- every point of the graph lies in some strict set with an active piece
  have hexists : ∀ p ∈ gph, ∃ σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m),
      (∃ j J, σ j = Sum.inr J) ∧ p ∈ gd_K' Q A a σ := by
    intro p hp
    have hp' : IsSubgrad f p.1 p.2 := hp
    rw [hiff] at hp'
    obtain ⟨hdomx, hnorm⟩ := hp'
    have H : ∀ j, ∃ s, p ∈ gd_S (Q j) (A j) (a j) s ∧ gd_c (Q j) s < gd_ℓ (Q j) s p ∧
        (p.1 ∈ (Q j).carrier → ∃ J, s = Sum.inr J) := fun j =>
      gd_exists_s (Q j) (A j) (a j) p (fun hx y hy => by
        rw [hQ j] at hx hy
        exact hnorm j hx y hy)
    choose σ hσ using H
    refine ⟨σ, ?_, Set.mem_iInter.mpr fun j => (hσ j).1, fun j => (hσ j).2.1⟩
    rw [hdom, Set.mem_iUnion] at hdomx
    obtain ⟨j, hj⟩ := hdomx
    exact ⟨j, (hσ j).2.2 (by rw [hQ j]; exact hj)⟩
  -- index set
  let ι := {σ : (j : Fin n) → Fin (Q j).m ⊕ Finset (Fin (Q j).m) //
    (∃ j J, σ j = Sum.inr J) ∧ gd_K Q A a σ ⊆ gph}
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => gd_K Q A a (e.symm k).1,
    fun k => (e.symm k).2.1.choose, fun k => gd_K_polyD Q A a _, ?_, ?_⟩
  · intro k p hp
    rw [← hQ]
    obtain ⟨J, hJ⟩ := (e.symm k).2.1.choose_spec
    exact gd_K_fst hJ hp
  · apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨σ, hσ, hpσ⟩ := hexists p hp
      have hsub : gd_K Q A a σ ⊆ gph :=
        (gd_K_subset_closure Q A a σ hpσ).trans
          ((closure_mono (hstrict σ hσ)).trans hclosed.closure_subset)
      rw [Set.mem_iUnion]
      refine ⟨e ⟨σ, hσ, hsub⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      exact gd_K'_subset Q A a σ hpσ
    · intro p hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨k, hk⟩ := hp
      exact (e.symm k).2.2 hk
-- END graphDecomp

-- BEGIN orth
theorem or_first_order (f : E → EReal) {P : Set E} (hP : Convex ℝ P) (A : E →L[ℝ] E) (a : E)
    (α : ℝ)
    (hval : ∀ x ∈ P, f x = (((1 / 2 : ℝ) * inner ℝ x (A x) + inner ℝ a x + α) : EReal))
    {x v : E} (hx : x ∈ P) (hsub : IsSubgrad f x v) {y : E} (hy : y ∈ P) :
    0 ≤ inner ℝ (gradQ A a x - v) (y - x) := by
  obtain ⟨r, hr, hineq⟩ := hsub
  have hrq : r = (1 / 2 : ℝ) * inner ℝ x (A x) + inner ℝ a x + α := by
    have h := hr.symm.trans (hval x hx)
    exact_mod_cast h
  suffices H : ∀ d : E, (∀ t : ℝ, 0 < t → t ≤ 1 → x + t • d ∈ P) →
      0 ≤ inner ℝ (gradQ A a x - v) d by
    exact H (y - x) (fun t ht0 ht1 => hP.add_smul_sub_mem hx hy ⟨ht0.le, ht1⟩)
  intro d hdP
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ t * inner ℝ (gradQ A a x - v) d + t ^ 2 / 2 * inner ℝ d (A d) := by
    intro t ht0 ht1
    have hz : x + t • d ∈ P := hdP t ht0 ht1
    have h1 := hineq (x + t • d)
    rw [hval _ hz] at h1
    have h2 : r + inner ℝ v (x + t • d - x) ≤ (1 / 2 : ℝ) * inner ℝ (x + t • d)
        (A (x + t • d)) + inner ℝ a (x + t • d) + α := by
      exact_mod_cast h1
    rw [hrq, add_sub_cancel_left] at h2
    have c1 := real_inner_comm (A x) d
    have c2 := ContinuousLinearMap.adjoint_inner_left A d x
    simp only [gradQ, map_add, map_smul, inner_add_left, inner_add_right, inner_sub_left,
      real_inner_smul_left, real_inner_smul_right] at h2 ⊢
    rw [c1] at h2
    rw [c2]
    linarith
  by_contra hneg
  push_neg at hneg
  set c := inner ℝ (gradQ A a x - v) d with hc
  set K := inner ℝ d (A d) with hK
  set t := min 1 (-c / (|K| + 1)) with ht
  have hK1 : 0 < |K| + 1 := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hK1)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -c / (|K| + 1) := min_le_right _ _
  have h := key t ht0 ht1
  have e0 : t * (|K| + 1) ≤ -c := by rwa [le_div_iff₀ hK1] at ht2
  have e1 : t ^ 2 * K ≤ t ^ 2 * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) (sq_nonneg t)
  have e2 : t * (t * (|K| + 1)) ≤ t * (-c) := mul_le_mul_of_nonneg_left e0 ht0.le
  have e3 : 0 < t * (-c) := mul_pos ht0 (by linarith)
  nlinarith [sq_nonneg t]

/-- first-order relations along a convex set of subgradient pairs inside one piece. -/
theorem subgrad_orth (f : E → EReal) {P : Set E} (hP : Convex ℝ P) (A : E →L[ℝ] E) (a : E)
    (α : ℝ)
    (hval : ∀ x ∈ P, f x = (((1 / 2 : ℝ) * inner ℝ x (A x) + inner ℝ a x + α) : EReal))
    {G : Set (E × E)} (hG : Convex ℝ G) (hGP : ∀ p ∈ G, p.1 ∈ P)
    (hGsub : ∀ p ∈ G, IsSubgrad f p.1 p.2) :
    ∀ p ∈ G, ∀ p' ∈ G, inner ℝ (gradQ A a p.1 - p.2) (p'.1 - p.1) = 0 := by
  have fo : ∀ p ∈ G, ∀ y ∈ P, 0 ≤ inner ℝ (gradQ A a p.1 - p.2) (y - p.1) :=
    fun p hp y hy => or_first_order f hP A a α hval (hGP p hp) (hGsub p hp) hy
  intro p hp p' hp'
  have aff : ∀ s : ℝ, gradQ A a (p + s • (p' - p)).1 - (p + s • (p' - p)).2 =
      (gradQ A a p.1 - p.2) + s • ((gradQ A a p'.1 - p'.2) - (gradQ A a p.1 - p.2)) := by
    intro s
    simp only [gradQ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, map_add, map_smul, map_sub]
    module
  have e1 : ∀ s : ℝ, p.1 - (p + s • (p' - p)).1 = (-s) • (p'.1 - p.1) := by
    intro s
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub]
    module
  have e2 : ∀ s : ℝ, p'.1 - (p + s • (p' - p)).1 = (1 - s) • (p'.1 - p.1) := by
    intro s
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub]
    module
  have mem : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → p + s • (p' - p) ∈ G :=
    fun s h0 h1 => hG.add_smul_sub_mem hp hp' ⟨h0, h1⟩
  have h1 := fo _ (mem (1 / 3) (by norm_num) (by norm_num)) p.1 (hGP p hp)
  have h2 := fo _ (mem (1 / 3) (by norm_num) (by norm_num)) p'.1 (hGP p' hp')
  have h3 := fo _ (mem (2 / 3) (by norm_num) (by norm_num)) p.1 (hGP p hp)
  have h4 := fo _ (mem (2 / 3) (by norm_num) (by norm_num)) p'.1 (hGP p' hp')
  rw [aff, e1] at h1 h3
  rw [aff, e2] at h2 h4
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_right]
    at h1 h2 h3 h4 ⊢
  linarith
-- END orth

-- BEGIN quadSection
/-- linear algebra: a quadratic form expressed through a linear section. -/
theorem quad_section (M : E →L[ℝ] E) (hM : ∀ y z, inner ℝ (M y) z = inner ℝ y (M z))
    (D : Submodule ℝ E) :
    ∃ B : E →L[ℝ] E, ∀ dx ∈ D, ∀ dv : E, (∀ z ∈ D, inner ℝ (dv - M dx) z = 0) →
      inner ℝ dx (M dx) = inner ℝ dv (B dv) := by
  -- `P` is the orthogonal projection onto `D`, `K = P ∘ M ∘ P`.
  set P : E →L[ℝ] E := D.starProjection with hPdef
  have hPsym : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v) := fun u v =>
    D.inner_starProjection_left_eq_right u v
  have hPself : ∀ u ∈ D, P u = u := fun u hu => Submodule.starProjection_eq_self_iff.mpr hu
  let K : E →ₗ[ℝ] E := (((P.comp M).comp P : E →L[ℝ] E) : E →ₗ[ℝ] E)
  have hKapp : ∀ u, K u = P (M (P u)) := fun u => rfl
  -- a linear map `S` with `K (S w) = w` for all `w ∈ range K`
  obtain ⟨S0, hS0⟩ := K.rangeRestrict.exists_rightInverse_of_surjective K.range_rangeRestrict
  obtain ⟨S, hS⟩ := LinearMap.exists_extend S0
  have hKS : ∀ w ∈ LinearMap.range K, K (S w) = w := by
    intro w hw
    have h1 : S w = S0 ⟨w, hw⟩ := by
      rw [← hS]; rfl
    have h2 := congrArg Subtype.val (LinearMap.congr_fun hS0 ⟨w, hw⟩)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.codRestrict_apply,
      LinearMap.id_coe, id_eq] at h2
    rw [h1]; exact h2
  refine ⟨LinearMap.toContinuousLinearMap ((P : E →ₗ[ℝ] E) ∘ₗ S ∘ₗ (P : E →ₗ[ℝ] E)), ?_⟩
  intro dx hdx dv hdv
  have hz : P (dv - M dx) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff D).2 ((Submodule.mem_orthogonal' D _).2 hdv)
  have hw : P dv = K dx := by
    rw [map_sub, sub_eq_zero] at hz
    rw [hKapp, hPself dx hdx, hz]
  have hB : (LinearMap.toContinuousLinearMap ((P : E →ₗ[ℝ] E) ∘ₗ S ∘ₗ (P : E →ₗ[ℝ] E))) dv
      = P (S (P dv)) := rfl
  rw [hB, ← hPsym, hw]
  have hKy := hKS (K dx) (LinearMap.mem_range_self K dx)
  have e1 : inner ℝ dx (K dx) = inner ℝ dx (M dx) := by
    rw [hKapp, hPself dx hdx, ← hPsym, hPself dx hdx]
  have e2 : ∀ y, inner ℝ (K dx) y = inner ℝ dx (K y) := by
    intro y
    rw [hKapp, hKapp, hPsym, hM, hPsym]
  rw [e2, hKy, e1]
-- END quadSection

-- BEGIN pieceFormula
/-- on a convex set of subgradient pairs inside one piece, `f*` is quadratic. -/
theorem conj_quadratic_on_piece (f : E → EReal) {P : Set E} (hP : Convex ℝ P)
    (A : E →L[ℝ] E) (a : E) (α : ℝ)
    (hval : ∀ x ∈ P, f x = (((1 / 2 : ℝ) * inner ℝ x (A x) + inner ℝ a x + α) : EReal))
    {G : Set (E × E)} (hG : Convex ℝ G) (hGP : ∀ p ∈ G, p.1 ∈ P)
    (hGsub : ∀ p ∈ G, IsSubgrad f p.1 p.2) :
    ∃ (B : E →L[ℝ] E) (b : E) (β : ℝ), (A = 0 → B = 0) ∧ ∀ p ∈ G,
      conjugate f p.2 = (((1 / 2 : ℝ) * inner ℝ p.2 (B p.2) + inner ℝ b p.2 + β) : EReal) := by
  rcases G.eq_empty_or_nonempty with hGe | ⟨p0, hp0⟩
  · exact ⟨0, 0, 0, fun _ => rfl, fun p hp => by simp [hGe] at hp⟩
  have horth := subgrad_orth f hP A a α hval hG hGP hGsub
  obtain ⟨M, hMdef⟩ : ∃ M : E →L[ℝ] E,
      M = (1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A) := ⟨_, rfl⟩
  have hM : ∀ y z, inner ℝ (M y) z = inner ℝ y (M z) := by
    intro y z
    simp only [hMdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    ring
  have hgrad : ∀ x, gradQ A a x = M x + a := by
    intro x
    simp only [gradQ, hMdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  have hAM : ∀ x, inner ℝ x (A x) = inner ℝ x (M x) := by
    intro x
    simp only [hMdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      real_inner_smul_right, inner_add_right, ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_comm x (A x)]
    ring
  obtain ⟨D, hD⟩ : ∃ D : Submodule ℝ E,
      D = Submodule.span ℝ ((fun p : E × E => p.1 - p0.1) '' G) := ⟨_, rfl⟩
  obtain ⟨B, hB0, hBq⟩ : ∃ B : E →L[ℝ] E, (A = 0 → B = 0) ∧ ∀ dx ∈ D, ∀ dv : E,
      (∀ z ∈ D, inner ℝ (dv - M dx) z = 0) → inner ℝ dx (M dx) = inner ℝ dv (B dv) := by
    by_cases hA : A = 0
    · refine ⟨0, fun _ => rfl, ?_⟩
      intro dx _ dv _
      have hM0 : M = 0 := by rw [hMdef, hA]; simp
      simp [hM0]
    · obtain ⟨B, hB⟩ := quad_section M hM D
      exact ⟨B, fun h => absurd h hA, hB⟩
  have hperp : ∀ p ∈ G, ∀ z ∈ D, inner ℝ ((p.2 - p0.2) - M (p.1 - p0.1)) z = 0 := by
    intro p hp z hz
    rw [hD] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p', hp', rfl⟩ := hz
      show inner ℝ ((p.2 - p0.2) - M (p.1 - p0.1)) (p'.1 - p0.1) = 0
      have o1 := horth p hp p' hp'
      have o2 := horth p hp p0 hp0
      have o3 := horth p0 hp0 p' hp'
      rw [hgrad] at o1 o2 o3
      simp only [map_sub, inner_sub_left, inner_sub_right, inner_add_left] at o1 o2 o3 ⊢
      linarith
    | zero => simp
    | add z w _ _ hz hw => rw [inner_add_right, hz, hw, add_zero]
    | smul c z _ hz => rw [real_inner_smul_right, hz, mul_zero]
  obtain ⟨r0, hr0, -⟩ := hGsub p0 hp0
  have hr0q : r0 = (1 / 2 : ℝ) * inner ℝ p0.1 (A p0.1) + inner ℝ a p0.1 + α := by
    have h := hr0.symm.trans (hval p0.1 (hGP p0 hp0))
    exact_mod_cast h
  refine ⟨B, p0.1 - (1 / 2 : ℝ) • (B p0.2 + ContinuousLinearMap.adjoint B p0.2),
    (1 / 2 : ℝ) * inner ℝ p0.2 (B p0.2) - r0, hB0, ?_⟩
  intro p hp
  obtain ⟨r, hr, hsub⟩ := hGsub p hp
  have hrq : r = (1 / 2 : ℝ) * inner ℝ p.1 (A p.1) + inner ℝ a p.1 + α := by
    have h := hr.symm.trans (hval p.1 (hGP p hp))
    exact_mod_cast h
  rw [hAM] at hrq hr0q
  have hdx : p.1 - p0.1 ∈ D := by
    rw [hD]
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  have F1 := hBq (p.1 - p0.1) hdx (p.2 - p0.2) (hperp p hp)
  have F2 := hperp p hp (p.1 - p0.1) hdx
  have F3 := horth p0 hp0 p hp
  rw [hgrad] at F3
  have key : inner ℝ p.2 p.1 - r = (1 / 2 : ℝ) * inner ℝ p.2 (B p.2) +
      inner ℝ (p0.1 - (1 / 2 : ℝ) • (B p0.2 + ContinuousLinearMap.adjoint B p0.2)) p.2 +
      ((1 / 2 : ℝ) * inner ℝ p0.2 (B p0.2) - r0) := by
    have c1 := hM p.1 p.1
    have c2 := hM p.1 p0.1
    have c3 := hM p0.1 p.1
    have c4 := hM p0.1 p0.1
    have c5 := real_inner_comm p.1 (M p0.1)
    have c6 := real_inner_comm p.2 p0.1
    have c7 := real_inner_comm (B p0.2) p.2
    simp only [map_sub, inner_sub_left, inner_sub_right, inner_add_left,
      real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left] at F1 F2 F3 ⊢
    linarith
  rw [conjugate_eq_of_isSubgrad hr hsub]
  exact_mod_cast congrArg (fun t : ℝ => (t : EReal)) key
-- END pieceFormula

/-! ### Conjugate basics and Fenchel–Moreau -/

-- BEGIN conjBasic
theorem conjugate_convex (f : E → EReal) : ConvexEReal (conjugate f) := by
  intro p hp q hq a b ha hb hab
  simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
  unfold conjugate at hp hq ⊢
  rw [sSup_le_iff] at hp hq ⊢
  rintro _ ⟨x, -, rfl⟩
  have h1 := hp _ ⟨x, Set.mem_univ _, rfl⟩
  have h2 := hq _ ⟨x, Set.mem_univ _, rfl⟩
  simp only at h1 h2 ⊢
  generalize f x = t at h1 h2 ⊢
  induction t using EReal.rec with
  | bot => simp at h1
  | coe t =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h1 h2 ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      inner_add_left, real_inner_smul_left]
    have ht : t = a * t + b * t := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  | top => simp

theorem conjugate_lsc (f : E → EReal) : LowerSemicontinuous (conjugate f) := by
  have : conjugate f = fun v => ⨆ x, (((inner ℝ v x : ℝ) : EReal) - f x) := by
    funext v
    unfold conjugate
    rw [Set.image_univ, sSup_range]
  rw [this]
  apply lowerSemicontinuous_iSup
  intro x
  generalize f x = t
  induction t using EReal.rec with
  | bot => simp only [EReal.coe_sub_bot]; exact lowerSemicontinuous_const
  | coe t =>
    apply Continuous.lowerSemicontinuous
    have : (fun v => ((inner ℝ v x : ℝ) : EReal) - (t : EReal)) =
        fun v => (((inner ℝ v x - t : ℝ)) : EReal) := by
      funext v; rw [EReal.coe_sub]
    rw [this]
    exact continuous_coe_real_ereal.comp (by fun_prop)
  | top => simp only [EReal.sub_top]; exact lowerSemicontinuous_const
-- END conjBasic

-- BEGIN fenchelMoreau
theorem fmo_le_of_forall {z : EReal} {a : ℝ} (hb : ⊥ < z) (h : ∀ s : ℝ, z ≤ (s : EReal) → a ≤ s) :
    (a : EReal) ≤ z := by
  induction z using EReal.rec with
  | bot => exact absurd hb (lt_irrefl _)
  | coe t => exact_mod_cast h t le_rfl
  | top => exact le_top

theorem fmo_conj_le {f : E → EReal} {v : E} {β : ℝ}
    (h : ∀ y, ((inner ℝ v y - β : ℝ) : EReal) ≤ f y) : conjugate f v ≤ (β : EReal) := by
  apply sSup_le
  rintro _ ⟨y, -, rfl⟩
  show ((inner ℝ v y : ℝ) : EReal) - f y ≤ β
  have hy := h y
  generalize f y = z at hy ⊢
  induction z using EReal.rec with
  | bot => exact absurd hy (not_le.mpr (EReal.bot_lt_coe _))
  | coe t =>
    have : inner ℝ v y - β ≤ t := by exact_mod_cast hy
    rw [← EReal.coe_sub]
    exact_mod_cast (by linarith)
  | top => rw [EReal.sub_top]; exact bot_le

theorem fmo_le_biconj {f : E → EReal} {v x : E} {β : ℝ} (h : conjugate f v ≤ (β : EReal)) :
    ((inner ℝ x v - β : ℝ) : EReal) ≤ conjugate (conjugate f) x := by
  have key : ((inner ℝ x v - β : ℝ) : EReal) ≤ ((inner ℝ x v : ℝ) : EReal) - conjugate f v := by
    generalize conjugate f v = z at h ⊢
    induction z using EReal.rec with
    | bot => rw [EReal.coe_sub_bot]; exact le_top
    | coe t =>
      have : t ≤ β := by exact_mod_cast h
      rw [← EReal.coe_sub]
      exact_mod_cast (by linarith)
    | top => exact absurd h (by simp)
  calc _ ≤ _ := key
    _ ≤ conjugate (conjugate f) x := le_sSup ⟨v, trivial, rfl⟩

theorem fmo_biconj_le (f : E → EReal) (x : E) : conjugate (conjugate f) x ≤ f x := by
  apply sSup_le
  rintro _ ⟨v, -, rfl⟩
  show ((inner ℝ x v : ℝ) : EReal) - conjugate f v ≤ f x
  have hv : ((inner ℝ v x : ℝ) : EReal) - f x ≤ conjugate f v := le_sSup ⟨x, trivial, rfl⟩
  generalize conjugate f v = z at hv ⊢
  generalize f x = w at hv ⊢
  induction w using EReal.rec with
  | bot =>
    rw [EReal.coe_sub_bot] at hv
    rw [top_le_iff.mp hv, EReal.sub_top]
  | coe t =>
    induction z using EReal.rec with
    | bot => exact absurd hv (by rw [← EReal.coe_sub]; exact not_le.mpr (EReal.bot_lt_coe _))
    | coe s =>
      have : inner ℝ v x - t ≤ s := by rw [← EReal.coe_sub] at hv; exact_mod_cast hv
      rw [← EReal.coe_sub]
      have h2 : inner ℝ x v - s ≤ t := by rw [real_inner_comm]; linarith
      exact_mod_cast h2
    | top => rw [EReal.sub_top]; exact bot_le
  | top => exact le_top

theorem fmo_epi_closed {f : E → EReal} (hf : LowerSemicontinuous f) : IsClosed (epigraph f) := by
  have h := hf.isClosed_epigraph
  have hc : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  exact h.preimage hc

theorem fmo_sep {f : E → EReal} (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) {x0 : E} {r : ℝ} (hr : (r : EReal) < f x0) :
    ∃ (w : E) (c u : ℝ), 0 ≤ c ∧ c * r + inner ℝ w x0 < u ∧
      ∀ y (s : ℝ), f y ≤ s → u < inner ℝ w y + c * s := by
  have hS : IsClosed (epigraph f) := fmo_epi_closed hf_lsc
  have hnot : (x0, r) ∉ epigraph f := by
    simp only [epigraph, Set.mem_setOf_eq, not_le]; exact hr
  obtain ⟨Φ, u, hΦx, hΦS⟩ := geometric_hahn_banach_point_closed hf_convex hS hnot
  set c := Φ ((0 : E), (1 : ℝ)) with hc_def
  set w := (InnerProductSpace.toDual ℝ E).symm (Φ.comp (ContinuousLinearMap.inl ℝ E ℝ)) with hw
  have hΦ : ∀ x (s : ℝ), Φ (x, s) = inner ℝ w x + c * s := by
    intro x s
    have : (x, s) = (x, (0:ℝ)) + s • ((0:E), (1:ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, hw, InnerProductSpace.toDual_symm_apply]
    simp [smul_eq_mul, mul_comm, hc_def]
  have hmem : ∀ y (s : ℝ), f y ≤ s → u < inner ℝ w y + c * s := by
    intro y s hys
    have := hΦS (y, s) (by simpa [epigraph] using hys)
    rwa [hΦ] at this
  refine ⟨w, c, u, ?_, ?_, hmem⟩
  · by_contra hcneg
    push_neg at hcneg
    obtain ⟨y, hy⟩ := hf_proper.2
    have hy1 : f y ≠ ⊤ := ne_of_lt hy
    have hy2 : f y ≠ ⊥ := ne_of_gt (hf_proper.1 y)
    set t := (f y).toReal with ht
    have hft : f y = (t : EReal) := (EReal.coe_toReal hy1 hy2).symm
    set s := max t ((u - inner ℝ w y) / c) with hs
    have h1 := hmem y s (by rw [hft]; exact_mod_cast le_max_left _ _)
    have h2 : (u - inner ℝ w y) / c ≤ s := le_max_right _ _
    have h3 := mul_le_mul_of_nonpos_right h2 (le_of_lt hcneg)
    rw [div_mul_cancel₀ _ (ne_of_lt hcneg)] at h3
    linarith
  · have := hΦ x0 r
    linarith

theorem fmo_pos_case {f : E → EReal} (hb : ∀ y, ⊥ < f y) {w x0 : E} {c u r : ℝ} (hc : 0 < c)
    (h1 : c * r + inner ℝ w x0 < u) (h2 : ∀ y (s : ℝ), f y ≤ s → u < inner ℝ w y + c * s) :
    ∃ (v : E) (β : ℝ), (∀ y, ((inner ℝ v y - β : ℝ) : EReal) ≤ f y) ∧ r < inner ℝ x0 v - β := by
  refine ⟨-(1/c) • w, -(u/c), ?_, ?_⟩
  · intro y
    apply fmo_le_of_forall (hb y)
    intro s hs
    have := h2 y s hs
    rw [real_inner_smul_left]
    have e : -(1/c) * inner ℝ w y - -(u/c) = (u - inner ℝ w y) / c := by field_simp; ring
    rw [e, div_le_iff₀ hc]; linarith
  · rw [real_inner_smul_right, real_inner_comm]
    have e : -(1/c) * inner ℝ w x0 - -(u/c) = (u - inner ℝ w x0) / c := by field_simp; ring
    rw [e, lt_div_iff₀ hc]; linarith

theorem fmo_minorant {f : E → EReal} (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) :
    ∃ (v : E) (β : ℝ), ∀ y, ((inner ℝ v y - β : ℝ) : EReal) ≤ f y := by
  obtain ⟨x1, hx1⟩ := hf_proper.2
  have hy1 : f x1 ≠ ⊤ := ne_of_lt hx1
  have hy2 : f x1 ≠ ⊥ := ne_of_gt (hf_proper.1 x1)
  set t := (f x1).toReal with ht
  have hft : f x1 = (t : EReal) := (EReal.coe_toReal hy1 hy2).symm
  have hr : ((t - 1 : ℝ) : EReal) < f x1 := by rw [hft]; exact_mod_cast (by linarith)
  obtain ⟨w, c, u, hc0, h1, h2⟩ := fmo_sep hf_proper hf_lsc hf_convex hr
  have h3 := h2 x1 t hft.le
  have hc : 0 < c := by nlinarith
  obtain ⟨v, β, hv, -⟩ := fmo_pos_case hf_proper.1 hc h1 h2
  exact ⟨v, β, hv⟩

theorem fmo_exists {f : E → EReal} (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) {x0 : E} {r : ℝ} (hr : (r : EReal) < f x0) :
    ∃ (v : E) (β : ℝ), (∀ y, ((inner ℝ v y - β : ℝ) : EReal) ≤ f y) ∧ r < inner ℝ x0 v - β := by
  obtain ⟨w, c, u, hc0, h1, h2⟩ := fmo_sep hf_proper hf_lsc hf_convex hr
  rcases hc0.lt_or_eq with hc | hc
  · exact fmo_pos_case hf_proper.1 hc h1 h2
  · subst hc
    obtain ⟨v1, β1, hv1⟩ := fmo_minorant hf_proper hf_lsc hf_convex
    have hδ : 0 < u - inner ℝ w x0 := by linarith [h1]
    obtain ⟨l, hl, hlδ⟩ : ∃ l : ℝ, 0 ≤ l ∧
        l * (u - inner ℝ w x0) = |r - (inner ℝ x0 v1 - β1)| + 1 :=
      ⟨(|r - (inner ℝ x0 v1 - β1)| + 1) / (u - inner ℝ w x0), by positivity,
        div_mul_cancel₀ _ hδ.ne'⟩
    rw [mul_sub] at hlδ
    refine ⟨v1 - l • w, β1 - l * u, ?_, ?_⟩
    · intro y
      apply fmo_le_of_forall (hf_proper.1 y)
      intro s hs
      have e1 : u ≤ inner ℝ w y := by linarith [h2 y s hs]
      have e2 : inner ℝ v1 y - β1 ≤ s := by
        have := le_trans (hv1 y) hs; exact_mod_cast this
      have e3 := mul_le_mul_of_nonneg_left e1 hl
      rw [inner_sub_left, real_inner_smul_left]
      linarith
    · rw [inner_sub_right, real_inner_smul_right, real_inner_comm w x0]
      have := le_abs_self (r - (inner ℝ x0 v1 - β1))
      linarith

theorem biconjugate_eq (f : E → EReal) (hf_proper : IsProper f)
    (hf_lsc : LowerSemicontinuous f) (hf_convex : ConvexEReal f) :
    conjugate (conjugate f) = f := by
  funext x
  apply le_antisymm (fmo_biconj_le f x)
  by_contra h
  push_neg at h
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp h
  obtain ⟨v, β, hvβ, hr⟩ := fmo_exists hf_proper hf_lsc hf_convex hr2
  have h3 := fmo_le_biconj (x := x) (fmo_conj_le hvβ)
  have h4 : (r : EReal) < ((inner ℝ x v - β : ℝ) : EReal) := by exact_mod_cast hr
  exact absurd (lt_trans hr1 (lt_of_lt_of_le h4 h3)) (lt_irrefl _)

theorem conjugate_proper (f : E → EReal) (hf_proper : IsProper f)
    (hf_lsc : LowerSemicontinuous f) (hf_convex : ConvexEReal f) :
    IsProper (conjugate f) := by
  obtain ⟨x0, hx0⟩ := hf_proper.2
  have hy1 : f x0 ≠ ⊤ := ne_of_lt hx0
  have hy2 : f x0 ≠ ⊥ := ne_of_gt (hf_proper.1 x0)
  set t := (f x0).toReal with ht
  have hft : f x0 = (t : EReal) := (EReal.coe_toReal hy1 hy2).symm
  refine ⟨fun v => ?_, ?_⟩
  · have : ((inner ℝ v x0 : ℝ) : EReal) - f x0 ≤ conjugate f v := le_sSup ⟨x0, trivial, rfl⟩
    refine lt_of_lt_of_le ?_ this
    rw [hft, ← EReal.coe_sub]
    exact EReal.bot_lt_coe _
  · by_contra hne
    have hall : ∀ v, conjugate f v = ⊤ := by
      intro v
      by_contra hv
      exact hne ⟨v, lt_top_iff_ne_top.mpr hv⟩
    have hle : conjugate (conjugate f) x0 ≤ ⊥ := by
      apply sSup_le
      rintro _ ⟨v, -, rfl⟩
      show ((inner ℝ x0 v : ℝ) : EReal) - conjugate f v ≤ ⊥
      rw [hall v, EReal.sub_top]
    rw [biconjugate_eq f hf_proper hf_lsc hf_convex] at hle
    exact absurd (hf_proper.1 x0) (not_lt.mpr hle)
-- END fenchelMoreau

/-! ### Main forward implications -/

-- BEGIN forward
theorem fw_main (f : E → EReal) (hf_proper : IsProper f)
    (hf_lsc : LowerSemicontinuous f) (hf_convex : ConvexEReal f)
    {n : ℕ} (P : Fin n → Set E) (A : Fin n → E →L[ℝ] E) (a : Fin n → E) (α : Fin n → ℝ)
    (hdom : effDom f = ⋃ i, P i) (hpoly : ∀ i, IsPolyhedral (P i))
    (hval : ∀ i : Fin n, ∀ x ∈ P i,
      f x = (((1 / 2 : ℝ) * inner ℝ x (A i x) + inner ℝ (a i) x + α i) : EReal)) :
    ∃ (N : ℕ) (Q : Fin N → Set E) (B : Fin N → E →L[ℝ] E) (b : Fin N → E) (β : Fin N → ℝ),
      effDom (conjugate f) = ⋃ k, Q k ∧
      (∀ k, IsPolyhedral (Q k)) ∧
      (∀ k, Q k ⊆ effDom (conjugate f)) ∧
      (∀ k, ∀ v ∈ Q k, conjugate f v =
        (((1 / 2 : ℝ) * inner ℝ v (B k v) + inner ℝ (b k) v + β k) : EReal)) ∧
      ((∀ i, A i = 0) → ∀ k, B k = 0) := by
  obtain ⟨N, G, j, hGpoly, hGP, hgraph⟩ :=
    subgrad_graph_decomp f hf_proper hf_lsc hf_convex P A a α hdom hpoly hval
  have hsubG : ∀ k, ∀ p ∈ G k, IsSubgrad f p.1 p.2 := by
    intro k p hp
    have hp' : p ∈ ⋃ k, G k := Set.mem_iUnion.2 ⟨k, hp⟩
    rw [← hgraph] at hp'
    exact hp'
  have hPconv : ∀ i, Convex ℝ (P i) := fun i =>
    ((isPolyD_iff_isPolyhedral (P i)).2 (hpoly i)).convex
  have key : ∀ k, ∃ (B : E →L[ℝ] E) (b : E) (β : ℝ), (A (j k) = 0 → B = 0) ∧ ∀ p ∈ G k,
      conjugate f p.2 = (((1 / 2 : ℝ) * inner ℝ p.2 (B p.2) + inner ℝ b p.2 + β) : EReal) :=
    fun k => conj_quadratic_on_piece f (hPconv (j k)) (A (j k)) (a (j k)) (α (j k))
      (hval (j k)) (hGpoly k).convex (hGP k) (hsubG k)
  choose B b β hB hform using key
  have hQpoly : ∀ k, IsPolyD (Prod.snd '' G k) := fun k => (hGpoly k).image_snd
  have hS : {w : E | ∃ x, IsSubgrad f x w} = ⋃ k, Prod.snd '' G k := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨x, hx⟩
      have hx' : (x, w) ∈ {p : E × E | IsSubgrad f p.1 p.2} := hx
      rw [hgraph, Set.mem_iUnion] at hx'
      obtain ⟨k, hk⟩ := hx'
      exact ⟨k, (x, w), hk, rfl⟩
    · rintro ⟨k, p, hp, rfl⟩
      exact ⟨p.1, hsubG k p hp⟩
  have hclosed : IsClosed (⋃ k, Prod.snd '' G k) :=
    isClosed_iUnion_of_finite (fun k => (hQpoly k).isClosed)
  have hQsub : ∀ k, Prod.snd '' G k ⊆ effDom (conjugate f) := by
    rintro k v ⟨p, hp, rfl⟩
    obtain ⟨r, hr, hry⟩ := hsubG k p hp
    show conjugate f p.2 < ⊤
    rw [conjugate_eq_of_isSubgrad hr hry]
    exact EReal.coe_lt_top _
  refine ⟨N, fun k => Prod.snd '' G k, B, b, β, ?_, ?_, hQsub, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro v hv
      have hv' := mem_closure_range_subgrad f hf_proper hf_lsc hf_convex hv
      rw [hS, hclosed.closure_eq] at hv'
      exact hv'
    · intro v hv
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hv
      exact hQsub k hk
  · intro k
    exact (isPolyD_iff_isPolyhedral _).1 (hQpoly k)
  · rintro k v ⟨p, hp, rfl⟩
    exact hform k p hp
  · intro hA k
    exact hB k (hA (j k))

theorem conj_PLQ_of_PLQ (f : E → EReal) (hf_proper : IsProper f)
    (hf_lsc : LowerSemicontinuous f) (hf_convex : ConvexEReal f)
    (h : IsPiecewiseLinearQuadratic f) : IsPiecewiseLinearQuadratic (conjugate f) := by
  obtain ⟨n, P, A, a, α, hdom, hpoly, -, hval⟩ := h
  obtain ⟨N, Q, B, b, β, h1, h2, h3, h4, -⟩ :=
    fw_main f hf_proper hf_lsc hf_convex P A a α hdom hpoly hval
  exact ⟨N, Q, B, b, β, h1, h2, h3, h4⟩

theorem conj_PL_of_PL (f : E → EReal) (hf_proper : IsProper f)
    (hf_lsc : LowerSemicontinuous f) (hf_convex : ConvexEReal f)
    (h : IsPiecewiseLinear f) : IsPiecewiseLinear (conjugate f) := by
  obtain ⟨g, ⟨n, P, A, a, hdom, hpoly, hlin⟩, hfg⟩ := h
  have hval : ∀ i : Fin n, ∀ x ∈ P i,
      f x = (((1 / 2 : ℝ) * inner ℝ x ((fun _ => (0 : E →L[ℝ] E)) i x) +
        inner ℝ ((fun i => (InnerProductSpace.toDual ℝ E).symm (A i)) i) x + a i) : EReal) := by
    intro i x hx
    have hxd : x ∈ effDom f := by
      rw [hdom]
      exact Set.mem_iUnion.2 ⟨i, hx⟩
    rw [hfg x hxd, hlin i x hx]
    simp [InnerProductSpace.toDual_symm_apply]
  obtain ⟨N, Q, B, b, β, h1, h2, -, h4, h5⟩ :=
    fw_main f hf_proper hf_lsc hf_convex P (fun _ => (0 : E →L[ℝ] E))
      (fun i => (InnerProductSpace.toDual ℝ E).symm (A i)) a hdom hpoly hval
  have hB : ∀ k, B k = 0 := h5 (fun _ => rfl)
  have hform : ∀ k, ∀ v ∈ Q k, conjugate f v = ((inner ℝ (b k) v + β k : ℝ) : EReal) := by
    intro k v hv
    rw [h4 k v hv, hB k]
    simp
  refine ⟨fun v => (conjugate f v).toReal,
    ⟨N, Q, fun k => innerSL ℝ (b k), β, h1, h2, ?_⟩, ?_⟩
  · intro k v hv
    show (conjugate f v).toReal = innerSL ℝ (b k) v + β k
    rw [hform k v hv, EReal.toReal_coe, innerSL_apply_apply]
  · intro v hv
    have hv' := hv
    rw [h1] at hv'
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hv'
    show conjugate f v = ((conjugate f v).toReal : EReal)
    rw [hform k v hk, EReal.toReal_coe]
-- END forward

end RW1114

theorem RW_chap_11_14
  (f : E → EReal)
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f)
  (hf_convex : ConvexEReal f) :
  (IsPiecewiseLinear f ↔ IsPiecewiseLinear (conjugate f)) ∧
  (IsPiecewiseLinearQuadratic f ↔
    IsPiecewiseLinearQuadratic (conjugate f)) := by
  have hc := RW1114.conjugate_proper f hf_proper hf_lsc hf_convex
  have hcl := RW1114.conjugate_lsc f
  have hcc := RW1114.conjugate_convex f
  have hbi := RW1114.biconjugate_eq f hf_proper hf_lsc hf_convex
  refine ⟨⟨RW1114.conj_PL_of_PL f hf_proper hf_lsc hf_convex, fun h => ?_⟩,
    ⟨RW1114.conj_PLQ_of_PLQ f hf_proper hf_lsc hf_convex, fun h => ?_⟩⟩
  · have := RW1114.conj_PL_of_PL _ hc hcl hcc h
    rwa [hbi] at this
  · have := RW1114.conj_PLQ_of_PLQ _ hc hcl hcc h
    rwa [hbi] at this

end RW_chap_11_14
