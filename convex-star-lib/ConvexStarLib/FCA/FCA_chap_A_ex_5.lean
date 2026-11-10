import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_5`, so the main result is `FCA_chap_A_ex_5.FCA_chap_A_ex_5`.
-/

namespace FCA_chap_A_ex_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Auxiliary lemmas on positive operators -/

omit [FiniteDimensional ℝ E] in
lemma FCA_A5_inner_nonneg {A : E →L[ℝ] E} (hA : A.IsPositive) (x : E) :
    0 ≤ inner ℝ (A x) x := by
  simpa using hA.re_inner_nonneg_left x

omit [FiniteDimensional ℝ E] in
lemma FCA_A5_symm {A : E →L[ℝ] E} (hA : A.IsPositive) (x y : E) :
    inner ℝ (A x) y = inner ℝ x (A y) :=
  hA.inner_left_eq_inner_right x y

omit [FiniteDimensional ℝ E] in
lemma FCA_A5_isPositive_of {T : E →L[ℝ] E} (hs : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hp : ∀ x, 0 ≤ inner ℝ (T x) x) : T.IsPositive :=
  ⟨hs, fun x => by simpa [ContinuousLinearMap.reApplyInnerSelf] using hp x⟩

lemma FCA_A5_apply_eq_zero {A : E →L[ℝ] E} (hA : A.IsPositive) {x : E}
    (hx : inner ℝ (A x) x = 0) : A x = 0 := by
  obtain ⟨m, u, rfl⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hA
  simp only [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply, sum_inner,
    real_inner_smul_left] at hx ⊢
  have h0 : ∀ i, inner ℝ (u i) x = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg _)).mp hx i
      (Finset.mem_univ _)
    exact mul_self_eq_zero.mp this
  simp [h0]

lemma FCA_A5_comb_ker {A B : E →L[ℝ] E} (hA : A.IsPositive) (hB : B.IsPositive) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {x : E} (hx : (a • A + b • B) x = 0) : A x = 0 ∧ B x = 0 := by
  have h1 : inner ℝ ((a • A + b • B) x) x = 0 := by rw [hx, inner_zero_left]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left,
    real_inner_smul_left] at h1
  have hA0 := FCA_A5_inner_nonneg hA x
  have hB0 := FCA_A5_inner_nonneg hB x
  have h2 : inner ℝ (A x) x = 0 := by nlinarith [mul_nonneg ha.le hA0, mul_nonneg hb.le hB0]
  have h3 : inner ℝ (B x) x = 0 := by nlinarith [mul_nonneg ha.le hA0, mul_nonneg hb.le hB0]
  exact ⟨FCA_A5_apply_eq_zero hA h2, FCA_A5_apply_eq_zero hB h3⟩

/-- Coercivity of a positive operator on the orthogonal complement of its kernel. -/
lemma FCA_A5_coercive {M : E →L[ℝ] E} (hM : M.IsPositive) :
    ∃ m : ℝ, 0 < m ∧ ∀ u ∈ (LinearMap.ker M.toLinearMap)ᗮ, m * ‖u‖ ^ 2 ≤ inner ℝ (M u) u := by
  set K := LinearMap.ker M.toLinearMap with hK
  set S : Set E := (Kᗮ : Set E) ∩ Metric.sphere 0 1 with hS
  have hScomp : IsCompact S :=
    (isCompact_sphere (0 : E) 1).inter_left (Submodule.isClosed_orthogonal K)
  have hnorm : ∀ u ∈ Kᗮ, u ≠ 0 → ‖u‖⁻¹ • u ∈ S := by
    intro u hu hu0
    refine ⟨Kᗮ.smul_mem _ hu, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)]
  by_cases hSne : S.Nonempty
  · obtain ⟨u₀, hu₀S, hmin⟩ := hScomp.exists_isMinOn hSne
      (f := fun u => inner ℝ (M u) u) (by fun_prop)
    refine ⟨inner ℝ (M u₀) u₀, ?_, ?_⟩
    · rcases (FCA_A5_inner_nonneg hM u₀).lt_or_eq with h | h
      · exact h
      · exfalso
        have hMu : M u₀ = 0 := FCA_A5_apply_eq_zero hM h.symm
        have hu₀K : u₀ ∈ K := by simpa [hK] using hMu
        have : inner ℝ u₀ u₀ = 0 := Submodule.inner_right_of_mem_orthogonal hu₀K hu₀S.1
        have hu0 : u₀ = 0 := inner_self_eq_zero.mp this
        have := hu₀S.2
        rw [mem_sphere_zero_iff_norm, hu0, norm_zero] at this
        exact zero_ne_one this
    · intro u hu
      by_cases hu0 : u = 0
      · simp [hu0]
      · have h1 : inner ℝ (M u₀) u₀ ≤ inner ℝ (M (‖u‖⁻¹ • u)) (‖u‖⁻¹ • u) :=
          hmin (hnorm u hu hu0)
        simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
        have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have : ‖u‖⁻¹ * (‖u‖⁻¹ * inner ℝ (M u) u) = inner ℝ (M u) u / ‖u‖ ^ 2 := by
          field_simp
        rw [this, le_div_iff₀ (by positivity)] at h1
        exact h1
  · refine ⟨1, one_pos, ?_⟩
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · exact absurd ⟨_, hnorm u hu hu0⟩ hSne

/-- If `ker M ≤ ker B` for positive `M, B`, then `B` is dominated by a multiple of `M`. -/
lemma FCA_A5_dom {M B : E →L[ℝ] E} (hM : M.IsPositive) (hB : B.IsPositive)
    (hker : LinearMap.ker M.toLinearMap ≤ LinearMap.ker B.toLinearMap) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x, ε * inner ℝ (B x) x ≤ inner ℝ (M x) x := by
  obtain ⟨m, hm, hcoer⟩ := FCA_A5_coercive hM
  set K := LinearMap.ker M.toLinearMap with hK
  have key : ∀ x, m / (‖B‖ + 1) * inner ℝ (B x) x ≤ inner ℝ (M x) x := by
    intro x
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) x
    have hMy : M y = 0 := hy
    have hBy : B y = 0 := hker hy
    have e1 : inner ℝ (M (y + z)) (y + z) = inner ℝ (M z) z := by
      rw [map_add, hMy, zero_add, inner_add_right, FCA_A5_symm hM z y, hMy, inner_zero_right,
        zero_add]
    have e2 : inner ℝ (B (y + z)) (y + z) = inner ℝ (B z) z := by
      rw [map_add, hBy, zero_add, inner_add_right, FCA_A5_symm hB z y, hBy, inner_zero_right,
        zero_add]
    rw [e1, e2]
    have h1 : inner ℝ (B z) z ≤ ‖B‖ * ‖z‖ ^ 2 := by
      calc inner ℝ (B z) z ≤ ‖B z‖ * ‖z‖ := real_inner_le_norm _ _
        _ ≤ ‖B‖ * ‖z‖ * ‖z‖ := by gcongr; exact B.le_opNorm z
        _ = ‖B‖ * ‖z‖ ^ 2 := by ring
    have h2 := hcoer z hz
    have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
    calc m / (‖B‖ + 1) * inner ℝ (B z) z ≤ m / (‖B‖ + 1) * (‖B‖ * ‖z‖ ^ 2) := by
          gcongr
      _ ≤ m * ‖z‖ ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg ‖z‖, mul_nonneg hm.le (sq_nonneg ‖z‖)]
      _ ≤ inner ℝ (M z) z := h2
  refine ⟨min (m / (‖B‖ + 1)) (1 / 2), by positivity,
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun x => ?_⟩
  calc min (m / (‖B‖ + 1)) (1 / 2) * inner ℝ (B x) x ≤ m / (‖B‖ + 1) * inner ℝ (B x) x :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (FCA_A5_inner_nonneg hB x)
    _ ≤ inner ℝ (M x) x := key x

/-! ### Faces of the elliptope -/

lemma FCA_A5_corrSet_comb {A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hA : A ∈ corrSet n) (hB : B ∈ corrSet n) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • A + b • B ∈ corrSet n := by
  refine ⟨FCA_A5_isPositive_of (fun x y => ?_) (fun x => ?_), fun i => ?_⟩
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left,
      inner_add_right, real_inner_smul_left, real_inner_smul_right, FCA_A5_symm hA.1,
      FCA_A5_symm hB.1]
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left,
      real_inner_smul_left]
    have := FCA_A5_inner_nonneg hA.1 x
    have := FCA_A5_inner_nonneg hB.1 x
    positivity
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_left,
      real_inner_smul_left, hA.2 i, hB.2 i]
    linarith

lemma FCA_A5_part1 (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hV : (corrFV n V).Nonempty) : IsFaceOf (corrFV n V) (corrSet n) := by
  refine ⟨?_, hV, ⟨fun A hA => hA.1, ?_⟩⟩
  · intro A hA B hB a b ha hb hab
    refine ⟨FCA_A5_corrSet_comb hA.1 hB.1 ha hb hab, fun v hv => ?_⟩
    have h1 : A v = 0 := hA.2 hv
    have h2 : B v = 0 := hB.2 hv
    show (a • A + b • B) v = 0
    simp [h1, h2]
  · intro x hx y hy z hz hseg
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
    refine ⟨hx, fun v hv => ?_⟩
    exact (FCA_A5_comb_ker hx.1 hy.1 ha hb (hz.2 hv)).1

lemma FCA_A5_face_sub
    {G : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))}
    (hG : IsFaceOf G (corrSet n))
    {M₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)} (hM₀ : M₀ ∈ G) :
    corrFV n (LinearMap.ker M₀.toLinearMap) ⊆ G := by
  intro B hB
  have hM₀c : M₀ ∈ corrSet n := hG.2.2.subset hM₀
  obtain ⟨ε, hε0, hε1, hdom⟩ := FCA_A5_dom hM₀c.1 hB.1.1 hB.2
  have hε1' : (1 : ℝ) - ε ≠ 0 := by linarith
  set N := (1 - ε)⁻¹ • (M₀ - ε • B) with hN
  have hNc : N ∈ corrSet n := by
    refine ⟨FCA_A5_isPositive_of (fun x y => ?_) (fun x => ?_), fun i => ?_⟩
    · simp only [N, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        FCA_A5_symm hM₀c.1, FCA_A5_symm hB.1.1]
    · simp only [N, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_left, real_inner_smul_left]
      have h1 := hdom x
      have h2 : 0 < (1 - ε)⁻¹ := inv_pos.mpr (by linarith)
      exact mul_nonneg h2.le (by linarith)
    · simp only [N, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        inner_sub_left, real_inner_smul_left, hM₀c.2 i, hB.1.2 i]
      field_simp
  have hseg : M₀ ∈ openSegment ℝ B N := by
    refine ⟨ε, 1 - ε, hε0, by linarith, by ring, ?_⟩
    rw [hN, smul_smul, mul_inv_cancel₀ hε1', one_smul]
    abel
  exact hG.2.2.left_mem_of_mem_openSegment hB.1 hNc hM₀ hseg

lemma FCA_A5_min_ker
    {G : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))}
    (hG : IsFaceOf G (corrSet n)) :
    ∃ A₀ ∈ G, ∀ A ∈ G, LinearMap.ker A₀.toLinearMap ≤ LinearMap.ker A.toLinearMap := by
  classical
  have hex : ∃ k, ∃ A ∈ G, Module.finrank ℝ (LinearMap.ker A.toLinearMap) = k := by
    obtain ⟨A, hA⟩ := hG.2.1
    exact ⟨_, A, hA, rfl⟩
  obtain ⟨A₀, hA₀, hk⟩ := Nat.find_spec hex
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  set Mid := (1 / 2 : ℝ) • A₀ + (1 / 2 : ℝ) • A with hMid_def
  have hMid : Mid ∈ G := hG.1 hA₀ hA (by norm_num) (by norm_num) (by norm_num)
  have hA₀c := hG.2.2.subset hA₀
  have hAc := hG.2.2.subset hA
  have hker : LinearMap.ker Mid.toLinearMap ≤
      LinearMap.ker A₀.toLinearMap ⊓ LinearMap.ker A.toLinearMap := by
    intro x hx
    have := FCA_A5_comb_ker hA₀c.1 hAc.1 (by norm_num : (0:ℝ) < 1 / 2)
      (by norm_num : (0:ℝ) < 1 / 2) hx
    exact ⟨this.1, this.2⟩
  have hle : Module.finrank ℝ (LinearMap.ker A₀.toLinearMap) ≤
      Module.finrank ℝ (LinearMap.ker Mid.toLinearMap) := by
    rw [hk]; exact Nat.find_min' hex ⟨Mid, hMid, rfl⟩
  have heq : LinearMap.ker Mid.toLinearMap = LinearMap.ker A₀.toLinearMap :=
    Submodule.eq_of_le_of_finrank_le (hker.trans inf_le_left) hle
  rw [← heq]
  exact hker.trans inf_le_right

lemma FCA_A5_face_eq
    {G : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))}
    (hG : IsFaceOf G (corrSet n)) :
    G = corrFV n (⨅ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (_ : A ∈ G), LinearMap.ker A.toLinearMap) := by
  apply Set.Subset.antisymm
  · intro A hA
    exact ⟨hG.2.2.subset hA, iInf₂_le A hA⟩
  · obtain ⟨A₀, hA₀, hmin⟩ := FCA_A5_min_ker hG
    intro B hB
    apply FCA_A5_face_sub hG hA₀
    exact ⟨hB.1, (le_iInf₂ (fun A hA => hmin A hA)).trans hB.2⟩

lemma FCA_A5_exposed_of (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hne : (corrFV n W).Nonempty) : IsExposedFaceOf (corrSet n) (corrFV n W) := by
  let b := Module.finBasis ℝ W
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ,
      ∀ A, ψ A = -∑ i, inner ℝ (A (b i)) ((b i : W) : EuclideanSpace ℝ (Fin n)) := by
    refine ⟨-∑ i, (innerSL ℝ ((b i : W) : EuclideanSpace ℝ (Fin n))).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n))
        ((b i : W) : EuclideanSpace ℝ (Fin n))), fun A => ?_⟩
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply]
    simp only [real_inner_comm]
  have hψle : ∀ A ∈ corrSet n, ψ A ≤ 0 := by
    intro A hA
    rw [hψ, neg_nonpos]
    exact Finset.sum_nonneg (fun i _ => FCA_A5_inner_nonneg hA.1 _)
  have hψ0 : ∀ A ∈ corrSet n, (ψ A = 0 ↔ W ≤ LinearMap.ker A.toLinearMap) := by
    intro A hA
    constructor
    · intro h
      rw [hψ, neg_eq_zero,
        Finset.sum_eq_zero_iff_of_nonneg (fun i _ => FCA_A5_inner_nonneg hA.1 _)] at h
      have hb : ∀ i, A (b i) = 0 := fun i => FCA_A5_apply_eq_zero hA.1 (h i (Finset.mem_univ _))
      have hext : A.toLinearMap ∘ₗ W.subtype = 0 := b.ext (fun i => by simp [hb i])
      intro w hw
      have := LinearMap.congr_fun hext ⟨w, hw⟩
      simpa using this
    · intro h
      rw [hψ]
      have : ∀ i, A (b i) = 0 := fun i => h (b i).2
      simp [this]
  refine ⟨ψ, ?_⟩
  ext A
  constructor
  · intro hA
    refine ⟨hA.1, fun B hB => ?_⟩
    rw [(hψ0 A hA.1).mpr hA.2]
    exact hψle B hB
  · rintro ⟨hAc, hmax⟩
    obtain ⟨C, hC⟩ := hne
    have hC0 : ψ C = 0 := (hψ0 C hC.1).mpr hC.2
    have hA0 : ψ A = 0 := le_antisymm (hψle A hAc) (hC0 ▸ hmax C hC.1)
    exact ⟨hAc, (hψ0 A hAc).mp hA0⟩

lemma FCA_A5_exposed
    {G : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))}
    (hG : IsFaceOf G (corrSet n)) : IsExposedFaceOf (corrSet n) G := by
  have hGeq := FCA_A5_face_eq hG
  have hne := hG.2.1
  rw [hGeq] at hne ⊢
  exact FCA_A5_exposed_of _ hne

theorem FCA_chap_A_ex_5 {n : ℕ} :
  (∀ (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
    Set.Nonempty (corrFV n V) →
    IsFaceOf (corrFV n V) (corrSet n)) ∧
  (∀ (F : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
    IsFaceOf F (corrSet n) →
    F = corrFV n (⨅ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (_ : A ∈ F), LinearMap.ker A.toLinearMap)) ∧
  (∀ (M₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
    M₀ ∈ corrSet n →
    IsFaceOf (corrFV n (LinearMap.ker M₀.toLinearMap)) (corrSet n) ∧
    M₀ ∈ corrFV n (LinearMap.ker M₀.toLinearMap) ∧
    (∀ F, IsFaceOf F (corrSet n) → M₀ ∈ F → corrFV n (LinearMap.ker M₀.toLinearMap) ⊆ F)) ∧
  (∀ (F : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
    IsFaceOf F (corrSet n) →
    IsExposedFaceOf (corrSet n) F) := by
  refine ⟨fun V hV => FCA_A5_part1 V hV, fun F hF => FCA_A5_face_eq hF,
    fun M₀ hM₀ => ⟨FCA_A5_part1 _ ⟨M₀, hM₀, le_rfl⟩, ⟨hM₀, le_rfl⟩,
      fun F hF hM₀F => FCA_A5_face_sub hF hM₀F⟩, fun F hF => FCA_A5_exposed hF⟩

end FCA_chap_A_ex_5
