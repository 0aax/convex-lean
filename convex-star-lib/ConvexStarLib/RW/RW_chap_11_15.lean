import ConvexStarLib.Defs

/-!
# `RW_chap_11_15`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_11_15` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_11_15`, so the main result is `RW_chap_11_15.RW_chap_11_15`.
-/

namespace RW_chap_11_15

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace RW1115

def QL {F : Type*} [AddCommGroup F] [Module ℝ F] (θ : F → ℝ) : Prop :=
  ∀ x h : F, ∃ c0 c1 c2 : ℝ, ∀ t : ℝ, θ (x + t • h) = c0 + c1 * t + c2 * t ^ 2

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

lemma QL.comb {θ ψ : F → ℝ} (hθ : QL θ) (hψ : QL ψ) (a b c : ℝ) :
    QL (fun x => a * θ x + b * ψ x + c) := by
  intro x h
  obtain ⟨p0, p1, p2, hp⟩ := hθ x h
  obtain ⟨q0, q1, q2, hq⟩ := hψ x h
  refine ⟨a * p0 + b * q0 + c, a * p1 + b * q1, a * p2 + b * q2, fun t => ?_⟩
  simp only [hp, hq]; ring

lemma QL.neg {θ : F → ℝ} (hθ : QL θ) : QL (fun x => θ (-x)) := by
  intro x h
  obtain ⟨p0, p1, p2, hp⟩ := hθ (-x) (-h)
  refine ⟨p0, p1, p2, fun t => ?_⟩
  rw [← hp]; show θ (-(x + t • h)) = _; rw [neg_add, smul_neg]

lemma QL.shift {θ : F → ℝ} (hθ : QL θ) (y : F) : QL (fun x => θ (x + y)) := by
  intro x h
  obtain ⟨p0, p1, p2, hp⟩ := hθ (x + y) h
  refine ⟨p0, p1, p2, fun t => ?_⟩
  rw [← hp]; show θ (x + t • h + y) = _; congr 1; abel

lemma hom1 (θ : F → ℝ) (hq : QL θ)
    (hh : ∀ (t : ℝ) (x : F), θ (t • x) = t * θ x) (x y : F) : θ (x + y) = θ x + θ y := by
  obtain ⟨p0, p1, p2, hp⟩ := hq y x
  obtain ⟨q0, q1, q2, hq'⟩ := hq x y
  have key : ∀ b : ℝ, b ≠ 0 → q0 + q1 * b + q2 * b ^ 2 = b * (p0 + p1 * b⁻¹ + p2 * b⁻¹ ^ 2) := by
    intro b hb
    rw [← hq', ← hp, ← hh]
    congr 1
    rw [smul_add, smul_smul, mul_inv_cancel₀ hb, one_smul, add_comm]
  have e1 := key 1 one_ne_zero
  have e2 := key (-1) (by norm_num)
  have e3 := key 2 (by norm_num)
  have e4 := key (-2) (by norm_num)
  have hx : θ x = q0 := by simpa using hq' 0
  have hy : θ y = p0 := by simpa using hp 0
  have hxy : θ (x + y) = p0 + p1 + p2 := by
    have := hp 1; simp only [one_smul, mul_one, one_pow] at this; rw [add_comm]; linarith
  norm_num at e1 e2 e3 e4
  rw [hx, hy, hxy]
  linarith

lemma hom2 (θ : F → ℝ) (hq : QL θ)
    (hh : ∀ (t : ℝ) (x : F), θ (t • x) = t ^ 2 * θ x) (a : ℝ) (x y : F) :
    θ (a • x + y) - θ (a • x) - θ y = a * (θ (x + y) - θ x - θ y) := by
  obtain ⟨p0, p1, p2, hp⟩ := hq y x
  obtain ⟨q0, q1, q2, hq'⟩ := hq x y
  have key : ∀ b : ℝ, b ≠ 0 → q0 + q1 * b + q2 * b ^ 2 = b ^ 2 * (p0 + p1 * b⁻¹ + p2 * b⁻¹ ^ 2) := by
    intro b hb
    rw [← hq', ← hp, ← hh]
    congr 1
    rw [smul_add, smul_smul, mul_inv_cancel₀ hb, one_smul, add_comm]
  have e1 := key 1 one_ne_zero
  have e2 := key (-1) (by norm_num)
  have e3 := key 2 (by norm_num)
  have hx : θ x = q0 := by simpa using hq' 0
  have hy : θ y = p0 := by simpa using hp 0
  have hxy : θ (x + y) = p0 + p1 + p2 := by
    have := hp 1; simp only [one_smul, mul_one, one_pow] at this; rw [add_comm]; linarith
  have hax : θ (a • x + y) = p0 + p1 * a + p2 * a ^ 2 := by rw [add_comm]; exact hp a
  norm_num at e1 e2 e3
  rw [hax, hh, hx, hy, hxy]
  have : q0 = p2 := by linarith
  rw [this]; ring

theorem alg (G : F → ℝ) (hG : QL G) :
    ∃ (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (L : F →ₗ[ℝ] ℝ) (c : ℝ), ∀ x, G x = B x x + L x + c := by
  set ℓ : F → ℝ := fun x => (1/2) * G x + (-1/2) * G (-x) + 0 with hℓ
  set β : F → ℝ := fun x => (1/2) * G x + (1/2) * G (-x) + (- G 0) with hβ
  have h0 : ∀ x : F, ∀ t : ℝ, G (t • x) = G 0 + ℓ x * t + β x * t ^ 2 := by
    intro x t
    obtain ⟨c0, c1, c2, hc⟩ := hG 0 x
    have e0 := hc 0
    have e1 := hc 1
    have e2 := hc (-1)
    have et := hc t
    simp only [zero_add, zero_smul, one_smul, neg_smul, mul_zero, mul_one, one_pow, add_zero,
      mul_neg, neg_one_sq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at e0 e1 e2 et
    simp only [hℓ, hβ]
    rw [et, e0, e1, e2]; ring
  have ℓhom : ∀ (t : ℝ) (x : F), ℓ (t • x) = t * ℓ x := by
    intro t x
    have a1 := h0 x t
    have a2 := h0 x (-t)
    simp only [hℓ]
    rw [← neg_smul, a1, a2]; simp only [hℓ]; ring
  have βhom : ∀ (t : ℝ) (x : F), β (t • x) = t ^ 2 * β x := by
    intro t x
    have a1 := h0 x t
    have a2 := h0 x (-t)
    have a3 := h0 x 0
    simp only [zero_smul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at a3
    simp only [hβ]
    rw [← neg_smul, a1, a2]; simp only [hβ]; ring
  have ℓQL : QL ℓ := hG.comb hG.neg _ _ _
  have βQL : QL β := hG.comb hG.neg _ _ _
  have ℓadd := hom1 ℓ ℓQL ℓhom
  set B0 : F → F → ℝ := fun x y => (1/2) * β (x + y) + (-1/2) * β x + (-(β y) / 2) with hB0
  have B0smul : ∀ (a : ℝ) (x y : F), B0 (a • x) y = a * B0 x y := by
    intro a x y
    have := hom2 β βQL βhom a x y
    simp only [hB0]
    linear_combination (1/2) * this
  have B0QL : ∀ y, QL (fun x => B0 x y) := fun y => (βQL.shift y).comb βQL _ _ _
  have B0add : ∀ x x' y, B0 (x + x') y = B0 x y + B0 x' y := fun x x' y =>
    hom1 (fun x => B0 x y) (B0QL y) (fun t x => B0smul t x y) x x'
  have B0symm : ∀ x y, B0 x y = B0 y x := by
    intro x y; simp only [hB0]; rw [add_comm x y]; ring
  have B0diag : ∀ x, B0 x x = β x := by
    intro x
    simp only [hB0]
    rw [← two_smul ℝ x, βhom]; ring
  let L : F →ₗ[ℝ] ℝ :=
    { toFun := ℓ
      map_add' := ℓadd
      map_smul' := fun t x => by simp only [ℓhom, smul_eq_mul, RingHom.id_apply] }
  let B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ B0 B0add B0smul
    (fun x y y' => by rw [B0symm, B0add, B0symm, B0symm x y'])
    (fun a x y => by rw [B0symm, B0smul, B0symm, smul_eq_mul])
  refine ⟨B, L, G 0, fun x => ?_⟩
  simp only [B, L, LinearMap.mk₂_apply, LinearMap.coe_mk, AddHom.coe_mk, B0diag]
  simp only [hℓ, hβ]; ring

end RW1115

namespace RW1115

lemma upgrade (ψ : ℝ → ℝ)
    (h : ∀ T : ℝ, 0 < T → ∃ c0 c1 c2 : ℝ, ∀ t ∈ Set.Icc (-T) T, ψ t = c0 + c1 * t + c2 * t ^ 2) :
    ∃ c0 c1 c2 : ℝ, ∀ t, ψ t = c0 + c1 * t + c2 * t ^ 2 := by
  obtain ⟨c0, c1, c2, hc⟩ := h 1 one_pos
  refine ⟨c0, c1, c2, fun t => ?_⟩
  have hT : 0 < |t| + 1 := by positivity
  obtain ⟨d0, d1, d2, hd⟩ := h (|t| + 1) hT
  have ha := abs_nonneg t
  have m1 : (-1:ℝ) ∈ Set.Icc (-(|t|+1)) (|t|+1) := ⟨by linarith, by linarith⟩
  have m0 : (0:ℝ) ∈ Set.Icc (-(|t|+1)) (|t|+1) := ⟨by linarith, by linarith⟩
  have m2 : (1:ℝ) ∈ Set.Icc (-(|t|+1)) (|t|+1) := ⟨by linarith, by linarith⟩
  have mt : t ∈ Set.Icc (-(|t|+1)) (|t|+1) := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have a1 := hc (-1) ⟨le_refl _, by norm_num⟩
  have a0 := hc 0 ⟨by norm_num, by norm_num⟩
  have a2 := hc 1 ⟨by norm_num, le_refl _⟩
  have b1 := hd (-1) m1
  have b0 := hd 0 m0
  have b2 := hd 1 m2
  rw [hd t mt]
  norm_num at a1 a0 a2 b1 b0 b2
  have e0 : d0 = c0 := by linarith
  have e1 : d1 = c1 := by linarith
  have e2 : d2 = c2 := by linarith
  rw [e0, e1, e2]

end RW1115

theorem RW_chap_11_15
  (f : E → EReal)
  (C : Set E)
  (hC_convex : Convex ℝ C) :
  ((∃ (A : E →L[ℝ] E) (a : E) (α : ℝ),
      ∀ x ∈ C,
        f x =
          (((1 / 2 : ℝ) * inner ℝ x (A x) +
              inner ℝ a x + α) : EReal)) ↔
    ∀ x₀ ∈ C, ∀ x₁ ∈ C,
      ∃ (A : E →L[ℝ] E) (a : E) (α : ℝ),
        ∀ x ∈ {x : E | ∃ t ∈ Set.Icc (0 : ℝ) 1,
            x = (1 - t) • x₀ + t • x₁},
          f x =
            (((1 / 2 : ℝ) * inner ℝ x (A x) +
                inner ℝ a x + α) : EReal)) := by
  constructor
  · rintro ⟨A, a, α, h⟩ x₀ hx₀ x₁ hx₁
    refine ⟨A, a, α, fun x hx => h x ?_⟩
    obtain ⟨t, ht, rfl⟩ := hx
    exact hC_convex hx₀ hx₁ (sub_nonneg.2 ht.2) ht.1 (by ring)
  intro H
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · exact ⟨0, 0, 0, fun x hx => by simp [hCe] at hx⟩
  set g : E → ℝ := fun x => (f x).toReal with hg
  have hfg : ∀ y ∈ C, f y = ((g y : ℝ) : EReal) := by
    intro y hy
    obtain ⟨A, a, α, hQ⟩ := H y hy y hy
    have := hQ y ⟨0, ⟨le_refl _, zero_le_one⟩, by simp⟩
    simp only [hg]
    rw [this, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.toReal_coe]
  have seg : ∀ (x h : E) (a b : ℝ), a ≤ b → x + a • h ∈ C → x + b • h ∈ C →
      ∃ d0 d1 d2 : ℝ, ∀ t ∈ Set.Icc a b,
        x + t • h ∈ C ∧ g (x + t • h) = d0 + d1 * t + d2 * t ^ 2 := by
    intro x h a b hab ha hb
    obtain ⟨A, a', α, hQ⟩ := H _ ha _ hb
    refine ⟨(1/2) * inner ℝ x (A x) + inner ℝ a' x + α,
      (1/2) * (inner ℝ x (A h) + inner ℝ h (A x)) + inner ℝ a' h,
      (1/2) * inner ℝ h (A h), fun t ht => ?_⟩
    obtain ⟨τ, hτ, hxt⟩ : ∃ τ ∈ Set.Icc (0:ℝ) 1,
        x + t • h = (1 - τ) • (x + a • h) + τ • (x + b • h) := by
      rcases eq_or_lt_of_le hab with hab' | hab'
      · refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
        have : t = a := le_antisymm (by linarith [ht.2]) ht.1
        subst this; simp
      · refine ⟨(t - a) / (b - a), ⟨div_nonneg (by linarith [ht.1]) (by linarith),
          (div_le_one (by linarith)).2 (by linarith [ht.2])⟩, ?_⟩
        have hba : b - a ≠ 0 := by linarith
        have key : (1 - (t - a) / (b - a)) * a + (t - a) / (b - a) * b = t := by
          field_simp; ring
        calc x + t • h = x + ((1 - (t - a) / (b - a)) * a + (t - a) / (b - a) * b) • h := by
              rw [key]
          _ = _ := by module
    refine ⟨?_, ?_⟩
    · rw [hxt]; exact hC_convex ha hb (by linarith [hτ.2]) hτ.1 (by ring)
    · have hf := hQ (x + t • h) ⟨τ, hτ, hxt⟩
      simp only [hg]
      rw [hf, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.toReal_coe]
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      ring
  obtain ⟨p, hp⟩ := hCne.intrinsicInterior hC_convex
  have hpC : p ∈ C := intrinsicInterior_subset hp
  set V : Submodule ℝ E := (affineSpan ℝ C).direction with hV
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ v ∈ V, ‖v‖ < ε → p + v ∈ C := by
    rw [mem_intrinsicInterior] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hq
    obtain ⟨ε, hε, hsub⟩ := hq
    refine ⟨ε, hε, fun v hv hvn => ?_⟩
    have hmem : v +ᵥ (q : E) ∈ affineSpan ℝ C := AffineSubspace.vadd_mem_of_mem_direction hv q.2
    have h1 : (⟨v +ᵥ (q : E), hmem⟩ : affineSpan ℝ C) ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, Subtype.dist_eq]
      simpa [dist_eq_norm] using hvn
    have h2 := hsub h1
    simpa [add_comm] using h2
  have hdir : ∀ x ∈ C, x - p ∈ V := fun x hx =>
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hx) (subset_affineSpan ℝ C hpC)
  obtain ⟨r, hr⟩ := V.subtype.exists_leftInverse_of_injective V.ker_subtype
  set Pr : E →ₗ[ℝ] E := V.subtype ∘ₗ r with hPr
  have hPrV : ∀ x, Pr x ∈ V := fun x => (r x).2
  have hPrid : ∀ v ∈ V, Pr v = v := fun v hv => by
    have := LinearMap.congr_fun hr ⟨v, hv⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    simp only [hPr, LinearMap.comp_apply, this, Submodule.subtype_apply]
  set ℓ0 : E → ℝ := fun v => (g (p + v) - g (p - v)) / 2 with hℓ0
  set β0 : E → ℝ := fun v => (g (p + v) + g (p - v)) / 2 - g p with hβ0
  have hline : ∀ u ∈ V, ‖u‖ < ε → ∀ s ∈ Set.Icc (-1:ℝ) 1,
      g (p + s • u) = g p + ℓ0 u * s + β0 u * s ^ 2 := by
    intro u hu hun s hs
    have hm : ∀ s : ℝ, s ∈ Set.Icc (-1:ℝ) 1 → p + s • u ∈ C := fun s hs =>
      hball _ (V.smul_mem _ hu) (by
        rw [norm_smul]
        calc ‖s‖ * ‖u‖ ≤ 1 * ‖u‖ := by
              gcongr; rw [Real.norm_eq_abs]; exact abs_le.2 ⟨hs.1, hs.2⟩
          _ < ε := by simpa using hun)
    obtain ⟨d0, d1, d2, hd⟩ := seg p u (-1) 1 (by norm_num) (hm _ ⟨le_refl _, by norm_num⟩)
      (hm _ ⟨by norm_num, le_refl _⟩)
    have e0 := (hd 0 ⟨by norm_num, by norm_num⟩).2
    have e1 := (hd 1 ⟨by norm_num, by norm_num⟩).2
    have e2 := (hd (-1) ⟨by norm_num, by norm_num⟩).2
    have es := (hd s hs).2
    simp only [zero_smul, add_zero, one_smul, neg_smul, mul_zero, mul_one, one_pow, mul_neg,
      neg_one_sq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at e0 e1 e2
    rw [← sub_eq_add_neg] at e2
    show _ = g p + (g (p + u) - g (p - u)) / 2 * s + ((g (p + u) + g (p - u)) / 2 - g p) * s ^ 2
    rw [es, e0, e1, e2]; ring
  have hhom : ∀ u ∈ V, ‖u‖ < ε → ∀ s ∈ Set.Icc (-1:ℝ) 1,
      ℓ0 (s • u) = s * ℓ0 u ∧ β0 (s • u) = s ^ 2 * β0 u := by
    intro u hu hun s hs
    have a1 := hline u hu hun s hs
    have a2 := hline u hu hun (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [neg_smul, ← sub_eq_add_neg] at a2
    constructor
    · show (g (p + s • u) - g (p - s • u)) / 2 = s * ℓ0 u
      rw [a1, a2]; ring
    · show (g (p + s • u) + g (p - s • u)) / 2 - g p = s ^ 2 * β0 u
      rw [a1, a2]; ring
  have hcons : ∀ z ∈ V, ∀ m m' : ℝ, 0 < m' → m' ≤ m → ‖m • z‖ < ε →
      m⁻¹ * ℓ0 (m • z) = m'⁻¹ * ℓ0 (m' • z) ∧
        m⁻¹ ^ 2 * β0 (m • z) = m'⁻¹ ^ 2 * β0 (m' • z) := by
    intro z hz m m' hm' hmm hn
    have hm : 0 < m := lt_of_lt_of_le hm' hmm
    have hs : m' / m ∈ Set.Icc (-1:ℝ) 1 :=
      ⟨by linarith [div_pos hm' hm], (div_le_one hm).2 hmm⟩
    have heq : m' • z = (m' / m) • (m • z) := by rw [smul_smul, div_mul_cancel₀ _ hm.ne']
    obtain ⟨h1, h2⟩ := hhom (m • z) (V.smul_mem _ hz) hn (m' / m) hs
    rw [heq, h1, h2]
    constructor
    · field_simp
    · field_simp
  set κ : E → ℝ := fun z => ε / (2 * (‖z‖ + 1)) with hκ
  have hκpos : ∀ z, 0 < κ z := fun z => by simp only [hκ]; positivity
  have hκn : ∀ z, ‖κ z • z‖ < ε := by
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hκpos z)]
    simp only [hκ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg z]
  set Φ : E → ℝ := fun z => g p + (κ z)⁻¹ * ℓ0 (κ z • z) + (κ z)⁻¹ ^ 2 * β0 (κ z • z) with hΦ
  have hΦ1 : ∀ z ∈ V, ∀ m : ℝ, 0 < m → ‖m • z‖ < ε →
      Φ z = g p + m⁻¹ * ℓ0 (m • z) + m⁻¹ ^ 2 * β0 (m • z) := by
    intro z hz m hm hn
    show g p + (κ z)⁻¹ * ℓ0 (κ z • z) + (κ z)⁻¹ ^ 2 * β0 (κ z • z) = _
    rcases le_total m (κ z) with h | h
    · obtain ⟨h1, h2⟩ := hcons z hz (κ z) m hm h (hκn z)
      rw [h1, h2]
    · obtain ⟨h1, h2⟩ := hcons z hz m (κ z) (hκpos z) h hn
      rw [h1, h2]
  have hΦ2 : ∀ z ∈ V, ‖z‖ < ε → Φ z = g (p + z) := by
    intro z hz hn
    rw [hΦ1 z hz 1 one_pos (by simpa using hn)]
    simp only [inv_one, one_smul, one_pow, one_mul]
    show g p + (g (p + z) - g (p - z)) / 2 + ((g (p + z) + g (p - z)) / 2 - g p) = g (p + z)
    ring
  have hΦ3 : ∀ v ∈ V, ∀ w ∈ V, ∀ T : ℝ, 0 < T →
      ∃ c0 c1 c2 : ℝ, ∀ t ∈ Set.Icc (-T) T, Φ (v + t • w) = c0 + c1 * t + c2 * t ^ 2 := by
    intro v hv w hw T hT
    set m : ℝ := ε / (2 * (‖v‖ + T * ‖w‖ + 1)) with hm
    have hmpos : 0 < m := by positivity
    have hbound : ∀ t ∈ Set.Icc (-T) T, ‖m • (v + t • w)‖ < ε := by
      intro t ht
      have h1 : ‖v + t • w‖ ≤ ‖v‖ + T * ‖w‖ := by
        calc ‖v + t • w‖ ≤ ‖v‖ + ‖t • w‖ := norm_add_le _ _
          _ = ‖v‖ + |t| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ ‖v‖ + T * ‖w‖ := by gcongr; exact abs_le.2 ⟨ht.1, ht.2⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hmpos]
      calc m * ‖v + t • w‖ ≤ m * (‖v‖ + T * ‖w‖) := by gcongr
        _ < ε := by
          rw [hm, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [mul_pos hε (show 0 < ‖v‖ + T * ‖w‖ + 2 by positivity)]
    have hsegV : ∀ y k : E, y ∈ V → k ∈ V → ‖y + T • k‖ < ε → ‖y + (-T) • k‖ < ε →
        ∃ d0 d1 d2 : ℝ, ∀ t ∈ Set.Icc (-T) T, g (p + (y + t • k)) = d0 + d1 * t + d2 * t ^ 2 := by
      intro y k hy hk h1 h2
      obtain ⟨d0, d1, d2, hd⟩ := seg (p + y) k (-T) T (by linarith)
        (by rw [add_assoc]; exact hball _ (V.add_mem hy (V.smul_mem _ hk)) h2)
        (by rw [add_assoc]; exact hball _ (V.add_mem hy (V.smul_mem _ hk)) h1)
      exact ⟨d0, d1, d2, fun t ht => by rw [← add_assoc]; exact (hd t ht).2⟩
    have hTm : T ∈ Set.Icc (-T) T := ⟨by linarith, le_refl _⟩
    have hTm' : -T ∈ Set.Icc (-T) T := ⟨le_refl _, by linarith⟩
    have e : ∀ t : ℝ, m • v + t • (m • w) = m • (v + t • w) := fun t => by
      rw [smul_add, smul_comm]
    have e' : ∀ t : ℝ, -(m • v) + t • -(m • w) = -(m • (v + t • w)) := fun t => by
      rw [smul_neg, ← neg_add, e]
    obtain ⟨d0, d1, d2, hd⟩ := hsegV (m • v) (m • w) (V.smul_mem _ hv) (V.smul_mem _ hw)
      (by rw [e]; exact hbound T hTm) (by rw [e]; exact hbound (-T) hTm')
    obtain ⟨e0, e1, e2, he⟩ := hsegV (-(m • v)) (-(m • w)) (V.neg_mem (V.smul_mem _ hv))
      (V.neg_mem (V.smul_mem _ hw))
      (by rw [e', norm_neg]; exact hbound T hTm) (by rw [e', norm_neg]; exact hbound (-T) hTm')
    refine ⟨g p + m⁻¹ * ((d0 - e0) / 2) + m⁻¹ ^ 2 * ((d0 + e0) / 2 - g p),
      m⁻¹ * ((d1 - e1) / 2) + m⁻¹ ^ 2 * ((d1 + e1) / 2),
      m⁻¹ * ((d2 - e2) / 2) + m⁻¹ ^ 2 * ((d2 + e2) / 2), fun t ht => ?_⟩
    have hvt : v + t • w ∈ V := V.add_mem hv (V.smul_mem _ hw)
    rw [hΦ1 _ hvt m hmpos (hbound t ht)]
    have h1 := hd t ht
    have h2 := he t ht
    rw [e] at h1
    rw [e', ← sub_eq_add_neg] at h2
    show g p + m⁻¹ * ((g (p + m • (v + t • w)) - g (p - m • (v + t • w))) / 2) +
      m⁻¹ ^ 2 * ((g (p + m • (v + t • w)) + g (p - m • (v + t • w))) / 2 - g p) = _
    rw [h1, h2]; ring
  set G : E → ℝ := fun x => Φ (Pr x) with hG
  have hGQL : RW1115.QL G := by
    intro x h
    apply RW1115.upgrade (fun t => G (x + t • h))
    intro T hT
    obtain ⟨c0, c1, c2, hc⟩ := hΦ3 (Pr x) (hPrV x) (Pr h) (hPrV h) T hT
    refine ⟨c0, c1, c2, fun t ht => ?_⟩
    show Φ (Pr (x + t • h)) = _
    rw [map_add, map_smul]; exact hc t ht
  obtain ⟨B, L, c, hBL⟩ := RW1115.alg G hGQL
  have hext : ∀ x ∈ C, g x = Φ (x - p) := by
    intro x hx
    set z := x - p with hz
    have hzV : z ∈ V := hdir x hx
    obtain ⟨e0, e1, e2, he⟩ := hΦ3 0 V.zero_mem z hzV 1 one_pos
    obtain ⟨d0, d1, d2, hd⟩ := seg p z 0 1 zero_le_one (by simpa using hpC) (by simp [hz, hx])
    set s1 : ℝ := min (1/2) (ε / (2 * (‖z‖ + 1))) with hs1
    have hs1pos : 0 < s1 := lt_min (by norm_num) (by positivity)
    have hs1le : s1 ≤ 1/2 := min_le_left _ _
    have hs1le' : s1 ≤ ε / (2 * (‖z‖ + 1)) := min_le_right _ _
    have hsmall : ∀ s : ℝ, 0 ≤ s → s ≤ 2 * s1 → ‖s • z‖ < ε := by
      intro s hs0 hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      have : s ≤ ε / (‖z‖ + 1) := by
        calc s ≤ 2 * s1 := hs
          _ ≤ 2 * (ε / (2 * (‖z‖ + 1))) := by gcongr
          _ = ε / (‖z‖ + 1) := by field_simp
      calc s * ‖z‖ ≤ ε / (‖z‖ + 1) * ‖z‖ := by gcongr
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg z]
    have hagree : ∀ s : ℝ, 0 ≤ s → s ≤ 2 * s1 →
        e0 + e1 * s + e2 * s ^ 2 = d0 + d1 * s + d2 * s ^ 2 := by
      intro s hs0 hs
      have hsI : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs0, by linarith⟩
      have hsI' : s ∈ Set.Icc (-1:ℝ) 1 := ⟨by linarith, by linarith⟩
      rw [← (hd s hsI).2, ← he s hsI', zero_add]
      exact hΦ2 _ (V.smul_mem _ hzV) (hsmall s hs0 hs)
    have a0 := hagree 0 le_rfl (by linarith)
    have a1 := hagree s1 hs1pos.le (by linarith)
    have a2 := hagree (2 * s1) (by linarith) le_rfl
    have hx' : x = p + (1:ℝ) • z := by simp [hz]
    have g1 := (hd 1 ⟨zero_le_one, le_rfl⟩).2
    have Φ1 := he 1 ⟨by norm_num, le_rfl⟩
    rw [zero_add] at Φ1
    have k2 : (e2 - d2) * s1 ^ 2 = 0 := by linear_combination (a2 - 2 * a1 + a0) / 2
    have k2' : e2 = d2 := by
      rcases mul_eq_zero.1 k2 with h | h
      · linarith
      · exact absurd h (pow_pos hs1pos 2).ne'
    have k1 : (e1 - d1) * s1 = 0 := by linear_combination a1 - a0 - k2
    have k1' : e1 = d1 := by
      rcases mul_eq_zero.1 k1 with h | h
      · linarith
      · exact absurd h hs1pos.ne'
    have k0 : e0 = d0 := by linear_combination a0
    calc g x = g (p + (1:ℝ) • z) := by rw [← hx']
      _ = d0 + d1 * 1 + d2 * 1 ^ 2 := g1
      _ = e0 + e1 * 1 + e2 * 1 ^ 2 := by rw [k0, k1', k2']
      _ = Φ ((1:ℝ) • z) := Φ1.symm
      _ = Φ z := by rw [one_smul]
  have hfin : ∀ x ∈ C, g x = B (x - p) (x - p) + L (x - p) + c := by
    intro x hx
    rw [hext x hx, ← hBL]
    show Φ (x - p) = Φ (Pr (x - p))
    rw [hPrid _ (hdir x hx)]
  set M : E →ₗ[ℝ] ℝ := L - B.flip p - B p with hM
  set α : ℝ := c - L p + B p p with hα
  set a : E := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap M) with ha
  have ha' : ∀ x, inner ℝ a x = M x := by
    intro x; rw [ha, InnerProductSpace.toDual_symm_apply]; rfl
  set b := stdOrthonormalBasis ℝ E with hb
  set A0 : E →ₗ[ℝ] E := (2:ℝ) • ∑ i, (B.flip (b i)).smulRight (b i) with hA0
  have hA0' : ∀ x, inner ℝ x (A0 x) = 2 * B x x := by
    intro x
    simp only [hA0, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smulRight_apply, LinearMap.flip_apply, real_inner_smul_right, inner_sum]
    congr 1
    rw [show B x x = B x (∑ i, inner ℝ (b i) x • b i) by rw [b.sum_repr' x], map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, real_inner_comm]; ring
  refine ⟨LinearMap.toContinuousLinearMap A0, a, α, fun x hx => ?_⟩
  rw [hfg x hx, hfin x hx, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  rw [LinearMap.coe_toContinuousLinearMap', hA0', ha']
  simp only [hM, hα, LinearMap.sub_apply, LinearMap.flip_apply, map_sub]
  ring

end RW_chap_11_15
