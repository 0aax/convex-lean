import ConvexStarLib.Defs

/-!
# `FCA_chap_D_ex12`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_ex12` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_ex12`, so the main result is `FCA_chap_D_ex12.FCA_chap_D_ex12`.
-/

namespace FCA_chap_D_ex12

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_ex12
  (f : EuclideanSpace ℝ (Fin 1) → ℝ)
  (g : EuclideanSpace ℝ (Fin 1) → ℝ)
  (h_convex : (InConvRn (liftRealtoEReal f)) ∧ (InConvRn (liftRealtoEReal g)))
  (h_pos : ∀ x, (f x > 0) ∧ (g x > 0))
  (hf_increasing : ∀ x y, (x 0 < y 0) → (f x < f y))
  (hg_increasing : ∀ x y, (x 0 < y 0) → (g x < g y)) :
  let fg := fun x => (f x) * (g x)
  (InConvRn (liftRealtoEReal fg)) ∧ (∀ x y, (x 0 < y 0) → (fg x < fg y)) ∧
  (∀ x, directionalSubdifferential (liftRealtoEReal fg) x =
  setAdd ({v : EuclideanSpace ℝ (Fin 1) | ∃ y ∈ directionalSubdifferential (liftRealtoEReal g) x, v 0 = ((f x) * (y 0))})
          ({v : EuclideanSpace ℝ (Fin 1) | ∃ y ∈ directionalSubdifferential (liftRealtoEReal f) x, v 0 = ((g x) * (y 0))})) := by
  -- If `t ↦ F (x + t • d)` has right derivative `D` at `0`, the directional derivative is `D`.
  have dd_eq : ∀ (F : EuclideanSpace ℝ (Fin 1) → ℝ) (x d : EuclideanSpace ℝ (Fin 1)) (D : ℝ),
      HasDerivWithinAt (fun t : ℝ => F (x + t • d)) D (Set.Ioi 0) 0 →
      directionalDeriv (liftRealtoEReal F) x d = (D : EReal) := by
    intro F x d D h
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Set.Ioi 0)] at h
    have h2 := (continuous_coe_real_ereal.tendsto D).comp h
    refine h2.congr' ?_
    filter_upwards with t
    simp [differenceQuotient, liftRealtoEReal, slope_def_field, EReal.coe_sub, EReal.coe_div]
  -- In dimension one, the directional derivative is given by the one-sided derivatives
  -- `R` and `L` of the restriction `u ↦ F (x + u • e)`.
  have dd_formula : ∀ (F : EuclideanSpace ℝ (Fin 1) → ℝ) (x : EuclideanSpace ℝ (Fin 1)) (R L : ℝ),
      HasDerivWithinAt (fun u : ℝ => F (x + u • EuclideanSpace.single 0 1)) R (Set.Ioi 0) 0 →
      HasDerivWithinAt (fun u : ℝ => F (x + u • EuclideanSpace.single 0 1)) L (Set.Iio 0) 0 →
      ∀ d : EuclideanSpace ℝ (Fin 1), directionalDeriv (liftRealtoEReal F) x d =
        ((if 0 ≤ d 0 then R * d 0 else L * d 0 : ℝ) : EReal) := by
    intro F x R L hR hL d
    have hd : d = d 0 • EuclideanSpace.single 0 1 := by
      ext i; fin_cases i; simp
    have hfun : (fun t : ℝ => F (x + t • d)) =
        (fun u : ℝ => F (x + u • EuclideanSpace.single 0 1)) ∘ (fun t => t * d 0) := by
      funext t
      simp only [Function.comp]
      congr 2
      conv_lhs => rw [hd]
      rw [smul_smul]
    apply dd_eq
    rw [hfun]
    split_ifs with h0
    · exact (hR.Ici_of_Ioi).comp_of_eq 0 (hasDerivAt_mul_const (d 0)).hasDerivWithinAt
        (fun t (ht : 0 < t) => (mul_nonneg ht.le h0 : 0 ≤ t * d 0)) (by simp)
    · exact (hL.Iic_of_Iio).comp_of_eq 0 (hasDerivAt_mul_const (d 0)).hasDerivWithinAt
        (fun t (ht : 0 < t) => ((mul_neg_of_pos_of_neg ht (not_le.1 h0)).le : t * d 0 ≤ 0))
        (by simp)
  -- Hence the directional subdifferential is the interval `[L, R]`.
  have subdiff_eq : ∀ (F : EuclideanSpace ℝ (Fin 1) → ℝ) (x : EuclideanSpace ℝ (Fin 1)) (R L : ℝ),
      HasDerivWithinAt (fun u : ℝ => F (x + u • EuclideanSpace.single 0 1)) R (Set.Ioi 0) 0 →
      HasDerivWithinAt (fun u : ℝ => F (x + u • EuclideanSpace.single 0 1)) L (Set.Iio 0) 0 →
      directionalSubdifferential (liftRealtoEReal F) x = {s | L ≤ s 0 ∧ s 0 ≤ R} := by
    intro F x R L hR hL
    have hinner : ∀ s d : EuclideanSpace ℝ (Fin 1), inner ℝ s d = s 0 * d 0 := by
      intro s d
      simp [PiLp.inner_apply]
      ring
    ext s
    simp only [directionalSubdifferential, Set.mem_setOf_eq, dd_formula F x R L hR hL,
      EReal.coe_le_coe_iff, hinner]
    constructor
    · intro h
      have h1 := h (EuclideanSpace.single 0 1)
      have h2 := h (EuclideanSpace.single 0 (-1))
      norm_num at h1 h2
      constructor <;> linarith
    · rintro ⟨h1, h2⟩ d
      split_ifs with h0
      · exact mul_le_mul_of_nonneg_right h2 h0
      · nlinarith
  intro fg
  obtain ⟨⟨_, _, hf⟩, ⟨_, _, hg⟩⟩ := h_convex
  have hconv : ∀ F : EuclideanSpace ℝ (Fin 1) → ℝ,
      ConvexEReal (liftRealtoEReal F) ↔ ConvexOn ℝ Set.univ F := by
    intro F
    rw [ConvexEReal, convexOn_iff_convex_epigraph]
    have : epigraph (liftRealtoEReal F) =
        {p : EuclideanSpace ℝ (Fin 1) × ℝ | p.1 ∈ Set.univ ∧ F p.1 ≤ p.2} := by
      ext p; simp [epigraph, liftRealtoEReal]
    rw [this]
  have hfc : ConvexOn ℝ Set.univ f := (hconv f).1 hf
  have hgc : ConvexOn ℝ Set.univ g := (hconv g).1 hg
  have hfg_mono : ∀ x y : EuclideanSpace ℝ (Fin 1), x 0 < y 0 → fg x < fg y := by
    intro x y hxy
    exact mul_lt_mul'' (hf_increasing x y hxy) (hg_increasing x y hxy) (h_pos x).1.le
      (h_pos x).2.le
  have hext : ∀ x y : EuclideanSpace ℝ (Fin 1), x 0 = y 0 → x = y := by
    intro x y h; ext i; fin_cases i; exact h
  have hmv : MonovaryOn f g Set.univ := by
    intro i _ j _ hij
    rcases lt_trichotomy (i 0) (j 0) with h | h | h
    · exact (hf_increasing i j h).le
    · rw [hext i j h]
    · exact absurd hij (not_lt.2 (hg_increasing j i h).le)
  have hfgc : ConvexOn ℝ Set.univ fg :=
    hfc.mul hgc (fun x _ => (h_pos x).1.le) (fun x _ => (h_pos x).2.le) hmv
  refine ⟨⟨fun x => EReal.bot_lt_coe _, ⟨0, EReal.coe_lt_top _⟩, (hconv fg).2 hfgc⟩, hfg_mono, ?_⟩
  intro x
  have hres : ∀ F : EuclideanSpace ℝ (Fin 1) → ℝ, ConvexOn ℝ Set.univ F →
      ConvexOn ℝ Set.univ (fun u : ℝ => F (x + u • EuclideanSpace.single 0 1)) := by
    intro F hF
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    have h1 := hF.2 (Set.mem_univ (x + u • EuclideanSpace.single 0 1))
      (Set.mem_univ (x + v • EuclideanSpace.single 0 1)) ha hb hab
    have h2 : x + (a • u + b • v) • EuclideanSpace.single 0 1 =
        a • (x + u • EuclideanSpace.single 0 1) + b • (x + v • EuclideanSpace.single 0 1) := by
      simp only [smul_eq_mul]
      calc x + (a * u + b * v) • EuclideanSpace.single 0 1
          = (a + b) • x + (a * u + b * v) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
            rw [hab, one_smul]
        _ = a • (x + u • EuclideanSpace.single 0 1) + b • (x + v • EuclideanSpace.single 0 1) := by
            module
    simp only [h2]
    exact h1
  have hψf := hres f hfc
  have hψg := hres g hgc
  have hint : (0:ℝ) ∈ interior (Set.univ : Set ℝ) := by simp
  have hRf := hψf.hasDerivWithinAt_rightDeriv_of_mem_interior hint
  have hLf := hψf.hasDerivWithinAt_leftDeriv_of_mem_interior hint
  have hRg := hψg.hasDerivWithinAt_rightDeriv_of_mem_interior hint
  have hLg := hψg.hasDerivWithinAt_leftDeriv_of_mem_interior hint
  have hLRf := hψf.leftDeriv_le_rightDeriv_of_mem_interior hint
  have hLRg := hψg.leftDeriv_le_rightDeriv_of_mem_interior hint
  set Rf := derivWithin (fun u : ℝ => f (x + u • EuclideanSpace.single 0 1)) (Set.Ioi 0) 0
  set Lf := derivWithin (fun u : ℝ => f (x + u • EuclideanSpace.single 0 1)) (Set.Iio 0) 0
  set Rg := derivWithin (fun u : ℝ => g (x + u • EuclideanSpace.single 0 1)) (Set.Ioi 0) 0
  set Lg := derivWithin (fun u : ℝ => g (x + u • EuclideanSpace.single 0 1)) (Set.Iio 0) 0
  -- product rule for the one-sided derivatives
  have hRfg := hRf.mul hRg
  have hLfg := hLf.mul hLg
  simp only [zero_smul, add_zero] at hRfg hLfg
  rw [subdiff_eq f x Rf Lf hRf hLf, subdiff_eq g x Rg Lg hRg hLg,
    subdiff_eq fg x _ _ hRfg hLfg]
  have hfx := (h_pos x).1
  have hgx := (h_pos x).2
  ext s
  simp only [setAdd, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hc : s 0 ≤ f x * Rg + g x * Lf
    · refine ⟨EuclideanSpace.single 0 (s 0 - g x * Lf),
        ⟨EuclideanSpace.single 0 ((s 0 - g x * Lf) / f x), ⟨?_, ?_⟩, ?_⟩,
        EuclideanSpace.single 0 (g x * Lf), ⟨EuclideanSpace.single 0 Lf, ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · simp only [EuclideanSpace.single_apply, if_true]
        rw [le_div_iff₀ hfx]; nlinarith
      · simp only [EuclideanSpace.single_apply, if_true]
        rw [div_le_iff₀ hfx]; nlinarith
      · simp only [EuclideanSpace.single_apply, if_true]
        field_simp
      · simp
      · simpa using hLRf
      · simp
      · ext i; fin_cases i; simp
    · push_neg at hc
      refine ⟨EuclideanSpace.single 0 (f x * Rg),
        ⟨EuclideanSpace.single 0 Rg, ⟨?_, ?_⟩, ?_⟩,
        EuclideanSpace.single 0 (s 0 - f x * Rg),
        ⟨EuclideanSpace.single 0 ((s 0 - f x * Rg) / g x), ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · simpa using hLRg
      · simp
      · simp
      · simp only [EuclideanSpace.single_apply, if_true]
        rw [le_div_iff₀ hgx]; nlinarith
      · simp only [EuclideanSpace.single_apply, if_true]
        rw [div_le_iff₀ hgx]; nlinarith
      · simp only [EuclideanSpace.single_apply, if_true]
        field_simp
      · ext i; fin_cases i; simp
  · rintro ⟨c, ⟨y, ⟨hy1, hy2⟩, hc⟩, k, ⟨z, ⟨hz1, hz2⟩, hk⟩, rfl⟩
    simp only [PiLp.add_apply, hc, hk]
    constructor <;> nlinarith

end FCA_chap_D_ex12
