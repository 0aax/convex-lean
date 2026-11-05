import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable def bregmanDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ)
  (x : E)
  (y : E) : ℝ :=
  (f x) - (f y) - (fderiv ℝ f y (x - y))

def IsMirrorMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓓 : Set E)
  (phi : E → ℝ) : Prop :=
  (StrictConvexOn ℝ 𝓓 phi) ∧
  (DifferentiableOn ℝ phi 𝓓) ∧
  (∀ (ℓ : E →L[ℝ] ℝ), ∃ y ∈ 𝓓, fderiv ℝ phi y = ℓ) ∧
  (∀ b ∈ frontier 𝓓, Filter.Tendsto (fun x => ‖fderiv ℝ phi x‖) (𝓝[𝓓] b) Filter.atTop)

noncomputable def prodBregmanDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (phix : E → ℝ)
  (phiy : F → ℝ)
  (z z' : E × F) : ℝ :=
  bregmanDivergence phix z.1 z'.1 +
  bregmanDivergence phiy z.2 z'.2

def IsSPMPSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (𝓧 : Set E)
  (𝓓x : Set E)
  (𝓨 : Set F)
  (𝓓y : Set F)
  (phi : E → F → ℝ)
  (phix : E → ℝ)
  (phiy : F → ℝ)
  (a b η : ℝ)
  (x_seq : ℕ → E)
  (y_seq : ℕ → F)
  (u_seq : ℕ → E)
  (v_seq : ℕ → F) : Prop :=
  (IsMinOn (fun z : E × F => a * phix z.1 + b * phiy z.2)
    ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))
    (x_seq 0, y_seq 0)) ∧
  (∀ t, (u_seq t, v_seq t) ∈ ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))) ∧
  (∀ t, IsMinOn
    (fun z : E × F =>
      η * (fderiv ℝ (fun x => phi x (y_seq t)) (x_seq t) z.1 +
           fderiv ℝ (fun y => -phi (x_seq t) y) (y_seq t) z.2) +
      prodBregmanDivergence
        (fun x => a * phix x)
        (fun y => b * phiy y)
        z
        (x_seq t, y_seq t))
    ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))
    (u_seq (t + 1), v_seq (t + 1))) ∧
  (∀ t, (x_seq t, y_seq t) ∈ ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))) ∧
  (∀ t, IsMinOn
    (fun z : E × F =>
      η * (fderiv ℝ (fun x => phi x (v_seq (t + 1))) (u_seq (t + 1)) z.1 +
           fderiv ℝ (fun y => -phi (u_seq (t + 1)) y) (v_seq (t + 1)) z.2) +
      prodBregmanDivergence
        (fun x => a * phix x)
        (fun y => b * phiy y)
        z
        (x_seq t, y_seq t))
    ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))
    (x_seq (t + 1), y_seq (t + 1)))

theorem saddle_point_mirror_prox_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {t : ℕ}
  (𝓧 : Set E)
  (𝓓x : Set E)
  (𝓨 : Set F)
  (𝓓y : Set F)
  (phi : E → F → ℝ)
  (phix : E → ℝ)
  (phiy : F → ℝ)
  (x_seq : ℕ → E)
  (y_seq : ℕ → F)
  (u_seq : ℕ → E)
  (v_seq : ℕ → F)
  (a b η : ℝ)
  (Rx Ry β₁₁ β₁₂ β₂₂ β₂₁ : ℝ)
  (hRx_sq : Rx ^ 2 = sSup {v | ∃ z ∈ 𝓧 ∩ 𝓓x, phix z - phix (x_seq 0) = v})
  (hRy_sq : Ry ^ 2 = sSup {v | ∃ z ∈ 𝓨 ∩ 𝓓y, phiy z - phiy (y_seq 0) = v})
  (hRx_pos : Rx > 0) (hRy_pos : Ry > 0)
  (hβ₁₁_nonneg : β₁₁ > 0) (hβ₁₂_nonneg : β₁₂ > 0)
  (hβ₂₂_nonneg : β₂₂ > 0) (hβ₂₁_nonneg : β₂₁ > 0)
  (ht : t ≥ 1)
  (hx_0 : x_seq 0 ∈ 𝓧 ∩ 𝓓x)
  (hy_0 : y_seq 0 ∈ 𝓨 ∩ 𝓓y)
  (ha_val : a = 1 / Rx ^ 2)
  (hb_val : b = 1 / Ry ^ 2)
  (hη_val : η =
    1 / (2 * max (max (β₁₁ * Rx ^ 2) (β₂₂ * Ry ^ 2))
                 (max (β₁₂ * Rx * Ry) (β₂₁ * Rx * Ry))))
  (h_spmp_seq :
    IsSPMPSequence 𝓧 𝓓x 𝓨 𝓓y phi phix phiy a b η
      x_seq y_seq u_seq v_seq)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓓x_convex : Convex ℝ 𝓓x)
  (h𝓓x_open : IsOpen 𝓓x)
  (h𝓓x_contains : 𝓧 ⊆ closure 𝓓x)
  (h_interx_nonempty : Set.Nonempty (𝓧 ∩ 𝓓x))
  (h𝓨_compact : IsCompact 𝓨)
  (h𝓨_convex : Convex ℝ 𝓨)
  (h𝓨_nonempty : Set.Nonempty 𝓨)
  (h𝓓y_convex : Convex ℝ 𝓓y)
  (h𝓓y_open : IsOpen 𝓓y)
  (h𝓓y_contains : 𝓨 ⊆ closure 𝓓y)
  (h_intery_nonempty : Set.Nonempty (𝓨 ∩ 𝓓y))
  (hphix_diff : DifferentiableOn ℝ phix 𝓓x)
  (hphix_mirror : IsMirrorMap 𝓓x phix)
  (hphix_strong : StrongConvexOn (𝓧 ∩ 𝓓x) 1 phix)
  (hphiy_diff : DifferentiableOn ℝ phiy 𝓓y)
  (hphiy_mirror : IsMirrorMap 𝓓y phiy)
  (hphiy_strong : StrongConvexOn (𝓨 ∩ 𝓓y) 1 phiy)
  (hphi_convex_x : ∀ y ∈ 𝓨, ConvexOn ℝ 𝓧 (fun x => phi x y))
  (hphi_concave_y : ∀ x ∈ 𝓧, ConcaveOn ℝ 𝓨 (fun y => phi x y))
  (hphi_diff_x : ∀ y ∈ 𝓨, DifferentiableOn ℝ (fun x => phi x y) 𝓧)
  (hphi_diff_y : ∀ x ∈ 𝓧, DifferentiableOn ℝ (fun y => phi x y) 𝓨)
  (hphi_grad_x : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, DifferentiableAt ℝ (fun z => phi z y) x)
  (hphi_grad_y : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, DifferentiableAt ℝ (fun w => phi x w) y)
  (hsmooth_xx : ∀ x ∈ 𝓧, ∀ x' ∈ 𝓧, ∀ y ∈ 𝓨,
    ‖fderiv ℝ (fun z => phi z y) x - fderiv ℝ (fun z => phi z y) x'‖ ≤
    β₁₁ * ‖x - x'‖)
  (hsmooth_xy : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, ∀ y' ∈ 𝓨,
    ‖fderiv ℝ (fun z => phi z y) x - fderiv ℝ (fun z => phi z y') x‖ ≤
    β₁₂ * ‖y - y'‖)
  (hsmooth_yy : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, ∀ y' ∈ 𝓨,
    ‖fderiv ℝ (fun w => phi x w) y - fderiv ℝ (fun w => phi x w) y'‖ ≤
    β₂₂ * ‖y - y'‖)
  (hsmooth_yx : ∀ x ∈ 𝓧, ∀ x' ∈ 𝓧, ∀ y ∈ 𝓨,
    ‖fderiv ℝ (fun w => phi x w) y - fderiv ℝ (fun w => phi x' w) y‖ ≤
    β₂₁ * ‖x - x'‖) :
  sSup ((fun y => phi ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, u_seq (s + 1)) y) '' 𝓨) -
  sInf ((fun x => phi x ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, v_seq (s + 1))) '' 𝓧) ≤
  max (max (β₁₁ * Rx ^ 2) (β₂₂ * Ry ^ 2)) (max (β₁₂ * Rx * Ry) (β₂₁ * Rx * Ry)) *
  (4 / (t : ℝ)) := by
  sorry
