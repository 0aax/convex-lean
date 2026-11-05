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

def IsSubgradientOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : E)
  (w : E →L[ℝ] ℝ) : Prop :=
  ∀ y ∈ 𝓧, f x + w (y - x) ≤ f y

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

def IsSPMDSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
  (gx_seq : ℕ → E →L[ℝ] ℝ)
  (y_seq : ℕ → F)
  (gy_seq : ℕ → F →L[ℝ] ℝ) : Prop :=
  ((x_seq 0, y_seq 0) ∈ ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y)) ∧
   IsMinOn (fun z : E × F => a * phix z.1 + b * phiy z.2)
    ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))
    (x_seq 0, y_seq 0)) ∧
  (∀ t, IsSubgradientOn 𝓧 (fun x => phi x (y_seq t)) (x_seq t) (gx_seq t)) ∧
  (∀ t, IsSubgradientOn 𝓨 (fun y => -phi (x_seq t) y) (y_seq t) (gy_seq t)) ∧
  (∀ t, (x_seq t, y_seq t) ∈ ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))) ∧
  (∀ t,
   IsMinOn
    (fun z : E × F =>
      η * (gx_seq t z.1 + gy_seq t z.2) +
      prodBregmanDivergence
        (fun v => a * phix v)
        (fun v => b * phiy v)
        z
        (x_seq t, y_seq t))
    ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))
    (x_seq (t + 1), y_seq (t + 1)))

theorem saddle_point_mirror_descent_bound
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
  (gx_seq : ℕ → E →L[ℝ] ℝ)
  (y_seq : ℕ → F)
  (gy_seq : ℕ → F →L[ℝ] ℝ)
  (a b Rx Lx Ry Ly : ℝ)
  (hRx_sq : Rx ^ 2 = sSup {v | ∃ z ∈ 𝓧 ∩ 𝓓x, phix z - phix (x_seq 0) = v})
  (hRy_sq : Ry ^ 2 = sSup {v | ∃ z ∈ 𝓨 ∩ 𝓓y, phiy z - phiy (y_seq 0) = v})
  (ha_pos : a > 0) (hb_pos : b > 0)
  (hRx_pos : Rx > 0) (hRy_pos : Ry > 0)
  (hLx_pos : Lx > 0) (hLy_pos : Ly > 0)
  (ht : t ≥ 1)
  (hx_0 : x_seq 0 ∈ 𝓧 ∩ 𝓓x)
  (hy_0 : y_seq 0 ∈ 𝓨 ∩ 𝓓y)
  (h_spmd_seq :
    IsSPMDSequence 𝓧 𝓓x 𝓨 𝓓y phi phix phiy a b (Real.sqrt (2 / (t : ℝ)))
      x_seq gx_seq y_seq gy_seq)
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
  (hphix_diff : DifferentiableOn ℝ (fun v => a * phix v) 𝓓x)
  (hphix_mirror : IsMirrorMap 𝓓x (fun v => a * phix v))
  (hphix_strong : StrongConvexOn (𝓧 ∩ 𝓓x) 1 phix)
  (hphiy_diff : DifferentiableOn ℝ (fun v => b * phiy v) 𝓓y)
  (hphiy_mirror : IsMirrorMap 𝓓y (fun v => b * phiy v))
  (hphiy_strong : StrongConvexOn (𝓨 ∩ 𝓓y) 1 phiy)
  (hphi_convex_x : ∀ y ∈ 𝓨, ConvexOn ℝ 𝓧 (fun x => phi x y))
  (hphi_concave_y : ∀ x ∈ 𝓧, ConcaveOn ℝ 𝓨 (fun y => phi x y))
  (hgx_bound : ∀ s, ‖gx_seq s‖ ≤ Lx)
  (hgy_bound : ∀ s, ‖gy_seq s‖ ≤ Ly)
  (ha_val : a = Lx / Rx) (hb_val : b = Ly / Ry) :
  sSup ((fun y => phi ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x_seq s) y) '' 𝓨) -
  sInf ((fun x => phi x ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, y_seq s)) '' 𝓧) ≤
  (Rx * Lx + Ry * Ly) * Real.sqrt (2 / t) := by
  sorry
