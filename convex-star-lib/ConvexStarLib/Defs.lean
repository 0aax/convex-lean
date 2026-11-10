import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

def affineHyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (s : E) (t : ℝ) : Set E :=
  {x | inner ℝ s x = t}

def IsRegularSubgradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar v : E) : Prop :=
  (⊥ < f x_bar) ∧ (f x_bar < ⊤) ∧
  ∃ (r : E → ℝ),
    r =o[𝓝 x_bar] (fun x => ‖x - x_bar‖) ∧
    ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V,
      f x_bar + (((inner ℝ v (x - x_bar) + r x) : ℝ) : EReal) ≤ f x

def IsSubgradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar v : E) : Prop :=
  (⊥ < f x_bar) ∧ (f x_bar < ⊤) ∧
  ∃ (x : ℕ → E), ∃ (vseq : ℕ → E),
    Filter.Tendsto x Filter.atTop (𝓝 x_bar) ∧
    Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f x_bar)) ∧
    Filter.Tendsto vseq Filter.atTop (𝓝 v) ∧
    (∀ i, IsRegularSubgradientAt f (x i) (vseq i))

def subdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) (x_bar : E) : Set E :=
  {v | IsSubgradientAt f x_bar v}

def AlmostStrictConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (C : Set E), C ⊆ {x | (subdifferential f x).Nonempty} → Convex ℝ C →
    ∀ (x y : E), x ∈ C → y ∈ C → x ≠ y →
      ∀ (t : ℝ), 0 < t ∧ t < 1 →
        f (t • x + (1 - t) • y) < t * f x + (1 - t) * f y

def argmax {E : Type*}  (f : E → ℝ) (C : Set E)
  : Set E
  := {x : E | (x ∈ C) ∧ (∀ y ∈ C, f y ≤ f x)}

def asymptoticConeAt {E : Type*} [AddCommGroup E] [Module ℝ E]
  (C : Set E)
  (x : E) : Set E :=
  {d | ∀ (t : ℝ), t > 0 → x + t • d ∈ C}

def BlowsUpOnBoundary {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (F : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ frontier 𝓧, ∀ M : ℝ, ∀ᶠ y in 𝓝[interior 𝓧] x, M ≤ F y

noncomputable def hessianOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (x : E)
  : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x

noncomputable def localInnerProd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (x u v : E) : ℝ :=
  inner ℝ u (hessianOperator f x v)

noncomputable def localNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x v : E) : ℝ :=
  Real.sqrt (localInnerProd f x v v)

noncomputable def closedLocalBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (x v : E) (r : ℝ) : Set E :=
  {y : E | localNorm f x (y - v) ≤ r}

-- `𝔼[g | σ(x)]` for a dual-valued oracle output `g` (Bubeck §6.1: conditioning on the current
-- iterate).
noncomputable def condExpGivenIterate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω)
  (x : Ω → E)
  (g : Ω → E →L[ℝ] ℝ) : Ω → E →L[ℝ] ℝ :=
  MeasureTheory.condExp (MeasurableSpace.comap x inferInstance) μ g

def IsHorizonSubgradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar v : E) : Prop :=
  (⊥ < f x_bar) ∧ (f x_bar < ⊤) ∧
  ∃ (x : ℕ → E), ∃ (vseq : ℕ → E), ∃ (l : ℕ → ℝ),
    Filter.Tendsto x Filter.atTop (𝓝 x_bar) ∧
    Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f x_bar)) ∧
    Filter.Tendsto l Filter.atTop (𝓝[>] (0 : ℝ)) ∧
    Filter.Tendsto (fun n => l n • vseq n) Filter.atTop (𝓝 v) ∧
    (∀ n, IsRegularSubgradientAt f (x n) (vseq n))

def horizonSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) (x_bar : E) : Set E :=
  {v | IsHorizonSubgradientAt f x_bar v}

def IsRegularNormalAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar v : E) : Prop :=
  x_bar ∈ C ∧
  ∃ (r : E → ℝ),
    r =o[𝓝 x_bar] (fun x => ‖x - x_bar‖) ∧
    ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V, x ∈ C →
      inner ℝ v (x - x_bar) ≤ r x

def regularNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar : E) : Set E :=
  {v | IsRegularNormalAt C x_bar v}

def IsNormalAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar v : E) : Prop :=
  ∃ (x : ℕ → E), ∃ (vseq : ℕ → E),
    Filter.Tendsto x Filter.atTop (𝓝 x_bar) ∧
    Filter.Tendsto vseq Filter.atTop (𝓝 v) ∧
    (∀ n, vseq n ∈ regularNormalCone C (x n))

def normalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar : E) : Set E :=
  {v | IsNormalAt C x_bar v}

def ConstraintQualification {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) (C : Set E) (x_bar : E) : Prop :=
  ¬ ∃ v : E,
      v ∈ horizonSubdifferential f x_bar ∧
      v ≠ 0 ∧
      (-v) ∈ normalCone C x_bar

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

-- Convexity of an extended-real-valued function as convexity of its epigraph
-- (BC Definition 8.1; equivalent to the inequality form of FCA 1.1.3 / RW 2.1(b)
-- whenever f never takes -∞, which is BC 8.4 / FCA 1.1.6).
def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def setLiminf {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) : Set X :=
  {u | ∀ V ∈ 𝓝 u, ∀ᶠ n in Filter.atTop, ∃ v ∈ A n, v ∈ V}

def setLimsup {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) : Set X :=
  {u | ∀ V ∈ 𝓝 u, ∃ᶠ n in Filter.atTop, ∃ v ∈ A n, v ∈ V}

def corrSet (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  {A | A.IsPositive ∧
    ∀ i : Fin n, inner ℝ (A (EuclideanSpace.single i (1:ℝ))) (EuclideanSpace.single i (1:ℝ)) = 1}

def corrFV (n : ℕ) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  {A ∈ corrSet n | V ≤ LinearMap.ker A.toLinearMap}

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

noncomputable def delta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) (τ : ℝ) : E → EReal :=
  fun w => differenceQuotient f x w τ

-- FCA's Conv ℝⁿ for functions with values in ℝ ∪ {+∞}: never −∞ (added 2026-10-15, since the
-- corpus works in EReal), not identically +∞, and convex.
def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

-- FCA C.1.1.1: sublinear = in Conv ℝⁿ and positively homogeneous; FCA's two-coefficient
-- inequality (C.1.1.3) is a theorem about it.
def IsSublinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (σ : E → EReal) : Prop :=
  (InConvRn σ) ∧ IsERealPosHomogeneous σ

noncomputable def distOnFunctions {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (σ₁ : E → ℝ)
  (σ₂ : E → ℝ)
  (_ : IsSublinear (liftRealtoEReal σ₁))
  (_ : IsSublinear (liftRealtoEReal σ₂)) : ℝ :=
  sSup (Set.image
       (fun x => AbsoluteValue.abs (σ₁ x - σ₂ x))
       {x | ‖x‖ ≤ 1})

def dualCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) : Set E :=
  {s | ∀ x ∈ K, inner (𝕜 := ℝ) s x ≥ 0}

def epiLiminfSet {E : Type*} [NormedAddCommGroup E]
  (fseq : ℕ → E → EReal) : Set (E × ℝ) :=
  setLimsup (fun n => epigraph (fseq n))

def epiLimsupSet {E : Type*} [NormedAddCommGroup E]
  (fseq : ℕ → E → EReal) : Set (E × ℝ) :=
  setLiminf (fun n => epigraph (fseq n))

def EpiConverges {E : Type*} [NormedAddCommGroup E]
  (fseq : ℕ → E → EReal)
  (f : E → EReal) : Prop :=
  epiLiminfSet fseq = epigraph f ∧
  epiLimsupSet fseq = epigraph f

def exposedFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (C : Set E) (s : E) : Set E :=
  argmax (fun y => inner ℝ s y) C

def proximalMapping {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (lam : ℝ)
  (x : E) : Set E :=
  {w : E | f w < ⊤ ∧ ∀ z, f w + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 ≤ f z + (2 * lam)⁻¹ * ‖z - x‖ ^ 2}

noncomputable def istaSet {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (xt : EuclideanSpace ℝ (Fin n))
  (η : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  -- Bubeck's ISTA step is the proximal mapping (RW 1.22, `proximalMapping`) of g with
  -- parameter η at the gradient step; g is lifted to EReal.
  proximalMapping (fun x => ((g x : ℝ) : EReal)) η (xt - η • (gradient f xt))

noncomputable def fistaSet {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (β : ℝ)
  (xt : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  istaSet f g xt (1 / β)

noncomputable def ft {n : ℕ}
  (F : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : EuclideanSpace ℝ (Fin n))
  (a : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => a * inner ℝ c x + F x

def genCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (S : Set E) : Set E :=
  {v : E | ∃ (k : ℕ) (α : ℕ → ℝ) (x : ℕ → E),
   (∀ i ∈ Finset.range k, α i ≥ 0) ∧
   (∀ i ∈ Finset.range k, x i ∈ S) ∧
   (v = ∑ i ∈ Finset.range k, (α i) • (x i))}

def graph {E : Type*} (T : E → Set E) : Set (E × E) :=
  {p | p.2 ∈ T p.1}

def graphSetLiminf {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) : Set (E × E) :=
  setLiminf (fun n => graph (Tseq n))

def graphSetLimsup {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) : Set (E × E) :=
  setLimsup (fun n => graph (Tseq n))

def GraphicallyConverges {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) (T : E → Set E) : Prop :=
  graphSetLimsup Tseq = graph T ∧
  graphSetLiminf Tseq = graph T

def HasDirectionalDerivativeEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x w : E)
  (a : EReal) : Prop :=
  Filter.Tendsto
    (fun τ : ℝ => differenceQuotient f x w τ)
    (𝓝[>] (0 : ℝ))
    (𝓝 a)

def HasHadamardDirectionalDerivativeEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x w : E)
  (a : EReal) : Prop :=
  Filter.Tendsto
    (fun p : ℝ × E => differenceQuotient f x p.2 p.1)
    ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w)
    (𝓝 a)

def HasPosDefHessianOn {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ interior 𝓧, ∀ (h : EuclideanSpace ℝ (Fin n)), h ≠ 0 →
    0 < inner ℝ h ((hessianOperator f x) h)

lemma hessianOperator_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (Df : Set E)
  (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd (f := f) x v v)
  (x : E)
  (hx : x ∈ Df) : Function.Injective (hessianOperator f x) := by
  intro u v huv
  by_contra h
  have hne : u - v ≠ 0 := sub_ne_zero.mpr h
  have hpd := h_pd x hx (u - v) hne
  simp only [localInnerProd] at hpd
  have : hessianOperator f x (u - v) = 0 := by rw [map_sub, huv, sub_self]
  rw [this] at hpd
  simp at hpd

noncomputable def hessianLinearEquiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (x : E)
  (hx : x ∈ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) : E ≃L[ℝ] E := by
  have hinj := hessianOperator_injective f Df h_Df_pd x hx
  exact ContinuousLinearEquiv.ofBijective (hessianOperator f x)
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hinj))

def HessianSymmetricOn {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ S, ∀ u v,
    inner ℝ u ((hessianOperator f x) v) = inner ℝ v ((hessianOperator f x) u)

def hyperplaneHalfspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : E) (t : ℝ) : Set E :=
  {x | inner ℝ s x ≤ t}

def halfspacesContaining {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]  (C : Set E) : Set (E × ℝ)
    := {(s, r) : E × ℝ | C ⊆ hyperplaneHalfspace s r}

def idMap {E : Type*} (x : E) : Set E := {x}

def linearRange {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (A : F →ₗ[ℝ] E) : Set E
  := {z | ∃ y, A y = z}

noncomputable def lscHull {E : Type*} [TopologicalSpace E]
  (f : E → EReal)
  (x : E) : EReal
  := Filter.liminf f (𝓝 x)

-- FCA's Conv-bar ℝⁿ for functions with values in ℝ ∪ {+∞}: never −∞ (added 2026-10-15, since the
-- corpus works in EReal), convex, and closed (lower semicontinuous).
def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

def InDomIsSubgradientAt {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (w : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ 𝓧, f y ≥ f x + inner ℝ (y - x) w

def InSubspaceSpanVec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ)
  (x : ℕ → E)
  (x' : E) : Prop :=
  ∃ (z : ℕ → E),
  ∃ (s : ℕ → ℝ),
  (∀ i ∈ Finset.range m, ∃ j ∈ Finset.range m, z i = x j) ∧
  (x' = ∑ i ∈ Finset.range m, (s i) • (z i))

def IsAcuteCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ K, ∀ x' ∈ K, (0 : ℝ) ≤ inner ℝ x x'

def IsAlphaStronglyConvex {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (N : EuclideanSpace ℝ (Fin n) → ℝ)
  (α : ℝ) : Prop :=
  (∀ x ∈ 𝓧, ∃ g, InDomIsSubgradientAt 𝓧 f x g) ∧
  (∀ x ∈ 𝓧, ∀ y ∈ 𝓧, ∀ g, (InDomIsSubgradientAt 𝓧 f x g) →
    f x - f y ≤ inner ℝ g (x - y) - (α / 2) * (N (x - y))^2)

def IsAnalyticCenter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (Df : Set E)
  (x : E) : Prop :=
  x ∈ Df ∧ gradient f x = 0

noncomputable def dualNorm {n : ℕ}
  (N : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {v | ∃ x, (N x ≤ 1) ∧ (v = inner ℝ g x)}

def IsBetaSmoothOn {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (N : EuclideanSpace ℝ (Fin n) → ℝ)
  (β : ℝ) : Prop :=
  ∀ x ∈ 𝓧, ∀ y ∈ 𝓧, dualNorm N (gradient f x - gradient f y) ≤ β * (N (x - y))

def IsSubgradientOracle {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ z ∈ 𝓧, InDomIsSubgradientAt 𝓧 f z (G z)

def IsBlackBoxSpanProcedure {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (x 0 = 0) ∧
  (∀ s, x s ∈ 𝓧) ∧
  (∀ s, x (s + 1) ∈ Submodule.span ℝ ((fun j => G (x j)) '' Set.Iic s))

def IsCalmFromBelowAtWith {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) (x_bar : E) (κ : ℝ) : Prop :=
  0 ≤ κ ∧
  (⊥ < f x_bar) ∧ (f x_bar < ⊤) ∧
  ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V,
    f x_bar - κ * ‖x - x_bar‖ ≤ f x

def IsCalmFromBelowAt {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) (x_bar : E) : Prop :=
  ∃ (κ : ℝ), IsCalmFromBelowAtWith f x_bar κ

def IsMinimizerAtTforCoG {n : ℕ}
  (t : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  : Prop :=
  (∀ (i : ℕ), i ≤ t → f x ≤ f (c i)) ∧
  (∃ (i : ℕ), i ≤ t ∧ (c i) = x)

noncomputable def barycenter {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (K : Set E) : E :=
  (MeasureTheory.volume.real K)⁻¹ • ∫ x in K, x

noncomputable def centerOfGravityStep {n : ℕ}
  (S_prev : Set (EuclideanSpace ℝ (Fin n)))
  (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) × Set (EuclideanSpace ℝ (Fin n)) :=
  let c := barycenter S_prev
  (c, S_prev ∩ {x | inner ℝ (x - c) w ≤ 0})

def IsCenterOfGravitySequence {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (S : ℕ → Set (EuclideanSpace ℝ (Fin n)))
  (w : ℕ → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (c 0 = barycenter (S 0)) ∧
  (S 0 = 𝓧) ∧
  (∀ t, c (t + 1) = (centerOfGravityStep (S t) (w t)).1) ∧  -- CoG sequence
  (∀ t, S (t + 1) = (centerOfGravityStep (S t) (w t)).2) ∧
  (∀ t, InDomIsSubgradientAt 𝓧 f (c (t + 1)) (w t)) ∧
  (∀ t, IsMinimizerAtTforCoG t f c (x t))

noncomputable def finiteSumObjective {m n : ℕ}
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun z => (1 / (m : ℝ)) * ∑ i, f i z

def IsCenteredSAGIterates {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  let f_sum := finiteSumObjective f
  (∀ i ω, g 0 i ω = gradient (f i) (x 0 ω) - gradient f_sum (x 0 ω)) ∧
  (∀ t ω, g (t + 1) (I t ω) ω = gradient (f (I t ω)) (x t ω)) ∧
  (∀ t i ω, i ≠ I t ω → g (t + 1) i ω = g t i ω) ∧
  (∀ t ω, x (t + 1) ω = x t ω - η • ((1 / (m : ℝ)) • ∑ i, g (t + 1) i ω))

def IsCone {E : Type*} [AddCommMonoid E] [SMul ℝ E]
  (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ (s : ℝ), s > 0 → s • x ∈ K

def IsPointedCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Prop :=
  (0 : E) ∈ K ∧
  ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K

def IsConvexCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C,
  ∀ (α : ℝ), α ≥ 0 → ∀ (β : ℝ), β ≥ 0 → α • x + β • y ∈ C

def IsDifferentiableAtWithGradientEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → EReal)
  (x_bar grad : E) : Prop :=
  ∃ g : E → ℝ,
    (∃ U ∈ 𝓝 x_bar, ∀ x ∈ U, f x = (g x : EReal)) ∧
    DifferentiableAt ℝ g x_bar ∧
    gradient g x_bar = grad

def IsMinimizerAtTforEllipsoid {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (t : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  : Prop :=
  x ∈ 𝓧 ∧
  (∃ i : ℕ, i ≤ t ∧ c i = x) ∧
  (∀ i : ℕ, i ≤ t → c i ∈ 𝓧 → f x ≤ f (c i))

def IsSeparatingHyperplane {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (c w : EuclideanSpace ℝ (Fin n)) : Prop :=
  𝓧 ⊆ {x | inner ℝ (x - c) w ≤ 0}

noncomputable def innerRightLM {n : ℕ}
  (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
  { toFun    := fun v => inner ℝ w v
    map_add' := by
      intro x y
      simp [inner_add_right]
    map_smul' := by
      intro a x
      simp [inner_smul_right] }

noncomputable def updateHRank1 {n : ℕ}
  (w : EuclideanSpace ℝ (Fin n))
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  -- phi: v ↦ w^T (H v)
  let phi : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := (innerRightLM w).comp H
  -- define rank-1 update as v ↦ (w^T H v) • (H w)
  LinearMap.smulRight phi (H w)

noncomputable def ellipsoidAxesLinMap {n : ℕ}
  (w : EuclideanSpace ℝ (Fin n))
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  let a : ℝ := ((n : ℝ)^2) / (((n : ℝ)^2) - 1)
  let b : ℝ := (2 / ((n : ℝ) + 1)) / (inner ℝ w (H w))
  a • (H - b • updateHRank1 w H)

noncomputable def ellipsoidMethodStep {n : ℕ}
  (w c : EuclideanSpace ℝ (Fin n))
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
  let c_next := c - ((1 / ((n : ℝ) + 1)) *
    (1 / Real.sqrt (inner ℝ w (H w)))) • (H w)
  let H_next : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := ellipsoidAxesLinMap w H
  (c_next, H_next)

def IsEllipsoidMethodSequence {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n))
  (H : ℕ → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
  (w : ℕ → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (R : ℝ) : Prop :=
  (c 0 = 0) ∧
  (H 0 = (R ^ 2 • LinearMap.id)) ∧
  (∀ t, w t ≠ 0) ∧  -- assume analysis is up until algorithm terminates
  (∀ t, c (t + 1) = (ellipsoidMethodStep (w t) (c t) (H t)).1) ∧  -- Ellipsoid method sequence
  (∀ t, H (t + 1) = (ellipsoidMethodStep (w t) (c t) (H t)).2) ∧
  (∀ t,
    (c t ∈ 𝓧 ∧ InDomIsSubgradientAt 𝓧 f (c t) (w t)) ∨
    (c t ∉ 𝓧 ∧ IsSeparatingHyperplane 𝓧 (c t) (w t))) ∧
  (∀ t, IsMinimizerAtTforEllipsoid 𝓧 t f c (x t))

def IsEpiLimsup {E : Type*} [NormedAddCommGroup E]
  {ι : Type*}
  (F : ι → E → EReal) (l : Filter ι) (g : E → EReal) : Prop :=
  epigraph g = {p | ∀ W ∈ 𝓝 p, ∀ᶠ i in l, ∃ q ∈ epigraph (F i), q ∈ W}

def IsSupportingHyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (s : E) (t : ℝ)
  (C : Set E) : Prop :=
  C ⊆ hyperplaneHalfspace s t

def IsExposedFaceOf {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C F : Set X) : Prop :=
  ∃ (phi : X →L[ℝ] ℝ),
    F = {x ∈ C | ∀ y ∈ C, phi y ≤ phi x}

def IsFISTASequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (y : ℕ → EuclideanSpace ℝ (Fin n))
  (lambda : ℕ → ℝ)
  (β : ℝ) : Prop :=
  let γ := fun t => (1 - lambda t) / (lambda (t + 1))
  (lambda 0 = 0) ∧
  (x 0 = y 0) ∧
  (∀ t, lambda (t + 1) = (1 + Real.sqrt (1 + 4 * (lambda t)^2)) / 2) ∧
  (∀ t, y (t + 1) ∈ fistaSet f g β (x t)) ∧
  (∀ t, x (t + 1) = (1 - γ t) • y (t + 1) + (γ t) • y t)

def IsFaceOf {E : Type*} [AddCommGroup E] [Module ℝ E]
  (F K : Set E) : Prop :=
  Convex ℝ F ∧ F.Nonempty ∧ IsExtreme ℝ K F

def IsFiniteEReal (a : EReal) : Prop :=
  ∃ r : ℝ, a = (r : EReal)

def IsFiniteAround {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (x_bar : E) : Prop :=
  ∃ U ∈ 𝓝 x_bar, ∀ x ∈ U, IsFiniteEReal (f x)

def IsFiniteOn {E : Type*}
  (f : E → EReal)
  (O : Set E) : Prop :=
  ∀ x ∈ O, IsFiniteEReal (f x)

noncomputable def frankWolfeStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : E)
  (y : E)
  (γ : ℝ) : E :=
  (1 - γ) • x + γ • y

-- Conditional gradient descent / Frank–Wolfe (Bubeck §3.3): `y_t ∈ argmin_{y ∈ 𝓧} ∇f(x_t)ᵀy`,
-- `x_{t+1} = (1 − γ_t) x_t + γ_t y_t`; the gradient is the derivative `fderiv ℝ f (x t)` as a
-- functional.
def IsFrankWolfeSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (γ : ℕ → ℝ) : Prop :=
  (∀ t, x t ∈ 𝓧) ∧
  (∀ t, y t ∈ 𝓧) ∧
  (∀ t, 0 ≤ γ t ∧ γ t ≤ 1) ∧
  (∀ t, x (t + 1) = frankWolfeStep (x t) (y t) (γ t)) ∧
  (∀ x' ∈ 𝓧, DifferentiableAt ℝ f x') ∧
  (∀ t, IsMinOn (fun z => fderiv ℝ f (x t) z) 𝓧 (y t))

def IsGloballyOptimal {E : Type*}
  (f : E → EReal)
  (C : Set E) (x_bar : E) : Prop :=
  f x_bar < ⊤ ∧
  ∀ x ∈ C, f x_bar ≤ f x

noncomputable def gradientDescentStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (η : ℝ) : EuclideanSpace ℝ (Fin n) :=
  x - η • (gradient f x)

def IsGradientDescentSequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (η : ℝ) : Prop :=
  (∀ t, x (t + 1) = gradientDescentStep f (x t) η)

def IsISTASequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (η : ℝ) : Prop :=
  (∀ t, x (t + 1) ∈ istaSet f g (x t) η)

def IsJointlyLogConcave {n m : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  (∀ x y, 0 ≤ f x y) ∧
  ∀ x₁ x₂ y₁ y₂ t, t ∈ Set.Icc 0 1 →
    f (t • x₁ + (1 - t) • x₂) (t • y₁ + (1 - t) • y₂) ≥
      Real.rpow (f x₁ y₁) t * Real.rpow (f x₂ y₂) (1 - t)

def IsLLipschitz {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (N : EuclideanSpace ℝ (Fin n) → ℝ)
  (L : ℝ) : Prop :=
  ∀ x ∈ 𝓧, ∀ g, InDomIsSubgradientAt 𝓧 f x g → dualNorm N g ≤ L

def sublevelSet {E : Type*}
  (r : ℝ) (f : E → EReal) :
  Set E :=
  {x : E | f x ≤ r}

def IsLevelBounded {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ α : ℝ, Bornology.IsBounded (sublevelSet α f)

def IsLinearOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (𝓧 : Set E)
  (σ : E → EReal) : Prop :=
  (∀ (x₁ x₂ : E), ∀ (t₁ t₂ : ℝ),
  x₁ ∈ 𝓧 → x₂ ∈ 𝓧 → t₁ • x₁ + t₂ • x₂ ∈ 𝓧 →
  (σ (t₁ • x₁ + t₂ • x₂)) = t₁ * (σ x₁) + t₂ * (σ x₂))

def IsLipschitzEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (A : Set X)
  (β : ℝ) : Prop :=
  (0 ≤ β) ∧
  (∀ x ∈ A, T x ≠ ⊤ ∧ T x ≠ ⊥) ∧
  (∀ (x y : X),
    x ∈ A → y ∈ A →
      ‖(T x).toReal - (T y).toReal‖ ≤ β • (dist x y))

def IsLipschitzHess {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (L : ℝ) : Prop :=
  ∀ x y, (hessianOperator f x - hessianOperator f y).opNorm ≤ L * ‖x - y‖

def IsLocallyBoundedAboveAtEReal {E : Type*} [NormedAddCommGroup E]
  (g : E → EReal)
  (x_bar : E) : Prop :=
  ∃ U ∈ 𝓝 x_bar, ∃ M : ℝ, ∀ x ∈ U, g x ≤ (M : EReal)

def IsLocallyBoundedAt {E : Type*} [NormedAddCommGroup E]
  (T : E → Set E)
  (x_bar : E) : Prop :=
  ∃ U ∈ 𝓝 x_bar, ∃ R > (0 : ℝ),
    ∀ x ∈ U, ∀ v ∈ T x, ‖v‖ ≤ R

def IsLocallyLipschitzNearEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (x : X) : Prop :=
  ∃ (ρ : ℝ),
    (0 < ρ) ∧
    (∃ (β : ℝ), IsLipschitzEReal T (Metric.ball x ρ) β)

def IsLocallyLipschitzOnEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (C : Set X) : Prop :=
  ∀ x ∈ C, IsLocallyLipschitzNearEReal T x

def IsLocallyOptimal {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (C : Set E) (x_bar : E) : Prop :=
  f x_bar < ⊤ ∧
  ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V ∩ C,
    f x_bar ≤ f x

def IsLogConcave {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  ∀ (x y : EuclideanSpace ℝ (Fin n)), ∀ (t : ℝ), t ∈ Set.Icc 0 1 →
    f (t • x + (1 - t) • y) ≥ (Real.rpow (f x)  t) * (Real.rpow (f y) (1 - t))

def IsLogConcaveMeasure {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ (A B : Set (EuclideanSpace ℝ (Fin n))),
  ∀ c : ℝ,
    IsCompact A → IsCompact B → 0 < c → c < 1 →
    μ (c • A + (1 - c) • B) ≥ ENNReal.rpow (μ A) c * ENNReal.rpow (μ B) (1 - c)

def IsLogarithmicallyHomogeneousWith {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (v : ℝ) : Prop :=
  ∃ (K : Set E), (Df = interior K) ∧ (IsCone K) ∧
    (∀ x ∈ interior K, ∀ t > 0,
      f (t • x) = f x - v * (Real.log t))

noncomputable def localBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (x v : E) (r : ℝ) : Set E :=
  {y : E | localNorm f x (y - v) < r}

def IsSelfConcordantLocalNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (Df : Set E)
  : Prop :=
  ∀ x ∈ Df,
    (localBall (f := f) x x 1 ⊆ Df) ∧
    (∀ y, y ∈ localBall (f := f) x x 1 →
      (∀ v ≠ 0,
        (1 : ℝ) - (localNorm (f := f) x (y - x)) ≤
          (localNorm (f := f) x v)⁻¹ * (localNorm (f := f) y v) ∧
        (localNorm (f := f) x v)⁻¹ * (localNorm (f := f) y v) ≤
          (1 - (localNorm (f := f) x (y - x)))⁻¹))

noncomputable def localGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x y : E)
  (hx : x ∈ Df) : E :=
  (hessianLinearEquiv (f := f) (Df := Df) (h_Df_pd := h_Df_pd) x hx).symm (gradient f y)

noncomputable def barrierIntegrand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E) (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x : Df) : ℝ :=
  (localNorm f x.1
    (localGradient f Df h_Df_pd x.1 x.1 x.2)) ^ 2

def IsSCBarrier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) : Prop :=
  IsSelfConcordantLocalNorm f Df ∧
  BddAbove (Set.range fun x : Df =>
    barrierIntegrand (f := f) (Df := Df) h_Df_pd x)

noncomputable def barrierParameter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) : ℝ :=
  sSup ((Set.range fun x : Df =>
    barrierIntegrand f Df h_Df_pd x))

def IsLogarithmicallyHomogeneousBarrier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) : Prop :=
  IsSCBarrier f Df h_Df_pd ∧
  IsLogarithmicallyHomogeneousWith (f := f) (Df := Df) (barrierParameter f Df h_Df_pd)

def IsMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

def IsMaximalMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  IsMonotone T ∧
  ∀ (x_hat v_hat : E),
    v_hat ∉ T x_hat →
    ∃ (x_tilde v_tilde : E),
      v_tilde ∈ T x_tilde ∧
      inner ℝ (v_hat - v_tilde) (x_hat - x_tilde) < 0

def projectionMapping {E : Type*} [NormedAddCommGroup E] (C : Set E) (x : E) : Set E :=
  {w : E | w ∈ C ∧ ∀ z ∈ C, ‖w - x‖ ≤ ‖z - x‖}

-- Mini-batch SGD (Bubeck §6.2): `x₁ ∈ argmin_X ½‖·‖²` and
-- `x_{t+1} = Π_X (x_t − (η/m) ∑ᵢ g̃ᵢ(x_t))`. The oracle assumptions are hypotheses of the theorem.
def IsMinibatchStochasticGradientDescentSequence {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (m : ℕ)
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (x : ℕ → (Ω → EuclideanSpace ℝ (Fin n)))
  (g : ℕ → Fin m → (Ω → EuclideanSpace ℝ (Fin n)))
  (η : ℝ) : Prop :=
  (∀ t, Measurable (x t)) ∧
  (∀ ω, x 0 ω ∈ 𝓧) ∧
  (∀ ω, IsMinOn (fun v => 1/2 * ‖v‖ ^ 2) 𝓧 (x 0 ω)) ∧
  (∀ t ω, x (t + 1) ω ∈ projectionMapping 𝓧
                    ((x t ω) - (η / (m : ℝ)) • ∑ i, (g t i ω)))

-- Bubeck, Chapters 3–6, in a real normed space `E` whose own norm is the book's "arbitrary
-- norm": gradients are functionals `E →L[ℝ] ℝ`, Bubeck's `gᵀx` is the evaluation `g x`, and the
-- dual norm `‖g‖∗ = sup_{‖x‖ ≤ 1} g x` is the operator norm `‖g‖` on `E →L[ℝ] ℝ`.

-- Bregman divergence `D_f(x, y) = f x − f y − ⟨∇f(y), x − y⟩` (Bubeck §4.1).
noncomputable def bregmanDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ)
  (x : E)
  (y : E) : ℝ :=
  (f x) - (f y) - (fderiv ℝ f y (x - y))

-- Subgradient of `f` at `x` relative to `𝓧` (Bubeck Definition 1.2): the subgradient inequality
-- is only required against points of `𝓧`.
def IsSubgradientOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : E)
  (w : E →L[ℝ] ℝ) : Prop :=
  ∀ y ∈ 𝓧, f x + w (y - x) ≤ f y

-- The Bregman projections `argmin_{x ∈ 𝓧 ∩ 𝓓} D_phi(x, y)` of `y` (Bubeck §4.1).
def bregmanDivergenceProjSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (phi : E → ℝ)
  (y : E) : Set E :=
  {x : E |
  (x ∈ 𝓧 ∩ 𝓓) ∧
  (∀ z ∈ 𝓧 ∩ 𝓓, bregmanDivergence phi x y ≤ bregmanDivergence phi z y)}

-- `β`-smooth on `𝓧` w.r.t. the norm of `E` (Bubeck, Chapter 4 convention (ii)):
-- `‖∇f(x) − ∇f(y)‖∗ ≤ β‖x − y‖` for `x, y ∈ 𝓧`.
def IsSmoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (f : E → ℝ)
  (β : ℝ) : Prop :=
  ∀ x ∈ 𝓧, ∀ y ∈ 𝓧, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ β * ‖x - y‖

-- Mirror descent (Bubeck §4.1, (4.1)–(4.2)): `x₁ ∈ argmin_{𝓧 ∩ 𝓓} Φ`, dual step
-- `∇Φ(y_{t+1}) = ∇Φ(x_t) − η g_t` with `g_t ∈ ∂f(x_t)`, then the Bregman projection
-- `x_{t+1} = Π^Φ_{𝓧 ∩ 𝓓}(y_{t+1})`. Indices are shifted by one: `x 0` is the book's `x₁`.
def IsMirrorDescentSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (g : ℕ → E →L[ℝ] ℝ)
  (η : ℝ) : Prop :=
  (IsMinOn phi (𝓧 ∩ 𝓓) (x 0)) ∧
  (∀ t, x (t + 1) ∈ bregmanDivergenceProjSet 𝓧 𝓓 phi (y (t + 1))) ∧
  (∀ t, (y t) ∈ 𝓓) ∧
  (∀ t, fderiv ℝ phi (y (t + 1)) = fderiv ℝ phi (x t) - η • (g t)) ∧
  (∀ t, IsSubgradientOn 𝓧 f (x t) (g t))

-- Lazy mirror descent / Nesterov's dual averaging (Bubeck §4.4): `∇Φ(y₁) = 0`,
-- `∇Φ(y_{t+1}) = ∇Φ(y_t) − η g_t` with `g_t ∈ ∂f(x_t)`, and `x_{t+1} = Π^Φ_{𝓧 ∩ 𝓓}(y_{t+1})`,
-- equivalently `x_{t+1} = argmin_{𝓧 ∩ 𝓓} η ∑_{s ≤ t} g_sᵀx + Φ(x)`.
def IsDualAveragingSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (g : ℕ → E →L[ℝ] ℝ)
  (η : ℝ) : Prop :=
  let dual_avg_iter := fun (t : ℕ) (z : E) =>
                       η * (∑ s ∈ Finset.range t, g s z) + phi z
  (IsMinOn phi (𝓧 ∩ 𝓓) (x 0)) ∧
  (fderiv ℝ phi (y 0) = 0) ∧
  (∀ t, IsMinOn (dual_avg_iter t) (𝓧 ∩ 𝓓) (x t)) ∧
  (∀ t, x t ∈ 𝓧 ∩ 𝓓) ∧
  (∀ t, (y t) ∈ 𝓓) ∧
  (∀ t, fderiv ℝ phi (y (t + 1)) = fderiv ℝ phi (y t) - η • (g t)) ∧
  (∀ t, IsSubgradientOn 𝓧 f (x t) (g t))

-- Mirror map on an open convex `𝓓` (Bubeck Definition 4.1 (i)–(iii)): strictly convex and
-- differentiable on `𝓓`, `∇phi(𝓓)` is the whole dual, and `‖∇phi‖∗ → ∞` at the boundary of `𝓓`.
def IsMirrorMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓓 : Set E)
  (phi : E → ℝ) : Prop :=
  (StrictConvexOn ℝ 𝓓 phi) ∧
  (DifferentiableOn ℝ phi 𝓓) ∧
  (∀ (ℓ : E →L[ℝ] ℝ), ∃ y ∈ 𝓓, fderiv ℝ phi y = ℓ) ∧
  (∀ b ∈ frontier 𝓓, Filter.Tendsto (fun x => ‖fderiv ℝ phi x‖) (𝓝[𝓓] b) Filter.atTop)

-- Mirror prox (Bubeck §4.5): `x₁ ∈ argmin_{𝓧 ∩ 𝓓} Φ`, then
-- `∇Φ(y'_{t+1}) = ∇Φ(x_t) − η∇f(x_t)`, `y_{t+1} = Π(y'_{t+1})`,
-- `∇Φ(x'_{t+1}) = ∇Φ(x_t) − η∇f(y_{t+1})`, `x_{t+1} = Π(x'_{t+1})`.
def IsMirrorProxSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (x_prime : ℕ → E)
  (y_prime : ℕ → E)
  (η : ℝ) : Prop :=
  (IsMinOn phi (𝓧 ∩ 𝓓) (x 0)) ∧
  (∀ t, x (t + 1) ∈ bregmanDivergenceProjSet 𝓧 𝓓 phi (x_prime (t + 1))) ∧
  (∀ t, y (t + 1) ∈ bregmanDivergenceProjSet 𝓧 𝓓 phi (y_prime (t + 1))) ∧
  (∀ t, (y_prime t) ∈ 𝓓) ∧ (∀ t, (x_prime t) ∈ 𝓓) ∧
  (∀ t, fderiv ℝ phi (y_prime (t + 1)) = fderiv ℝ phi (x t) - η • (fderiv ℝ f (x t))) ∧
  (∀ t, fderiv ℝ phi (x_prime (t + 1)) = fderiv ℝ phi (x t) - η • (fderiv ℝ f (y (t + 1))))

noncomputable def nesterovStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))
  (α β : ℝ) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let κ := β / α
  let κ_term := (Real.sqrt κ - 1) / (Real.sqrt κ + 1)
  let y_next := x - (1 / β) • (gradient f x)
  let x_next := (1 + κ_term) • y_next - κ_term • y
  (y_next, x_next)

def IsNesterovSequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (y : ℕ → EuclideanSpace ℝ (Fin n))
  (α β : ℝ) : Prop :=
  (∀ t, y (t + 1) = (nesterovStep f (x t) (y t) α β).1) ∧
  (∀ t, x (t + 1) = (nesterovStep f (x t) (y t) α β).2)

noncomputable def nesterovStepAlphaZero {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (y : EuclideanSpace ℝ (Fin n))
  (β lambda : ℝ) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let lambda_next := (1 + (Real.sqrt (1 + 4 * lambda^2))) / 2
  let γ := (1 - lambda) / lambda_next
  let y_next := x - (1 / β) • (gradient f x)
  let x_next := (1 - γ) • y_next + γ • y
  (y_next, x_next)

def IsNesterovSequenceAlphaZero {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (y : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ)
  (lambda : ℕ → ℝ) : Prop :=
  (∀ t, y (t + 1) = (nesterovStepAlphaZero f (x t) (y t) β (lambda t)).1) ∧
  (∀ t, x (t + 1) = (nesterovStepAlphaZero f (x t) (y t) β (lambda t)).2) ∧
  (lambda 0 = 0) ∧
  (∀ t, lambda (t + 1) = (1 + (Real.sqrt (1 + 4 * (lambda t)^2))) / 2)

noncomputable def newtonStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (hessianOperator f x).inverse (gradient f x)

def IsNewtonsMethodSequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ t, x (t + 1) = newtonStep f (x t))

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

def IsNonexpansive {E : Type*} [NormedAddCommGroup E]
  (S : E → Set E) : Prop :=
  ∀ (z₀ z₁ w₀ w₁ : E), w₀ ∈ S z₀ → w₁ ∈ S z₁ →
    ‖w₁ - w₀‖ ≤ ‖z₁ - z₀‖

def IsNormalToProd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set (E × ℝ)) (x : E × ℝ) (s : E × ℝ) : Prop :=
  ∀ y ∈ C, inner ℝ s.1 (y.1 - x.1) + s.2 * (y.2 - x.2) ≤ 0

noncomputable def jerkOperator {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
  : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  fderiv ℝ (fun y => hessianOperator f y) x

def IsSelfConcordant {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (M : ℝ) : Prop :=
  ConvexOn ℝ (interior 𝓧) f ∧
  ContDiffOn ℝ 3 f (interior 𝓧) ∧
  (∀ x ∈ interior 𝓧, ∀ h,
    |inner ℝ h (jerkOperator f x h h)| ≤ M * (localNorm f x h)^3) ∧
  (∀ y ∈ interior 𝓧, ∀ v ≠ 0,
    0 < inner ℝ v ((hessianOperator f y) v))

def IsNuSelfConcordantBarrier {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) : Prop :=
  1 ≤ ν ∧
  IsSelfConcordant 𝓧 F 2 ∧
  ConcaveOn ℝ (interior 𝓧) (fun x => Real.exp ((-1 / ν) * (F x))) ∧
  BlowsUpOnBoundary 𝓧 F

noncomputable def IsOneCoerciveFun {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ C : ℝ, ∀ᶠ x in Filter.comap norm Filter.atTop, (C : EReal) ≤ (norm x)⁻¹ * (f x)

def IsOuterSemicontinuousOn {E : Type*} [NormedAddCommGroup E]
  (T : E → Set E)
  (O : Set E) : Prop :=
  ∀ x ∈ O,
    ∀ (xseq vseq : ℕ → E) (v : E),
      (∀ n, xseq n ∈ O) →
      Filter.Tendsto xseq Filter.atTop (𝓝 x) →
      (∀ n, vseq n ∈ T (xseq n)) →
      Filter.Tendsto vseq Filter.atTop (𝓝 v) →
        v ∈ T x

noncomputable def Set.affineFinrank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (S : Set E) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ S).direction

structure Polytope (E : Type*)
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] where
  m : ℕ
  a : Fin m → E
  b : Fin m → ℝ

def Polytope.carrier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set E :=
  {x : E | ∀ i, inner ℝ (P.a i) x ≤ P.b i}

def Polytope.IsFullDimensional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Prop :=
  affineSpan ℝ P.carrier = ⊤

def Polytope.faces {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set (Set E) :=
  {F : Set E | IsFaceOf F P.carrier}

def Polytope.facets {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set (Set E) :=
  {F : Set E |
    F ∈ P.faces ∧
    Set.affineFinrank F + 1 = Set.affineFinrank P.carrier}

def IsPolyhedral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Prop :=
  ∃ P : Polytope E, P.carrier = C

def IsPiecewiseLinearOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (D : Set E) (G : E → F) : Prop :=
  ∃ (n : ℕ),
    ∃ (P : Fin n → Set E),
    ∃ (A : Fin n → E →L[ℝ] F),
    ∃ (a : Fin n → F),
      (D = ⋃ i : Fin n, P i) ∧
      (∀ i : Fin n, IsPolyhedral (P i)) ∧
      (∀ i : Fin n, ∀ x ∈ P i, G x = A i x + a i)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsPiecewiseLinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∃ (g : E → ℝ),
    IsPiecewiseLinearOn (effDom f) g ∧
    ∀ x ∈ effDom f, f x = (g x : EReal)

def IsPiecewiseLinearQuadratic {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∃ (n : ℕ),
    ∃ (P : Fin n → Set E),
    ∃ (A : Fin n → E →L[ℝ] E),
    ∃ (a : Fin n → E),
    ∃ (α : Fin n → ℝ),
      effDom f = ⋃ i : Fin n, P i ∧
      (∀ i : Fin n, IsPolyhedral (P i)) ∧
      (∀ i : Fin n, P i ⊆ effDom f) ∧
      (∀ i : Fin n, ∀ x ∈ P i,
        f x =
          (((1 / 2 : ℝ) * inner ℝ x (A i x) +
              inner ℝ (a i) x +
              α i) : EReal))

noncomputable def pC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) (C : Set E)
    (hC₁ : IsClosed C) (hC₂ : Convex ℝ C) (hC₃ : Set.Nonempty C) : E
    := Classical.choose (exists_norm_eq_iInf_of_complete_convex hC₃ hC₁.isComplete hC₂ x)

noncomputable def projSubgradientStep {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (g : EuclideanSpace ℝ (Fin n))
  (η : ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : EuclideanSpace ℝ (Fin n) :=
  let y_next := x - η • g
  pC y_next 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty

noncomputable def projGradientDescentStep {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  (η : ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : EuclideanSpace ℝ (Fin n) :=
  projSubgradientStep 𝓧 x (g x) η h𝓧_nonempty h𝓧_compact h𝓧_convex

def IsProjectedGradientDescentSequence {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (η : ℕ → ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : Prop :=
  (∀ x' ∈ 𝓧, HasGradientAt f (g x') x') ∧
  (∀ t, x (t + 1) = projGradientDescentStep 𝓧 g (x t) (η t) h𝓧_nonempty h𝓧_compact h𝓧_convex)

def IsProjectedSubgradientSequence {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (g : ℕ → EuclideanSpace ℝ (Fin n))
  (η : ℕ → ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : Prop :=
  (∀ t, x (t + 1) = projSubgradientStep 𝓧 (x t) (g t) (η t) h𝓧_nonempty h𝓧_compact h𝓧_convex) ∧
  (∀ t, InDomIsSubgradientAt 𝓧 f (x t) (g t))

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

def IsProperLSCConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) : Prop :=
  (IsProper f) ∧ (LowerSemicontinuous f) ∧ (ConvexEReal f)

def IsQuasiConvex {n : ℕ}
  (L : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ (x y : EuclideanSpace ℝ (Fin n)), ∀ (t : ℝ), t ∈ Set.Icc 0 1 →
    L (t • x + (1 - t) • y) ≤ max (L x) (L y)

noncomputable def randomizedCoordDescentStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (I : Fin n)
  (η : ℝ) : EuclideanSpace ℝ (Fin n) :=
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single I (1 : ℝ)
  let g : ℝ := (fderiv ℝ f x) e
  let upd : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single I (η * g)
  x - upd

def IsRandomizedCoordDescentGammaSequence {n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (β : Fin n → ℝ)
  (γ : ℝ) : Prop :=
  (∀ s, Measurable (x s)) ∧
  (∀ s, Measurable (I s)) ∧
  (∀ s ω, x (s + 1) ω = randomizedCoordDescentStep f (x s ω) (I s ω) ((β (I s ω))⁻¹)) ∧
  (ProbabilityTheory.iIndepFun (fun (p : ℕ) => I p) μ) ∧
  (∀ s (i : Fin n), μ ((I s) ⁻¹' {i}) =
    ENNReal.ofReal ((Real.rpow (β i) γ) / ∑ j, (Real.rpow (β j) γ)))

def IsRandomizedCoordDescentSequence {n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (η : ℝ) : Prop :=
  (∀ s, Measurable (x s)) ∧
  (∀ s, Measurable (I s)) ∧
  (∀ s ω, x (s + 1) ω = randomizedCoordDescentStep f (x s ω) (I s ω) η) ∧
  (ProbabilityTheory.iIndepFun (fun (p : ℕ) => I p) μ) ∧
  (∀ s i, μ ((I s) ⁻¹' {i}) = (n : ENNReal)⁻¹)

def LocalLscAt {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (x_bar : E) : Prop :=
  (⊥ < f x_bar) ∧ (f x_bar < ⊤) ∧
  (∃ (ε : ℝ), ∀ (α : ℝ), α ≤ f x_bar + ε →
    ((ε > 0) ∧
    IsClosed {x | (x ∈ Metric.closedBall x_bar ε) ∧ f x ≤ α}))

def fApproach {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (x_bar : E) : Filter E :=
  𝓝 x_bar ⊓ Filter.comap f (𝓝 (f x_bar))

noncomputable def regularSubderivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar w_bar : E) : EReal :=
  Filter.limsup
    (fun (δ : ℝ) =>
      Filter.limsup
        (fun p : E × ℝ =>
          sInf ((delta f p.1 p.2) '' Metric.closedBall w_bar δ))
        ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))))
    (𝓝[>] (0 : ℝ))

noncomputable def subderivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar w_bar : E) : EReal :=
  Filter.liminf
    (fun p : ℝ × E => differenceQuotient f x_bar p.2 p.1)
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w_bar)

def IsRegularAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar : E) : Prop :=
  (⊥ < f x_bar ∧ f x_bar < ⊤) ∧
  LocalLscAt f x_bar ∧
  ∀ w, subderivative f x_bar w = regularSubderivative f x_bar w

def IsRegularSetAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (C : Set E) (x_bar : E) : Prop :=
  regularNormalCone C x_bar = normalCone C x_bar

-- SAGA for the composite objective `F = f + h` (Defazio, Bach & Lacoste-Julien 2014, §2,
-- equations (1)–(3)): a table `g t i` holding the most recent gradient of each `f i`; the step
-- `w = x t − η (g_{t+1,j} − g_{t,j} + (1/m) ∑ᵢ g_{t,i})` with `j = I t` the sampled index; and the
-- proximal step `x (t+1) = prox_h^η (w) = argmin_z h z + ‖z − w‖² / (2η)`. With `h = 0` the
-- proximal step is `x (t+1) = w`, the smooth SAGA of Tibshirani's slides.
def IsSAGAIterates {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (h : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  (∀ i ω, g 0 i ω = gradient (f i) (x 0 ω)) ∧
  (∀ t ω, g (t + 1) (I t ω) ω = gradient (f (I t ω)) (x t ω)) ∧
  (∀ t i ω, i ≠ I t ω → g (t + 1) i ω = g t i ω) ∧
  (∀ t ω,
    let w := x t ω - η • (g (t + 1) (I t ω) ω - g t (I t ω) ω + ((1 / (m : ℝ)) • ∑ i, g t i ω))
    x (t + 1) ω ∈ proximalMapping (liftRealtoEReal h) η w)

def IsSAGASequence {m n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (h : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  (∀ t, Measurable (x t)) ∧
  (∀ t i, Measurable (g t i)) ∧
  (∀ t, Measurable (I t)) ∧
  IsSAGAIterates f h x g I η ∧
  ProbabilityTheory.iIndepFun I μ ∧
  (∀ t, ProbabilityTheory.IndepFun
    (I t)
    (fun ω => (x t ω, fun i => g t i ω)) μ) ∧
  (∀ t i, μ ((I t) ⁻¹' {i}) = (m : ENNReal)⁻¹)

def IsSAGSequence {m n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  (∀ t, Measurable (x t)) ∧
  (∀ t i, Measurable (g t i)) ∧
  (∀ t, Measurable (I t)) ∧
  IsCenteredSAGIterates f x g I η ∧
  ProbabilityTheory.iIndepFun I μ ∧
  (∀ t, ProbabilityTheory.IndepFun (I t) (fun ω => (x t ω, fun i => g t i ω)) μ) ∧
  (∀ t i, μ ((I t) ⁻¹' {i}) = (m : ENNReal)⁻¹)

-- Bregman divergence of `Φ(z) = Φ_𝓧(x) + Φ_𝓨(y)` on the product space (Bubeck §5.2).
noncomputable def prodBregmanDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (phix : E → ℝ)
  (phiy : F → ℝ)
  (z z' : E × F) : ℝ :=
  bregmanDivergence phix z.1 z'.1 +
  bregmanDivergence phiy z.2 z'.2

-- Saddle-point mirror descent, SP-MD (Bubeck §5.2.2), on `Z = 𝓧 × 𝓨` with the mirror map
-- `Φ(z) = a Φ_𝓧(x) + b Φ_𝓨(y)`: `z₁ ∈ argmin_{Z ∩ D} Φ` and
-- `z_{t+1} = argmin_{z ∈ Z ∩ D} η g_tᵀz + D_Φ(z, z_t)`, `g_t = (g_{𝓧,t}, g_{𝓨,t})` with
-- `g_{𝓧,t} ∈ ∂_x ϕ(x_t, y_t)`, `g_{𝓨,t} ∈ ∂_y(−ϕ(x_t, y_t))`.
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
  -- initial point is in the domain and is argmin of phi on 𝓩 ∩ 𝓓
  ((x_seq 0, y_seq 0) ∈ ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y)) ∧
   IsMinOn (fun z : E × F => a * phix z.1 + b * phiy z.2)
    ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))
    (x_seq 0, y_seq 0)) ∧
  -- g_{𝓧, t} ∈ ∂_x phi(x_t, y_t)
  (∀ t, IsSubgradientOn 𝓧 (fun x => phi x (y_seq t)) (x_seq t) (gx_seq t)) ∧
  -- g_{𝓨, t} ∈ ∂_y -phi(x_t, y_t)
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

-- Saddle-point mirror prox, SP-MP (Bubeck §5.2.3), main iterates `z_t = (x_t, y_t)` and prox
-- iterates `w_t = (u_t, v_t)`: `z₁ ∈ argmin_{Z ∩ D} Φ`,
-- `w_{t+1} = argmin η (∇_xϕ(z_t), −∇_yϕ(z_t))ᵀz + D_Φ(z, z_t)`,
-- `z_{t+1} = argmin η (∇_xϕ(w_{t+1}), −∇_yϕ(w_{t+1}))ᵀz + D_Φ(z, z_t)`.
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
  -- main sequence: zₜ = (x_seq t, y_seq t)
  (x_seq : ℕ → E)
  (y_seq : ℕ → F)
  -- prox sequence: wₜ = (u_seq t, v_seq t)
  (u_seq : ℕ → E)
  (v_seq : ℕ → F) : Prop :=
  -- z₀ is argmin of phi in 𝓩 ∩ 𝓓
  (IsMinOn (fun z : E × F => a * phix z.1 + b * phiy z.2)
    ((𝓧 ∩ 𝓓x) ×ˢ (𝓨 ∩ 𝓓y))
    (x_seq 0, y_seq 0)) ∧
  -- w_{t+1} update
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
  -- z_{t+1} update
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

def IsSVRGIterates {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (k : ℕ)
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (y : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  let f_sum := fun z => (1 / (m : ℝ)) • ∑ i, f i z
  (∀ s ω, x s 0 ω = y s ω) ∧
  (∀ s t ω, t < k →
    x s (t + 1) ω =
      (x s t ω) - η • (gradient (f (I s t ω)) (x s t ω) -
                       gradient (f (I s t ω)) (y s ω) +
                       gradient f_sum (y s ω))) ∧
  (∀ s ω, y (s + 1) ω = (1 / (k : ℝ)) • ∑ i ∈ Finset.range k, x s i ω)

def IsSVRGSequence {m n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (k : ℕ)
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (y : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  (∀ s t, Measurable (x s t)) ∧
  (∀ s, Measurable (y s)) ∧
  (∀ s t, Measurable (I s t)) ∧
  (IsSVRGIterates k f x y I η) ∧
  (ProbabilityTheory.iIndepFun (fun (p : ℕ × ℕ) => I p.1 p.2) μ) ∧
  (∀ s t,
    ProbabilityTheory.IndepFun
      (I s t)
      (fun ω => (x s t ω, y s ω))
      μ) ∧
  (∀ s t i, μ ((I s t) ⁻¹' {i}) = (m : ENNReal)⁻¹)

def IsSemidifferentiableOnWith {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (O : Set E)
  (h : E → E → EReal) : Prop :=
  ∀ x ∈ O, ∀ w : E,
    HasHadamardDirectionalDerivativeEReal f x w (h x w)

def IsSingleValued {E : Type*}
  (S : E → Set E) : Prop :=
  ∀ z, ∃! x, x ∈ S z

def IsStandardSelfConcordantBarrier {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsSelfConcordant 𝓧 f 2 ∧ BlowsUpOnBoundary 𝓧 f

-- Bubeck's stochastic first-order oracle condition `𝔼(g̃(x) | x) ∈ ∂f(x)` (§6.1), conditioned on
-- the current iterate, the subgradient taken relative to `𝓧`.
def IsStochasticSubgradientOracle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω)
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : Ω → E)
  (g : Ω → E →L[ℝ] ℝ) : Prop :=
  (Integrable g μ) ∧
  (∀ᵐ ω ∂μ, IsSubgradientOn 𝓧 f (x ω) (condExpGivenIterate μ x g ω))

-- Stochastic mirror descent with step sizes `η` (Bubeck §6.1): `x₁ ∈ argmin_{𝓧 ∩ 𝓓} Φ` and
-- `x_{t+1} = argmin_{z ∈ 𝓧 ∩ 𝓓} η_t ⟨g̃(x_t), z⟩ + D_Φ(z, x_t)`. SGD is the case `Φ = ½‖·‖²` on
-- an inner-product space (Theorem 6.2).
def IsStochasticMirrorDescentSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (phi : E → ℝ)
  (x : ℕ → (Ω → E))
  (g : ℕ → (Ω → E →L[ℝ] ℝ))
  (η : ℕ → ℝ) : Prop :=
  (∀ t, Measurable (x t)) ∧
  (∀ ω, x 0 ω ∈ 𝓧 ∩ 𝓓) ∧
  (∀ ω, IsMinOn phi (𝓧 ∩ 𝓓) (x 0 ω)) ∧
  (∀ t ω, x t ω ∈ 𝓧 ∩ 𝓓) ∧
  (∀ t ω,
    IsMinOn
      (fun z =>
        (η t) * g t ω z +
        bregmanDivergence phi z (x t ω))
      (𝓧 ∩ 𝓓)
      (x (t + 1) ω))

def IsStrictMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), x₀ ≠ x₁ → v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  0 < inner ℝ (v₁ - v₀) (x₁ - x₀)

noncomputable def lipModulusRel {E : Type*} [NormedAddCommGroup E] {F : Type*} [NormedAddCommGroup F]
  (F : E → F)
  (X : Set E)
  (x_bar : E) : EReal :=
  Filter.limsup
    (fun p : E × E =>
      ((‖F p.2 - F p.1‖ / ‖p.2 - p.1‖ : ℝ) : EReal))
    (((𝓝[X] x_bar) ×ˢ (𝓝[X] x_bar)) ⊓
      Filter.principal {p : E × E | p.1 ≠ p.2})

noncomputable def lipModulus {E : Type*} [NormedAddCommGroup E] {F : Type*} [NormedAddCommGroup F]
  (F : E → F)
  (x_bar : E) : EReal :=
  lipModulusRel F Set.univ x_bar

def IsStrictlyContinuousAt {E : Type*} [NormedAddCommGroup E] {F : Type*} [NormedAddCommGroup F]
  (F : E → F)
  (x_bar : E) : Prop :=
  IsFiniteEReal (lipModulus F x_bar)

def IsStrictlyDifferentiableAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar v : E) : Prop :=
  IsFiniteEReal (f x_bar) ∧
  Filter.Tendsto
    (fun p : E × E =>
      (f p.2 - f p.1 -
          (((inner ℝ v (p.2 - p.1)) : ℝ) : EReal)) /
        ((‖p.2 - p.1‖ : ℝ) : EReal))
    (((𝓝 x_bar) ×ˢ (𝓝 x_bar)) ⊓
      Filter.principal {p : E × E | p.2 ≠ p.1})
    (𝓝 (0 : EReal))

def IsStrictlyDifferentiable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar : E) : Prop :=
  ∃ v : E, IsStrictlyDifferentiableAt f x_bar v

-- Strong monotonicity of a set-valued mapping with constant c (RW 12.53; BC Chapter 22),
-- in the same shape as `IsMonotone`. FCA 4.1.3's single-valued notion is this at the
-- graph of F restricted to C.
def IsStronglyMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E)
  (c : ℝ) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  c * ‖x₁ - x₀‖^2 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

def IsSubadditive {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ (x₁ : E), ∀ (x₂ : E),
  f (x₁ + x₂) ≤ (f x₁) + (f x₂)

def IsSublinearRW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (0 ∈ effDom f ∧ IsERealPosHomogeneous f) ∧
  ConvexEReal f

def IsSymmetricFun {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x, f (-x) = f x

def IsUscOnEReal {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (O : Set E) : Prop :=
  ∀ x ∈ O, Filter.limsup f (𝓝[O] x) ≤ f x

def Minorizes {E : Type*}
  (f : E → EReal) (g : E → EReal) : Prop :=
  ∀ x, f x ≤ g x

noncomputable def newtonDecrement {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  dualNorm (localNorm f x) (gradient f x)

def convexNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : E) (C : Set E) : Set E :=
  {s : E | ∀ y ∈ C, inner ℝ s (y - x) ≤ 0}

def pLiminf {E : Type*} [NormedAddCommGroup E] (Tseq : ℕ → E → Set E) : E → Set E :=
  fun x => setLiminf (fun n => Tseq n x)

def pLimsup {E : Type*} [NormedAddCommGroup E] (Tseq : ℕ → E → Set E) : E → Set E :=
  fun x => setLimsup (fun n => Tseq n x)

def PointwiseMapConverges {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) (T : E → Set E) : Prop :=
  pLimsup Tseq = T ∧ pLiminf Tseq = T

def polarBody {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ 1}

noncomputable def setIndicator {E : Type*}
  (H : Set E)
  (x : E)
  : EReal := by
  classical
  exact if x ∈ H then 0 else ⊤

-- Level-boundedness of f on S is RW's `IsLevelBounded` (RW 1.8) of f plus the indicator of S.
def LevelBoundedOn {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsLevelBounded (fun x => liftRealtoEReal f x + setIndicator S x)

def convexSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) : Set E :=
  {s | ∀ y, f y ≥ f x + inner ℝ s (y - x)}

noncomputable def directionalDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) : EReal :=
  limUnder (𝓝[>] 0) (fun t => differenceQuotient f x d t)

def directionalSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) : Set E :=
  let f' := fun (d : E) => directionalDeriv f x d
  {s : E | ∀ d, inner ℝ s d ≤ f' d}

def SupportingHyperplaneAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (s x : E) (r : ℝ)
  (C : Set E) : Prop :=
  (s ≠ 0) ∧ (x ∈ C) ∧
  (IsSupportingHyperplane s r C) ∧
  (x ∈ affineHyperplane s r)

def εEnlarge {E : Type*} [NormedAddCommGroup E] (A : Set E) (ε : ℝ) : Set E :=
  {y | ∃ z ∈ A, dist y z < ε}

def UniformlyConvergesOn {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E)
  (T : E → Set E)
  (X : Set E) : Prop :=
  ∀ ε > (0 : ℝ), ∀ ρ > (0 : ℝ),
    ∃ N : ℕ,
      ∀ n ≥ N, ∀ x ∈ X,
        (Tseq n x ∩ Metric.ball 0 ρ) ⊆ εEnlarge (T x) ε ∧
        (T x ∩ Metric.ball 0 ρ) ⊆ εEnlarge (Tseq n x) ε

def UniformlyConvergesOnBounded {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E)
  (T : E → Set E) : Prop :=
  ∀ R > (0 : ℝ),
    UniformlyConvergesOn Tseq T {x | ‖x‖ ≤ R}

def UniformlyConvergesOnBoundedEReal {E : Type*} [NormedAddCommGroup E]
  (gseq : ℕ → E → EReal)
  (g : E → EReal) : Prop :=
  ∀ R > (0 : ℝ), ∀ ε > (0 : ℝ),
    ∃ (N : ℕ), ∀ n ≥ N, ∀ x : E,
      ‖x‖ ≤ R →
        g x - (ε : EReal) ≤ gseq n x ∧
        gseq n x ≤ g x + (ε : EReal)

def addMap {E : Type*} [NormedAddCommGroup E]
  (S T : E → Set E) : E → Set E :=
  fun x => {z | ∃ u ∈ S x, ∃ v ∈ T x, z = u + v}

def affineHull {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Set E
  := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → E) (_ : ∀ i, x i ∈ C),
     {v : E |
      ∃ (a : Fin k → ℝ), (∑ i, a i = 1) ∧ (v = ∑ i, a i • x i)}

def affineMinorantValuesE {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal)
    (x : E) : Set EReal :=
  {v : EReal | ∃ (z : E × ℝ),
    (v = (inner ℝ z.1 x - z.2 : ℝ)) ∧ (∀ y, (inner ℝ z.1 y) - z.2 ≤ f y)}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

noncomputable def biconjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (u : E) : EReal :=
  conjugate (conjugate f) u

noncomputable def onesVec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin n, EuclideanSpace.single i 1

def doublyStochasticSet (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  {A | A (onesVec n) = onesVec n ∧
    ∀ j : Fin n, ∑ i : Fin n, (A (EuclideanSpace.single j 1)) i = 1}

def birkhoffPolytope (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  {A ∈ doublyStochasticSet n |
    ∀ i j : Fin n, (A (EuclideanSpace.single j 1)) i ≥ 0}

noncomputable def verticalSlice {E : Type*}
  (S : Set (E × ℝ)) (x : E) : Set ℝ :=
  {r : ℝ | (x, r) ∈ S}

noncomputable def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((fun r : ℝ => (r : EReal)) '' verticalSlice S x))

noncomputable def closedConvexHullFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (h : E → EReal) : E → EReal :=
  funFromSet (closure (convexHull ℝ (epigraph h)))

def cone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ} (x : Fin m → E) : Set E :=
  {v : E | ∃ (α : Fin m → ℝ) (_ : ∀ i, α i ≥ 0), v = ∑ i, α i • x i}

def coneKp {n : ℕ} (p : ℝ) (hn : n ≥ 2) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ⟨n - 1, by omega⟩ ≥
    (∑ k : Fin (n - 1), |x ⟨k.val, by omega⟩| ^ p) ^ (1 / p)}

noncomputable def hsInner {n : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, inner ℝ (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1))

noncomputable def hsInnerSA {n : ℕ}
    (A B : selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) : ℝ :=
  hsInner (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

def conePolarSA {n : ℕ}
    (K : Set (selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) :
    Set (selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
  {P | ∀ M ∈ K, hsInnerSA M P ≤ 0}

def cont {X : Type*} [TopologicalSpace X]
  (f : X → EReal) : Set X :=
  {x : X | f x ≠ ⊤ ∧ f x ≠ ⊥ ∧ ContinuousAt f x}

def probSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)}

def conv {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))
    := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → (EuclideanSpace ℝ (Fin n))) (_ : ∀ i, x i ∈ S),
         {v : (EuclideanSpace ℝ (Fin n)) |
          ∃ (a : (EuclideanSpace ℝ (Fin k))),
          (a.ofLp ∈ (probSimplex k)) ∧ (v = ∑ i, a i • x i)}

lemma convexCone_isConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E} (hC : IsConvexCone C) : Convex ℝ C := by
  intro x hx y hy a b ha hb hab
  exact hC x hx y hy a ha b hb

noncomputable def convexHullFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (g : E → EReal) : E → EReal :=
  funFromSet (convexHull ℝ (epigraph g))

noncomputable def distToSetEReal {E : Type*} [NormedAddCommGroup E]
  (x : E) (A : Set E) : EReal :=
  sInf ((fun y : E => ((‖x - y‖ : ℝ) : EReal)) '' A)

noncomputable def ellipsoidDecay (n i : ℕ) : ℝ :=
  Real.exp (-(i : ℝ) / (2 * (n : ℝ) ^ 2))

noncomputable def ellipsoidGapBound (B R r : ℝ) (n i : ℕ) : ℝ :=
  2 * B * R * ellipsoidDecay n i / r

noncomputable def exactCalmFromBelowModulus {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) (x_bar : E) : EReal :=
  sInf ((fun κ : ℝ => (κ : EReal)) '' {κ : ℝ | IsCalmFromBelowAtWith f x_bar κ})

noncomputable def expNegWT (v : EReal) : ℝ :=
  if v = ⊤ then 0 else Real.exp (-(v.toReal))

noncomputable def gammaMin {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf {v | ∃ l ∈ dualCone K, ‖l‖ = 1 ∧ v = inner (𝕜 := ℝ) l u}

noncomputable def gaugeFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x : E) : EReal :=
  sInf {l : EReal | ∃ (l' : ℝ),
                        (l = (l' : EReal)) ∧
                        (l' > 0) ∧
                        (∃ y ∈ C, (x = l' • y))}

-- RW Definition 3.3: the horizon cone of an arbitrary set, in the sequential form of RW 3(2).
-- Stated for any topological real vector space so that it applies to epigraphs in `E × ℝ`.
-- The sequential form gives `horizonCone ∅ = ∅`, whereas RW sets `∅^∞ = {0}`; kept as is
-- (decision of 2026-10-14), no statement depends on the empty case.
def horizonCone {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (C : Set E) : Set E :=
  {x : E | ∃ (xseq : ℕ → E) (l : ℕ → ℝ),
    (∀ i, xseq i ∈ C) ∧
    (Filter.Tendsto l Filter.atTop (𝓝[>] 0)) ∧
    (Filter.Tendsto
      (fun i => (l i) • (xseq i))
      Filter.atTop
      (𝓝 x))}

-- Asymptotic (horizon, recession) function, defined epigraphically as in RW 3.17:
-- `epi (asymptoticFun f) = horizonCone (epi f)`. Decided 2026-10-14: this is the most general of
-- the three books' definitions; FCA (3.2.2) `sup_{t>0} (f(x₀+td) − f(x₀))/t = lim_{t→∞} …` and
-- BC 9.28 `sup_{x ∈ dom f} (f(x+y) − f(x))` are each book's own equivalence theorem
-- (FCA B.3.2.1, BC 9.29/9.30, RW 3.21). RW's exceptional case f ≡ +∞ (f^∞ = δ_{0}) is not
-- special-cased: with the sequential horizon cone the value is then +∞ everywhere.
noncomputable def asymptoticFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : E → EReal :=
  funFromSet (horizonCone (epigraph f))

noncomputable def imageFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (A : F →ₗ[ℝ] E)
  (g : F → EReal)
  (x : E) : EReal :=
  sInf (Set.image g {y : F | A y = x})

noncomputable def infimalConv {E : Type*} [NormedAddCommGroup E]
  (f₁ : E → EReal)
  (f₂ : E → EReal)
  (x : E) : EReal
  := sInf {z : EReal | ∃ y : E,
  z = (f₁ y + f₂ (x - y))}

noncomputable def pompeiuHausdorffDistOn {E : Type*} [NormedAddCommGroup E]
  (ρ : ℝ)
  (C D : Set E) : EReal :=
  sSup
    ((fun x : E =>
      max
        (distToSetEReal x C - distToSetEReal x D)
        (distToSetEReal x D - distToSetEReal x C)) ''
      Metric.closedBall (0 : E) ρ)

noncomputable def integratedSetDistance {E : Type*} [NormedAddCommGroup E]
  (C D : Set E) : ℝ :=
  ∫ ρ in Set.Ioi (0 : ℝ),
    (pompeiuHausdorffDistOn ρ C D).toReal * Real.exp (-ρ)

def invMap {E : Type*}
  (T : E → Set E) : E → Set E :=
  fun y => {x | y ∈ T x}

noncomputable def lipModulusEReal {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (x_bar : E) : EReal :=
  sInf
    ((fun κ : ℝ => (κ : EReal)) ''
      {κ : ℝ | 0 ≤ κ ∧
        ∃ U ∈ 𝓝 x_bar, ∀ x ∈ U, ∀ y ∈ U,
          IsFiniteEReal (f x) ∧
          IsFiniteEReal (f y) ∧
          f y ≤ f x + ((κ * ‖y - x‖ : ℝ) : EReal) ∧
          f x ≤ f y + ((κ * ‖y - x‖ : ℝ) : EReal)})

noncomputable def marginalFun {n m : ℕ}
  (g : EuclideanSpace ℝ (Fin (n + m)) → EReal)
  (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  let g_concat : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EReal := fun a b
  => g ((WithLp.equiv 2 _).symm (Fin.append (α := ℝ) a.ofLp b.ofLp))
  sInf (Set.range (g_concat x))

def IsMinorizedAt {E : Type*}
  (C : Set (E × ℝ)) (x : E) : Prop :=
  let K := {r : ℝ | ∃ (z : E × ℝ), (z ∈ C) ∧ (x = z.1) ∧ (r = z.2)}
  ∃ (k₀ : ℝ), ∀ r ∈ K, r ≥ k₀

def EpiSetNoNegInf {E : Type*}
  (S : Set (E × ℝ)) : Prop :=
  ∀ x : E, IsMinorizedAt S x

noncomputable def moreauEnvelope {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (lam : ℝ)
  (x : E) : EReal :=
  sInf {v : EReal | ∃ w, v = f w + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 }

noncomputable def multiInfimalConv {E : Type*} [NormedAddCommGroup E]  (m : ℕ)
  (f : ℕ → (E → EReal))
  (x : E) : EReal :=
  sInf {z : EReal |
        ∃ (y : ℕ → E),
        (x = ∑ i ∈ Finset.range m, (y i)) ∧
        (z = ∑ i ∈ Finset.range m, ((f i) (y i)))}

def negPsdCone (n : ℕ) :
    Set (selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
  {A | ∀ x, inner ℝ ((A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) x) x ≤ 0}

def opDom {E : Type*} (A : E → Set E) : Set E :=
  {x : E | Set.Nonempty (A x)}

def parallelSubspace {E : Type*} [NormedAddCommGroup E]
  (S : Set E) : Set E :=
  {v : E | ∃ x, ∃ y, (x ∈ S) ∧ (y ∈ S) ∧ (v = x - y)}

noncomputable def pathFollowingStep {n : ℕ}
  (F : EuclideanSpace ℝ (Fin n) → ℝ)
  (t ν : ℝ) (x c : EuclideanSpace ℝ (Fin n))
  : ℝ × EuclideanSpace ℝ (Fin n) :=
  let t_next := (1 + 1 / (13 * Real.sqrt ν)) * t
  let x_next := x - (hessianOperator F x).inverse (t_next • c + gradient F x)
  (t_next, x_next)

-- The perspective of f (FCA §B.2.2), f̃(u, x) = u f(x/u) for u > 0 and +∞ otherwise; on a
-- general inner product space since 2026-10-14 (it was fixed to EuclideanSpace before).
noncomputable def perspective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) (u : ℝ) (x : E) : EReal :=
  if u > 0 then u * f (u⁻¹ • x) else ⊤

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

lemma polarCone_isClosed {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E} : IsClosed (polarCone K) := by
  have pc_intersection : (polarCone K) = ⋂ x ∈ K, {s : E | inner ℝ s x ≤ 0} := by
    ext s
    simp [polarCone]
  rw [pc_intersection]
  have h_cont (x : E) : Continuous (fun s : E => (inner ℝ s x : ℝ)) :=
    continuous_inner.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ => x)))
  have h_closed : ∀ x ∈ K, IsClosed {s : E | inner ℝ s x ≤ 0} := by
    intro x _
    exact IsClosed.preimage (h_cont x) isClosed_Iic
  exact isClosed_biInter h_closed

lemma polarCone_isConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E} : Convex ℝ (polarCone K) := by
  intro x hx y hy a b ha hb hab
  have h_combo : ∀ z ∈ K, inner ℝ (a • x + b • y) z ≤ 0 := by
    intro z hz
    simp [inner_add_left, inner_smul_left_eq_star_smul]
    have hx' : a * (inner ℝ x z) ≤ 0 := by
      have non_mul_x := hx.out z hz
      have := mul_le_mul_of_nonneg_left non_mul_x ha
      simpa [mul_zero] using this
    have hy' : b * (inner ℝ y z) ≤ 0 := by
      have non_mul_y := hy.out z hz
      have := mul_le_mul_of_nonneg_left non_mul_y hb
      simpa [mul_zero] using this
    have := add_le_add hx' hy'
    simpa [add_zero] using this
  exact h_combo

lemma polarCone_isNonempty {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {K : Set E} : Set.Nonempty (polarCone K) :=
  ⟨0, by simp [polarCone]⟩

noncomputable def proxPerturbedFun {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) (lam : ℝ) : E → EReal :=
  fun x => f x + (((2 * lam)⁻¹ * ‖x‖ ^ 2 : ℝ) : EReal)

def psdCone (n : ℕ) :
    Set (selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
  {A | ∀ x, 0 ≤ inner ℝ ((A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) x) x}

noncomputable def realDirectionalDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → ℝ)
  (x : E)
  (d : E) : ℝ :=
  (directionalDeriv (liftRealtoEReal f) x d).toReal

def regularSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar : E) : Set E :=
  {v | IsRegularSubgradientAt f x_bar v}

noncomputable def sagAverageIterate {n : ℕ} {Ω : Type*}
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (k : ℕ)
  (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  (1 / (k : ℝ)) • ∑ t ∈ Finset.range k, x t ω

noncomputable def sagaAverageIterate {n : ℕ} {Ω : Type*}
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (k : ℕ)
  (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  (1 / (k : ℝ)) • ∑ t ∈ Finset.range k, x (t + 1) ω

def setAdd {E : Type*} [NormedAddCommGroup E]
    (C : Set E) (K : Set E)
    : Set E
    := {v : E | ∃ c ∈ C, ∃ k ∈ K, v = c + k}

def setNeg {E : Type*} [NormedAddCommGroup E] (A : Set E) : Set E :=
  {x : E | -x ∈ A}

def setSub {E : Type*} [NormedAddCommGroup E] (A B : Set E) : Set E :=
  setAdd A (setNeg B)

noncomputable def singularValues {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Fin n → ℝ :=
  let T := ((ContinuousLinearMap.adjoint A).comp A)
  let h_sym : T.toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self A).toLinearMap.isSymmetric
  fun i => Real.sqrt (h_sym.eigenvalues finrank_euclideanSpace_fin i)

def smulMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ℝ) (T : E → Set E) : E → Set E :=
  fun x => {v | ∃ w ∈ T x, v = a • w}

def strictEpigraph {E : Type*}
  (f : E → EReal) : Set (E × ℝ)
  := {p : E × ℝ | f p.1 < p.2}

def subMap {E : Type*} [NormedAddCommGroup E]
  (S T : E → Set E) : E → Set E :=
  fun x => {z | ∃ u ∈ S x, ∃ v ∈ T x, z = u - v}

def sublevelSetFun {E : Type*}
  (f : E → EReal)
  (x : E) : Set E :=
  {y : E | f y ≤ f x}

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

def supportInterior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (C : Set E) : Set E :=
  {x : E | ∀ v : E, v ≠ 0 → (((inner ℝ x v) : ℝ) : EReal) < supportFunction C v}

def supportSublevelSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (h : E → EReal) : Set E :=
  {v : E | ∀ (w : E), (((inner ℝ v w) : ℝ) : EReal) ≤ h w}

def translateSet {E : Type*} [NormedAddCommGroup E]
  (C : Set E) (x : E)
  : Set E
  := {v : E | ∃ c ∈ C, v = (c - x)}

def unitBall {E : Type*} [NormedAddCommGroup E] : Set E := Metric.closedBall (0 : E) 1

noncomputable def valueFun {p n : ℕ}
  (phi : EuclideanSpace ℝ (Fin p) → EReal)
  (c : (Fin n) → (EuclideanSpace ℝ (Fin p) → EReal))
  (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  sInf (Set.image phi {u | ∀ j, (c j) u ≤ x j})

def vecHead {n : ℕ}
  (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n)
  := (WithLp.equiv 2 _).symm (fun i => x (Fin.castSucc i))

def vecLast {n : ℕ}
  (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ
  := x (Fin.last n)

noncomputable def xCentered {n : ℕ}
  (F : EuclideanSpace ℝ (Fin n) → ℝ)
  (t : ℕ → ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (ν : ℝ)
  (c : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
| 0 => newtonStep (ft F c (t 0)) x0
| k + 1 => (pathFollowingStep F (t k) ν (xCentered F t x0 ν c k) c).2
