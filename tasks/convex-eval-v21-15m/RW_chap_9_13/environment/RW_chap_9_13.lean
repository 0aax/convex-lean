import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

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

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

noncomputable def delta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) (τ : ℝ) : E → EReal :=
  fun w => differenceQuotient f x w τ

def IsFiniteEReal (a : EReal) : Prop :=
  ∃ r : ℝ, a = (r : EReal)

def IsFiniteAround {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (x_bar : E) : Prop :=
  ∃ U ∈ 𝓝 x_bar, ∀ x ∈ U, IsFiniteEReal (f x)

def IsLipschitzEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (A : Set X)
  (β : ℝ) : Prop :=
  (0 ≤ β) ∧
  (∀ x ∈ A, T x ≠ ⊤ ∧ T x ≠ ⊥) ∧
  (∀ (x y : X),
    x ∈ A → y ∈ A →
      ‖(T x).toReal - (T y).toReal‖ ≤ β • (dist x y))

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

def regularSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar : E) : Set E :=
  {v | IsRegularSubgradientAt f x_bar v}

theorem RW_chap_9_13
  [Nontrivial E]
  (f : E → EReal)
  (x_bar : E)
  (hf_lsc : LocalLscAt f x_bar)
  (hf_finite : ⊥ < f x_bar ∧ f x_bar < ⊤) :
  List.TFAE [
    IsLocallyLipschitzNearEReal f x_bar,
    horizonSubdifferential f x_bar = {(0 : E)},
    IsLocallyBoundedAt (fun x => regularSubdifferential f x) x_bar,
    IsLocallyBoundedAt (fun x => subdifferential f x) x_bar,
    ∀ (w : E), IsFiniteEReal (regularSubderivative f x_bar w),
    IsFiniteAround f x_bar ∧
      ∀ (w : E),
        IsLocallyBoundedAboveAtEReal
          (fun x => subderivative f x w) x_bar ] ∧
  (IsLocallyLipschitzNearEReal f x_bar →
    ((subdifferential f x_bar).Nonempty ∧
      IsCompact (subdifferential f x_bar)) ∧
    (lipModulusEReal f x_bar =
      sSup ((fun (w : E) => regularSubderivative f x_bar w) ''
            {w : E | ‖w‖ = 1})) ∧
    (sSup ((fun (w : E) => regularSubderivative f x_bar w) ''
            {w : E | ‖w‖ = 1}) =
      sSup ((fun (v : E) => ((‖v‖ : ℝ) : EReal)) ''
            subdifferential f x_bar))) := by
  sorry
