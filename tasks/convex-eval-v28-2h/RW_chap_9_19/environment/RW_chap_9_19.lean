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

def IsLipschitzEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (A : Set X)
  (β : ℝ) : Prop :=
  (0 ≤ β) ∧
  (∀ x ∈ A, T x ≠ ⊤ ∧ T x ≠ ⊥) ∧
  (∀ (x y : X),
    x ∈ A → y ∈ A →
      ‖(T x).toReal - (T y).toReal‖ ≤ β • (dist x y))

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

def IsRegularAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar : E) : Prop :=
  (⊥ < f x_bar ∧ f x_bar < ⊤) ∧
  LocalLscAt f x_bar ∧
  ∀ w, subderivative f x_bar w = regularSubderivative f x_bar w

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

theorem RW_chap_9_19
  (f : E → EReal)
  (O : Set E)
  (hO_open : IsOpen O)
  (hf_finite_on : ∀ x ∈ O, IsFiniteEReal (f x)) :
  List.TFAE [
  ∀ x ∈ O, IsStrictlyDifferentiable f x,
  ∃ (g : E → ℝ),
    (∀ x ∈ O, f x = (g x : EReal)) ∧
    ContDiffOn ℝ 1 g O,
  (∀ x ∈ O, IsLocallyLipschitzNearEReal f x) ∧
    (∀ x ∈ O, IsRegularAt f x) ∧
    (∀ x ∈ O, ∃! (v : E), v ∈ subdifferential f x),
  (∀ x ∈ O, LocalLscAt f x) ∧
    (∀ x ∈ O,
      IsLocallyBoundedAt (fun y => subdifferential f y) x) ∧
    (∀ x ∈ O,
      (subdifferential f x).Nonempty →
        ∃! (v : E), v ∈ subdifferential f x) ] := by
  sorry
