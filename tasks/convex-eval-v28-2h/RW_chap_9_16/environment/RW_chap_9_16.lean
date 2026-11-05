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

def IsFiniteEReal (a : EReal) : Prop :=
  ∃ r : ℝ, a = (r : EReal)

def IsFiniteOn {E : Type*}
  (f : E → EReal)
  (O : Set E) : Prop :=
  ∀ x ∈ O, IsFiniteEReal (f x)

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

def IsSemidifferentiableOnWith {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (O : Set E)
  (h : E → E → EReal) : Prop :=
  ∀ x ∈ O, ∀ w : E,
    HasHadamardDirectionalDerivativeEReal f x w (h x w)

def IsUscOnEReal {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (O : Set E) : Prop :=
  ∀ x ∈ O, Filter.limsup f (𝓝[O] x) ≤ f x

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem RW_chap_9_16
  (f : E → EReal)
  (O : Set E)
  (hO_open : IsOpen O)
  (hf_finite_on : IsFiniteOn f O) :
  ((∀ x ∈ O,
      IsLocallyLipschitzNearEReal f x ∧ IsRegularAt f x) ↔
    ∃ (h : E → E → EReal),
      (∀ x ∈ O, ∀ (w : E),
        IsFiniteEReal (h x w) ∧
          HasDirectionalDerivativeEReal f x w (h x w)) ∧
      (∀ (w : E), IsUscOnEReal (fun x => h x w) O)) ∧
  (∀ (h : E → E → EReal),
    ((∀ x ∈ O, ∀ (w : E),
        IsFiniteEReal (h x w) ∧
          HasDirectionalDerivativeEReal f x w (h x w)) ∧
      (∀ (w : E), IsUscOnEReal (fun x => h x w) O)) →
      IsUscOnEReal
        (fun (p : E × E) => h p.1 p.2)
        {p : E × E | p.1 ∈ O} ∧
      IsSemidifferentiableOnWith f O h ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = Filter.liminf
          (fun (p : ℝ × E) =>
            (f (x + p.1 • p.2) - f x) / (p.1 : EReal))
          ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w)) ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = Filter.limsup
          (fun (p : ℝ × E) =>
            (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
          (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓
            Filter.principal {p : ℝ × E | p.2 ∈ O})) ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = subderivative f x w) ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = regularSubderivative f x w) ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = supportFunction (subdifferential f x) w) ∧
      (∀ x ∈ O,
        (subdifferential f x).Nonempty ∧ Convex ℝ (subdifferential f x)) ∧
      IsOuterSemicontinuousOn (fun x => subdifferential f x) O ∧
      (∀ x ∈ O, IsLocallyBoundedAt (fun y => subdifferential f y) x)) := by
  sorry
