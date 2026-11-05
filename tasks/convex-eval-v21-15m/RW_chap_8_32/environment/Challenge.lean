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

def IsCalmFromBelowAtWith {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) (x_bar : E) (κ : ℝ) : Prop :=
  0 ≤ κ ∧
  (⊥ < f x_bar) ∧ (f x_bar < ⊤) ∧
  ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V,
    f x_bar - κ * ‖x - x_bar‖ ≤ f x

def IsCalmFromBelowAt {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) (x_bar : E) : Prop :=
  ∃ (κ : ℝ), IsCalmFromBelowAtWith f x_bar κ

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

noncomputable def distToSetEReal {E : Type*} [NormedAddCommGroup E]
  (x : E) (A : Set E) : EReal :=
  sInf ((fun y : E => ((‖x - y‖ : ℝ) : EReal)) '' A)

noncomputable def exactCalmFromBelowModulus {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) (x_bar : E) : EReal :=
  sInf ((fun κ : ℝ => (κ : EReal)) '' {κ : ℝ | IsCalmFromBelowAtWith f x_bar κ})

def unitBall {E : Type*} [NormedAddCommGroup E] : Set E := Metric.closedBall (0 : E) 1

theorem RW_chap_8_32
  (f : E → EReal)
  (x_bar : E) :
  ((IsCalmFromBelowAt f x_bar) ↔
      subderivative f x_bar 0 = 0) ∧
  ((IsCalmFromBelowAt f x_bar) ↔
      ∀ (w : E), subderivative f x_bar w > ⊥) ∧
  (exactCalmFromBelowModulus f x_bar =
      (-1 : EReal) *
        sInf ((fun (w : E) => subderivative f x_bar w) '' unitBall)) ∧
  ((LocalLscAt f x_bar) →
    (((Set.Nonempty (subdifferential f x_bar)) ↔
        regularSubderivative f x_bar 0 = 0) ∧
      ((Set.Nonempty (subdifferential f x_bar)) ↔
        ∀ (w : E), regularSubderivative f x_bar w > ⊥))) ∧
  ((LocalLscAt f x_bar ∧ IsCalmFromBelowAt f x_bar) →
    ∃ v_bar ∈ subdifferential f x_bar,
      (((‖v_bar‖ : ℝ) : EReal) = exactCalmFromBelowModulus f x_bar)) ∧
  ((IsRegularAt f x_bar) →
    ((IsCalmFromBelowAt f x_bar) ↔
        Set.Nonempty (subdifferential f x_bar)) ∧
    (exactCalmFromBelowModulus f x_bar =
      distToSetEReal (0 : E) (subdifferential f x_bar))) := by
  sorry
