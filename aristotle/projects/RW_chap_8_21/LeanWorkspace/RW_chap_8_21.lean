import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

noncomputable def delta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) (τ : ℝ) : E → EReal :=
  fun w => differenceQuotient f x w τ

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

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

def IsSublinearRW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (0 ∈ effDom f ∧ IsERealPosHomogeneous f) ∧
  ConvexEReal f

theorem RW_chap_8_21
  (f : E → EReal)
  (x_bar : E)
  (hf_convex : ConvexEReal f)
  (hf_ne_bot : ∀ x, ⊥ < f x)
  (hx_bar : ⊥ < f x_bar ∧ f x_bar < ⊤)
  (hx_bar_dom : x_bar ∈ interior (effDom f)) :
  let W := {w | ∃ (τ : ℝ), 0 < τ ∧ x_bar + τ • w ∈ interior (effDom f)}
  ∃ (h : E → EReal),
    (IsSublinearRW h) ∧
    (∀ (w : E),
        Filter.Tendsto
        (fun (τ : ℝ) => (f (x_bar + τ • w) - f x_bar) / (τ : EReal))
        (𝓝[>] 0)
        (𝓝 (h w))) ∧
    (∀ (w : E), ∀ (τ : ℝ), 0 ≤ τ →
      f x_bar + (τ : EReal) * h w ≤ f (x_bar + τ • w)) ∧
    (∀ (w : E),
      regularSubderivative f x_bar w = subderivative f x_bar w ∧
      subderivative f x_bar w = Filter.liminf h (𝓝 w)) ∧
    (∀ (w : E), w ∈ W →
      Filter.liminf h (𝓝 w) = h w) ∧
    (W = interior (effDom (regularSubderivative f x_bar)) ∧
      W = interior (effDom (subderivative f x_bar)) ∧
      W = interior (effDom h)) := by
  sorry
