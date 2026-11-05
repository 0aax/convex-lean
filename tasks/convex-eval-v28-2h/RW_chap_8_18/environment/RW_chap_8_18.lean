import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

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

def IsEpiLimsup {E : Type*} [NormedAddCommGroup E]
  {ι : Type*}
  (F : ι → E → EReal) (l : Filter ι) (g : E → EReal) : Prop :=
  epigraph g = {p | ∀ W ∈ 𝓝 p, ∀ᶠ i in l, ∃ q ∈ epigraph (F i), q ∈ W}

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

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

def IsSublinearRW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (0 ∈ effDom f ∧ IsERealPosHomogeneous f) ∧
  ConvexEReal f

theorem RW_chap_8_18
  (f : E → EReal)
  (x_bar : E)
  (hx_bar : ⊥ < f x_bar ∧ f x_bar < ⊤) :
  LowerSemicontinuous (regularSubderivative f x_bar) ∧
  LowerSemicontinuous (subderivative f x_bar) ∧
  (0 ∈ effDom (regularSubderivative f x_bar) ∧ IsERealPosHomogeneous (regularSubderivative f x_bar)) ∧
  (0 ∈ effDom (subderivative f x_bar) ∧ IsERealPosHomogeneous (subderivative f x_bar)) ∧
  (∀ (w : E), subderivative f x_bar w ≤ regularSubderivative f x_bar w) ∧
  (LowerSemicontinuousAt f x_bar →
    (∀ (w : E), ⊥ < regularSubderivative f x_bar w) →
    IsSublinearRW (regularSubderivative f x_bar)) ∧
  (LocalLscAt f x_bar →
    IsEpiLimsup
      (fun x => subderivative f x)
      (fApproach f x_bar)
      (regularSubderivative f x_bar)) := by
  sorry
