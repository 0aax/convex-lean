import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

noncomputable def delta {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) (τ : ℝ) : E → EReal :=
  fun w => differenceQuotient f x w τ

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

theorem RW_chap_8_22
  (f : E → EReal)
  (x_bar : E)
  (hf_local_lsc : LocalLscAt f x_bar)
  (hx_bar : ⊥ < f x_bar ∧ f x_bar < ⊤) :
  let h : E → EReal := fun w_bar =>
    Filter.limsup
      (fun p : E × ℝ × E =>
        let x := p.1
        let τ := p.2.1
        let w := p.2.2
        delta f x τ w)
      ((fApproach f x_bar) ×ˢ ((𝓝[>] 0) ×ˢ (𝓝 w_bar)))
  let O : Set E := {w | h w < ⊤}
  (interior (effDom (regularSubderivative f x_bar)) = O) ∧
  (∀ w_bar ∈ O, regularSubderivative f x_bar w_bar = h w_bar) ∧
  (Set.Nonempty O →
    (∀ w_bar ∉ closure O, regularSubderivative f x_bar w_bar = ⊤) ∧
    (∀ w_bar ∈ frontier O, ∀ w_hat ∈ O,
      Filter.Tendsto
        (fun (τ : ℝ) => h ((1 - τ) • w_bar + τ • w_hat))
        (𝓝[>] 0)
        (𝓝 (regularSubderivative f x_bar w_bar)))) := by
  sorry
