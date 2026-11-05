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

def IsGloballyOptimal {E : Type*}
  (f : E → EReal)
  (C : Set E) (x_bar : E) : Prop :=
  f x_bar < ⊤ ∧
  ∀ x ∈ C, f x_bar ≤ f x

def IsLocallyOptimal {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (C : Set E) (x_bar : E) : Prop :=
  f x_bar < ⊤ ∧
  ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V ∩ C,
    f x_bar ≤ f x

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

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

theorem RW_chap_8_15
  (f : E → EReal)
  (x_bar : E)
  (C : Set E)
  (hx_bar : x_bar ∈ C)
  (hC_closed : IsClosed C)
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f) :
  (ConstraintQualification f C x_bar →
    (IsLocallyOptimal f C x_bar →
      ∃ v ∈ subdifferential f x_bar,
        ∃ n ∈ normalCone C x_bar,
          v + n = 0) ∧
    ((IsRegularAt f x_bar ∧ IsRegularSetAt C x_bar) →
      ((∃ v ∈ subdifferential f x_bar,
          ∃ n ∈ normalCone C x_bar,
            v + n = 0) ↔
        (∀ w ∈ posTangentConeAt C x_bar,
          0 ≤ subderivative f x_bar w)))) ∧
  ((ConvexEReal f ∧ Convex ℝ C ∧ ⊥ < f x_bar ∧ f x_bar < ⊤) →
    (((∃ v ∈ subdifferential f x_bar,
          ∃ n ∈ normalCone C x_bar,
            v + n = 0) ∨
        (∀ w ∈ posTangentConeAt C x_bar,
          0 ≤ subderivative f x_bar w)) →
      IsGloballyOptimal f C x_bar)) := by
  sorry
