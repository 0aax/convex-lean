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

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

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

def convexNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : E) (C : Set E) : Set E :=
  {s : E | ∀ y ∈ C, inner ℝ s (y - x) ≤ 0}

def convexSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) : Set E :=
  {s | ∀ y, f y ≥ f x + inner ℝ s (y - x)}

def horizonCone {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (C : Set E) : Set E :=
  {x : E | ∃ (xseq : ℕ → E) (l : ℕ → ℝ),
    (∀ i, xseq i ∈ C) ∧
    (Filter.Tendsto l Filter.atTop (𝓝[>] 0)) ∧
    (Filter.Tendsto
      (fun i => (l i) • (xseq i))
      Filter.atTop
      (𝓝 x))}

def regularSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar : E) : Set E :=
  {v | IsRegularSubgradientAt f x_bar v}

theorem RW_chap_8_12
  (f : E → EReal)
  (x_bar : E)
  (hx_bar : x_bar ∈ effDom f)
  (hf_convex : ConvexEReal f)
  (hf_proper : IsProper f) :
  subdifferential f x_bar = regularSubdifferential f x_bar ∧
  subdifferential f x_bar = convexSubdifferential f x_bar ∧
  horizonSubdifferential f x_bar ⊆ convexNormalCone x_bar (effDom f) ∧
  normalCone (effDom f) x_bar = convexNormalCone x_bar (effDom f) ∧
  (LocalLscAt f x_bar →
    horizonSubdifferential f x_bar = convexNormalCone x_bar (effDom f)) ∧
  (Set.Nonempty (subdifferential f x_bar) →
    (horizonSubdifferential f x_bar = convexNormalCone x_bar (effDom f)) ∧
    (horizonSubdifferential f x_bar = horizonCone (regularSubdifferential f x_bar))) := by
  sorry
