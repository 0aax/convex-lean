import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def IsLinearOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (𝓧 : Set E)
  (σ : E → EReal) : Prop :=
  (∀ (x₁ x₂ : E), ∀ (t₁ t₂ : ℝ),
  x₁ ∈ 𝓧 → x₂ ∈ 𝓧 → t₁ • x₁ + t₂ • x₂ ∈ 𝓧 →
  (σ (t₁ • x₁ + t₂ • x₂)) = t₁ * (σ x₁) + t₂ * (σ x₂))

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

theorem FCA_chap_B_4_2_1
  (f : E → EReal)
  (x : E)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ y, ⊥ < f y)
  (hx : x ∈ interior (effDom f)) :
  let g := fun (d : E) =>
    limUnder (𝓝[>] 0) (fun (t : ℝ) => t⁻¹ * ((f (x + t • d)).toReal - (f x).toReal))
  List.TFAE [
    IsLinearOn Set.univ (liftRealtoEReal g),
    ∃ (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E),
      ∀ i, DifferentiableAt ℝ (fun (t : ℝ) => (f (x + t • b i)).toReal) 0,
    DifferentiableAt ℝ (fun y => (f y).toReal) x
  ] := by
  sorry
