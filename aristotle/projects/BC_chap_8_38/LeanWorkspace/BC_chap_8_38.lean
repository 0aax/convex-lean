import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def IsLipschitzEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (A : Set X)
  (β : ℝ) : Prop :=
  (0 ≤ β) ∧
  (∀ x ∈ A, T x ≠ ⊤ ∧ T x ≠ ⊥) ∧
  (∀ (x y : X),
    x ∈ A → y ∈ A →
      ‖(T x).toReal - (T y).toReal‖ ≤ β • (dist x y))

def IsLocallyLipschitzNearEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (x : X) : Prop :=
  ∃ (ρ : ℝ),
    (0 < ρ) ∧
    (∃ (β : ℝ), IsLipschitzEReal T (Metric.ball x ρ) β)

def IsLocallyLipschitzOnEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (C : Set X) : Prop :=
  ∀ x ∈ C, IsLocallyLipschitzNearEReal T x

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

theorem BC_chap_8_38
  (f : E → EReal)
  (x₀ : E)
  (hx₀ : x₀ ∈ effDom f)
  (hf_proper : IsProper f)
  (hf_convex : ConvexEReal f) :
  List.TFAE [
    IsLocallyLipschitzNearEReal f x₀,
    ContinuousAt f x₀,
    (∃ U ∈ 𝓝 x₀, ∃ (a b : ℝ),
      ∀ y ∈ U,
        (a : EReal) ≤ f y ∧ f y ≤ (b : EReal)),
    (∃ U ∈ 𝓝 x₀, ∃ (a : ℝ),
      ∀ y ∈ U, f y ≤ (a : EReal))
  ] ∧
  (ContinuousAt f x₀ →
    IsLocallyLipschitzOnEReal f (intrinsicInterior ℝ (effDom f))) := by
  sorry
