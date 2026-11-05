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

def IsLogConcaveMeasure {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ (A B : Set (EuclideanSpace ℝ (Fin n))),
  ∀ c : ℝ,
    IsCompact A → IsCompact B → 0 < c → c < 1 →
    μ (c • A + (1 - c) • B) ≥ ENNReal.rpow (μ A) c * ENNReal.rpow (μ B) (1 - c)

noncomputable def expNegWT (v : EReal) : ℝ :=
  if v = ⊤ then 0 else Real.exp (-(v.toReal))

theorem Duchi_Q9_1
  {n : ℕ} :
  (∀ (u : EuclideanSpace ℝ (Fin n) → EReal),
    InConvRn u →
    Measurable (fun x => ENNReal.ofReal (expNegWT (u x))) →
    let P := Measure.withDensity volume (fun x => ENNReal.ofReal (expNegWT (u x)))
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P) ∧
  (∀ (P : Measure (EuclideanSpace ℝ (Fin n)))
      (p : EuclideanSpace ℝ (Fin n) → ℝ),
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P →
    Continuous p →
    (∀ x, 0 ≤ p x) →
    P = Measure.withDensity volume (fun x => ENNReal.ofReal (p x)) →
    ∃ (u : EuclideanSpace ℝ (Fin n) → EReal),
      InConvRn u ∧ ∀ x, p x = expNegWT (u x)) ∧
  (∀ (P : Measure (EuclideanSpace ℝ (Fin n)))
      (A : Set (EuclideanSpace ℝ (Fin n)))
      (r : ℝ),
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P →
    Convex ℝ A →
    (∀ x, x ∈ A ↔ -x ∈ A) →
    MeasurableSet A →
    P A ≠ 0 →
    r ≥ 1 →
    1 - (P (r • A)).toReal ≤
      Real.rpow ((1 - (P A).toReal) / (P A).toReal) (r / 2) *
        Real.sqrt ((P A).toReal * (1 - (P A).toReal))) := by
  sorry
