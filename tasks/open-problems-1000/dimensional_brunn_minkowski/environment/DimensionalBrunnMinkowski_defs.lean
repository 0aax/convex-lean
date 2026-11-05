import Mathlib

open MeasureTheory Pointwise ENNReal Filter Topology Metric ProbabilityTheory NNReal

def IsSymmetricSet {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def IsLogConcaveMeasure {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ (A B : Set (EuclideanSpace ℝ (Fin n))),
  ∀ c : ℝ,
    IsCompact A → IsCompact B → 0 < c → c < 1 →
    μ (c • A + (1 - c) • B) ≥ ENNReal.rpow (μ A) c * ENNReal.rpow (μ B) (1 - c)

def IsEvenMeasure {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
  Prop :=
  Measure.map (fun x => -x) μ = μ

def gardner_zvavitch_bm : Prop :=
  ∀ (n : ℕ), n ≥ 1 →
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin n))),
      IsLogConcaveMeasure μ →
      IsEvenMeasure μ →
        ∀ (K : ConvexBody (EuclideanSpace ℝ (Fin n))) (L : ConvexBody (EuclideanSpace ℝ (Fin n))),
          IsSymmetricSet K.carrier →
          IsSymmetricSet L.carrier →
          ∀ (lam : ℝ≥0), lam ≤ 1 →
            (μ (lam • K + (1 - lam) • L)) ^ (1 / (n : ℝ)) ≥ lam * (μ K) ^ (1 / (n : ℝ)) + (1 - lam) * (μ L) ^ (1 / (n : ℝ))
