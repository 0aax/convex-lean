import Mathlib
open Set MeasureTheory ENNReal
open scoped MeasureTheory

noncomputable def supportFun
  {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun y => inner ℝ x y) '' K)

noncomputable def projectedArea {n : ℕ}
  (K : ConvexBody (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n)) : ENNReal :=
  μH[(n : ℝ) - 1] (((ℝ ∙ u)ᗮ).starProjection '' (K : Set (EuclideanSpace ℝ (Fin n))))

def IsProjectionBody {n : ℕ}
  (K PiK : ConvexBody (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ u, u ≠ 0 →
    supportFun PiK u = ‖u‖ * (projectedArea K u).toReal

def EllipsoidSet {n : ℕ}
  (c : EuclideanSpace ℝ (Fin n))
  (P : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
  Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ w, (inner ℝ w (y - c)) ^ 2 ≤ inner ℝ w (P w)}

def IsEllipsoid {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ c : (EuclideanSpace ℝ (Fin n)),
  ∃ P : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
  K = EllipsoidSet c P ∧ (∀ v ≠ 0, inner ℝ v (P v) > 0)
  -- we need P to not be degenerate

noncomputable def petty_functional {n : ℕ}
  (K PiK : ConvexBody (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ((volume PiK.carrier) * (volume K.carrier) ^ (1 - (n : ℝ))).toReal

def petty : Prop :=
  ∀ (n : ℕ), n ≥ 3 →
    ∀ (K PiK : ConvexBody (EuclideanSpace ℝ (Fin n))),
      (Nonempty (interior K.carrier)) →
      (IsProjectionBody K PiK) →
        ∀ (L PiL : ConvexBody (EuclideanSpace ℝ (Fin n))),
          (IsEllipsoid L.carrier) →
          (IsProjectionBody L PiL) →
          petty_functional L PiL ≤ petty_functional K PiK ∧
          (petty_functional L PiL = petty_functional K PiK ↔ IsEllipsoid K.carrier)
