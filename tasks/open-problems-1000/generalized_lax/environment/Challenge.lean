import Mathlib

open MvPolynomial Polynomial

-- p(x_1, ..., x_n) -> p(t - X · e)
noncomputable def restrictToLine {n : ℕ}
  (p : MvPolynomial (Fin n) ℝ)
  (t e : Fin n → ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (t i) - Polynomial.C (e i) * Polynomial.X) p

def IsHyperbolicPolynomial {n : ℕ}
  (p : MvPolynomial (Fin n) ℝ)
  (e : Fin n → ℝ) : Prop :=
  (∃ d : ℕ, p.IsHomogeneous d) ∧
  MvPolynomial.eval e p ≠ 0 ∧
  ∀ x : Fin n → ℝ,
    (restrictToLine p x e).roots.card = (restrictToLine p x e).natDegree

def HyperbolicityCone {n : ℕ}
  (p : MvPolynomial (Fin n) ℝ)
  (e : Fin n → ℝ)
  (hp_hyperbolic : IsHyperbolicPolynomial p e) :
  Set (Fin n → ℝ) :=
  {x | ∀ r ∈ (restrictToLine p x e).roots, r ≥ 0}

def generalized_lax : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (e : Fin n → ℝ) (hp_hyperbolic : IsHyperbolicPolynomial p e),
    ∃ (d : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ),
      (∀ i, (A i).IsSymm) ∧ HyperbolicityCone p e hp_hyperbolic = {x | (∑ i, x i • A i).PosSemidef}

theorem generalized_lax_POS : generalized_lax := by
  sorry

theorem generalized_lax_NEG : ¬ generalized_lax := by
  sorry
