import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_ex6 (p : ℝ)
  (fp : ℝ → (EuclideanSpace ℝ (Fin 1) → EReal))
  (gp : ℝ → (EuclideanSpace ℝ (Fin 1) → EReal))
  (hp : ℝ → (EuclideanSpace ℝ (Fin 1) → EReal))
  (hp_pos : p > 0)
  (h_eq : ∀ r > 0, ∀ (x : EuclideanSpace ℝ (Fin 1)),
            (x 0 ≥ 0) →
            ((fp r x = gp r x) ∧ (gp r x = hp r x) ∧
            ((fp r x) = (((r + 1)⁻¹ * (x 0) ^ (r + 1) : ℝ) : EReal))))
  (h_ow : ∀ r > 0, ∀ (x : EuclideanSpace ℝ (Fin 1)),
            (x 0 < 0) →
            ((fp r x = ⊤) ∧ (gp r x = 0) ∧
            ((hp r x) = (((r + 1)⁻¹ * (-1 * (x 0)) ^ (r + 1) : ℝ) : EReal))))
  (fp_ne_bot : ∀ x₁ x₂, ⊥ < fp x₁ x₂) (gp_ne_bot : ∀ x₁ x₂, ⊥ < gp x₁ x₂) (hp_ne_bot : ∀ x₁ x₂, ⊥ < hp x₁ x₂) :
  let fp_conj := conjugate (fp p)
  let gp_conj := conjugate (gp p)
  let hp_conj := conjugate (hp p)
  (∀ x, fp_conj x = gp (p⁻¹) x) ∧
  (∀ x, gp_conj x = fp (p⁻¹) x) ∧
  (∀ x, hp_conj x = hp (p⁻¹) x) := by
  sorry
