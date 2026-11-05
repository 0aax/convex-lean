import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def multiInfimalConv {E : Type*} [NormedAddCommGroup E]  (m : ℕ)
  (f : ℕ → (E → EReal))
  (x : E) : EReal :=
  sInf {z : EReal |
        ∃ (y : ℕ → E),
        (x = ∑ i ∈ Finset.range m, (y i)) ∧
        (z = ∑ i ∈ Finset.range m, ((f i) (y i)))}

theorem FCA_chap_E_ex7 (m : ℕ) (p : ℝ)
  (r : ℕ → ℝ)
  (a : ℕ → ℝ)
  (f : ℕ → (EuclideanSpace ℝ (Fin 1) → EReal))
  (hp : p > 0) (hm : m > 0)
  (hr : ∀ i ∈ Finset.range m, r i > 0)
  (hf : ∀ i ∈ Finset.range m, ∀ (x : EuclideanSpace ℝ (Fin 1)),
        (f i x) = ((((p + 1) * (r i) ^ p)⁻¹ * (abs (x 0 - (a i)) ^ (p + 1)) : ℝ) : EReal))
  (f_ne_bot : ∀ x₁ x₂, ⊥ < f x₁ x₂) :
  let f_infconv := multiInfimalConv m f
  let r_sum := ∑ i ∈ Finset.range m, r i
  let a_sum := ∑ i ∈ Finset.range m, a i
  ∀ (x : EuclideanSpace ℝ (Fin 1)),
  f_infconv x = ((((p + 1) * r_sum ^ p)⁻¹ * (abs (x 0 - a_sum)) ^ (p + 1) : ℝ) : EReal) := by
  sorry
