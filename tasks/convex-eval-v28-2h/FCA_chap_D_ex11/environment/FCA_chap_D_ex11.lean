import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

noncomputable def directionalDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) : EReal :=
  limUnder (𝓝[>] 0) (fun t => differenceQuotient f x d t)

def directionalSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) : Set E :=
  let f' := fun (d : E) => directionalDeriv f x d
  {s : E | ∀ d, inner ℝ s d ≤ f' d}

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_D_ex11
  (α : ℝ)
  (hα : α ∈ Set.Ioo 0 1) :
  let f₁ := fun (x : EuclideanSpace ℝ (Fin 2)) => (x 0) ^ 2
  let f₂ := fun (x : EuclideanSpace ℝ (Fin 2)) => α * (x 0) ^2 + (x 1)
  let f : EuclideanSpace ℝ (Fin 2) → EReal := fun x => max (f₁ x) (f₂ x)
  let q2 := fun (h : EuclideanSpace ℝ (Fin 2)) => ((f h) - (f 0) - (directionalDeriv f 0 h)) * ((1/2) * (‖h‖ ^ 2 : ℝ))⁻¹
  let q2_lim := fun (d : EuclideanSpace ℝ (Fin 2)) =>
    if 0 < d 1 then
      2 * α * (d 0) ^ 2 / ((d 0) ^ 2 + (d 1) ^ 2)
    else
      2 * (d 0) ^ 2 / ((d 0) ^ 2 + (d 1) ^ 2)
  (0 ∈ directionalSubdifferential f 0) ∧
  (∀ d, directionalDeriv f 0 d = (supportFunction (directionalSubdifferential f 0) d)) ∧
  (∀ d, (d ≠ 0) → (∃ (L : ℝ), (L = q2_lim d) ∧ (Filter.Tendsto (fun (t : ℝ) => q2 (t • d)) (𝓝[>] 0) (𝓝 L)))) := by
  sorry
