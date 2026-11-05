import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsLipschitzEReal {X : Type*} [MetricSpace X]
  (T : X → EReal)
  (A : Set X)
  (β : ℝ) : Prop :=
  (0 ≤ β) ∧
  (∀ x ∈ A, T x ≠ ⊤ ∧ T x ≠ ⊥) ∧
  (∀ (x y : X),
    x ∈ A → y ∈ A →
      ‖(T x).toReal - (T y).toReal‖ ≤ β • (dist x y))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem RW_chap_9_12
  (C : Set E)
  (f : E → EReal)
  (κ : ℝ)
  (hC_ne : Set.Nonempty C)
  (hf_lip : IsLipschitzEReal f C κ) :
  let fbar : E → EReal :=
    fun x => sInf ((fun w : E => f w + ((κ * ‖x - w‖ : ℝ) : EReal)) '' C)
  ((∀ x ∈ C, fbar x = f x) ∧
    IsLipschitzEReal fbar Set.univ κ) ∧
  (sInf (f '' C) = sInf (fbar '' Set.univ)) ∧
  ({x : E | x ∈ C ∧ ∀ y ∈ C, f x ≤ f y} =
    C ∩ {x : E | ∀ y : E, fbar x ≤ fbar y}) := by
  sorry
