import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def gaugeFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x : E) : EReal :=
  sInf {l : EReal | ∃ (l' : ℝ),
                        (l = (l' : EReal)) ∧
                        (l' > 0) ∧
                        (∃ y ∈ C, (x = l' • y))}

noncomputable def infimalConv {E : Type*} [NormedAddCommGroup E]
  (f₁ : E → EReal)
  (f₂ : E → EReal)
  (x : E) : EReal
  := sInf {z : EReal | ∃ y : E,
  z = (f₁ y + f₂ (x - y))}

theorem FCA_chap_C_ex4
  (C₁ C₂ : Set E)
  (hC₁_closed : IsClosed C₁) (hC₁_convex : Convex ℝ C₁) (hC₁_origin : 0 ∈ C₁)
  (hC₂_closed : IsClosed C₂) (hC₂_convex : Convex ℝ C₂) (hC₂_origin : 0 ∈ C₂)
  (hC_int_origin : 0 ∈ interior C₁ ∨ 0 ∈ interior C₂) :
  let f := gaugeFun C₁
  let g := gaugeFun C₂
  let fg := fun x => infimalConv f g x
  (∃ C : Set E,
    IsClosed C ∧ Convex ℝ C ∧ 0 ∈ C ∧
    ∀ x, fg x = (gaugeFun C x)) ∧
  ({x | fg x < (1 : EReal)} =
    convexHull ℝ ({x | f x < 1} ∪ {x | g x < 1})) := by
  sorry
