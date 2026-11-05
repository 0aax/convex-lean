import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsPointedCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Prop :=
  (0 : E) ∈ K ∧
  ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K

noncomputable def distToSetEReal {E : Type*} [NormedAddCommGroup E]
  (x : E) (A : Set E) : EReal :=
  sInf ((fun y : E => ((‖x - y‖ : ℝ) : EReal)) '' A)

noncomputable def pompeiuHausdorffDistOn {E : Type*} [NormedAddCommGroup E]
  (ρ : ℝ)
  (C D : Set E) : EReal :=
  sSup
    ((fun x : E =>
      max
        (distToSetEReal x C - distToSetEReal x D)
        (distToSetEReal x D - distToSetEReal x C)) ''
      Metric.closedBall (0 : E) ρ)

noncomputable def integratedSetDistance {E : Type*} [NormedAddCommGroup E]
  (C D : Set E) : ℝ :=
  ∫ ρ in Set.Ioi (0 : ℝ),
    (pompeiuHausdorffDistOn ρ C D).toReal * Real.exp (-ρ)

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

theorem RW_chap_11_36
    (K₁ K₂ : Set E)
    (hK₁_closed : IsClosed K₁)
    (hK₂_closed : IsClosed K₂)
    (hK₁_cone : IsPointedCone K₁)
    (hK₂_cone : IsPointedCone K₂)
    (hK₁_convex : Convex ℝ K₁)
    (hK₂_convex : Convex ℝ K₂) :
    integratedSetDistance K₁ K₂ =
      integratedSetDistance (polarCone K₁) (polarCone K₂) := by
  sorry
