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

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

noncomputable def IsOneCoerciveFun {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ C : ℝ, ∀ᶠ x in Filter.comap norm Filter.atTop, (C : EReal) ≤ (norm x)⁻¹ * (f x)

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_4_1_3
  (f : E → ℝ)
  (hf_convex : InConvRn (liftRealtoEReal f))
  (hf_strict : StrictConvexOn ℝ Set.univ f)
  (hf_diff : Differentiable ℝ f)
  (hf_coercive : IsOneCoerciveFun (liftRealtoEReal f)) :
  (∀ s, conjugate (liftRealtoEReal f) s < ⊤) ∧
  (∃ (g : E → ℝ),
    (∀ s, (conjugate (liftRealtoEReal f) s) = (g s : EReal)) ∧
    (StrictConvexOn ℝ Set.univ g) ∧
    (Differentiable ℝ g) ∧
    (IsOneCoerciveFun (liftRealtoEReal g))) ∧
  ((Function.Bijective (gradient f)) ∧
    (Continuous (gradient f)) ∧
    (Continuous (Function.invFun (gradient f)))) ∧
  (∀ s, (conjugate (liftRealtoEReal f) s) =
  (inner ℝ s (Function.invFun (gradient f) s) -
  f (Function.invFun (gradient f) s) : ℝ)) := by
  sorry
