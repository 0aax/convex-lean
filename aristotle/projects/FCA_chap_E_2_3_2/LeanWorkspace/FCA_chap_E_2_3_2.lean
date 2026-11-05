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

def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

noncomputable def infimalConv {E : Type*} [NormedAddCommGroup E]
  (f₁ : E → EReal)
  (f₂ : E → EReal)
  (x : E) : EReal
  := sInf {z : EReal | ∃ y : E,
  z = (f₁ y + f₂ (x - y))}

theorem FCA_chap_E_2_3_2
  (g₁ g₂ : E → EReal)
  (hg_closed_convex : InClosedConvRn g₁ ∧ InClosedConvRn g₂)
  (hg_nondegenerate : IsNondegenerate g₁ ∧ IsNondegenerate g₂)
  (h_ri_intersect : Set.Nonempty (intrinsicInterior ℝ (effDom g₁) ∩
    intrinsicInterior ℝ (effDom g₂))) :
  let h := fun p q => conjugate g₁ p + conjugate g₂ q
  (∀ s, (conjugate (g₁ + g₂) s) =
  (infimalConv (conjugate g₁) (conjugate g₂) s)) ∧
  (∀ s ∈ effDom ((conjugate (g₁ + g₂))), ∃ p' q',
  (p' + q' = s) ∧
  ((h p' q') = sInf {v | ∃ p q, (p + q = s) ∧ (h p q = v)}) ∧
  ((h p' q') = infimalConv (conjugate g₁) (conjugate g₂) s) ∧
  (h p' q' = conjugate (g₁ + g₂) s)) := by
  sorry
