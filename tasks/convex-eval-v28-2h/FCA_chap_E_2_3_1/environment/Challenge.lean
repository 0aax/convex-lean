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

noncomputable def lscHull {E : Type*} [TopologicalSpace E]
  (f : E → EReal)
  (x : E) : EReal
  := Filter.liminf f (𝓝 x)

def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

noncomputable def infimalConv {E : Type*} [NormedAddCommGroup E]
  (f₁ : E → EReal)
  (f₂ : E → EReal)
  (x : E) : EReal
  := sInf {z : EReal | ∃ y : E,
  z = (f₁ y + f₂ (x - y))}

theorem FCA_chap_E_2_3_1
  (g₁ g₂ : E → EReal)
  (hg_closed_convex : InClosedConvRn g₁ ∧ InClosedConvRn g₂)
  (h_dom_nonempty : Set.Nonempty (effDom g₁ ∩
    effDom g₂))
  (g₁_ne_bot : ∀ x, ⊥ < g₁ x)
  (g₂_ne_bot : ∀ x, ⊥ < g₂ x) :
  ∀ s, (conjugate (g₁ + g₂) s) =
  (lscHull (infimalConv (conjugate g₁) (conjugate g₂)) s) := by
  sorry
