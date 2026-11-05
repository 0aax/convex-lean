import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

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

def linearRange {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (A : F →ₗ[ℝ] E) : Set E
  := {z | ∃ y, A y = z}

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

noncomputable def imageFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (A : F →ₗ[ℝ] E)
  (g : F → EReal)
  (x : E) : EReal :=
  sInf (Set.image g {y : F | A y = x})

theorem FCA_chap_E_2_2_2
  (g : F → EReal)
  (A₀ : E →ₗ[ℝ] F)
  (hg_closed_convex : InClosedConvRn g)
  (hg_nondegenerate : IsNondegenerate g)
  (h_zero : 0 ∈ effDom g)
  (h_dom_nonempty : Set.Nonempty
    (linearRange A₀ ∩ intrinsicInterior ℝ (effDom g))) :
  let gA₀ := fun x => g (A₀ x)
  let A_star_g_star := imageFun A₀.adjoint (conjugate g)
  (∀ s, conjugate gA₀ s = A_star_g_star s) ∧
  (∀ s ∈ effDom ((conjugate gA₀)), ∃ p',
    (A₀.adjoint p' = s) ∧
    ((conjugate g p') =
      sInf (Set.image (conjugate g) {p | A₀.adjoint p = s})) ∧
    ((conjugate gA₀ s) = (A_star_g_star s)) ∧
    ((A_star_g_star s) = (conjugate g p'))) := by
  sorry
