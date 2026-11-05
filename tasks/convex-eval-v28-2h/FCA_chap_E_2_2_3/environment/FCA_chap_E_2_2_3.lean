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

theorem FCA_chap_E_2_2_3
  (g : F → EReal)
  (y₀ : F)
  (A₀ : E →ₗ[ℝ] F)
  (hg_closed_convex : InClosedConvRn g)
  (hg_nondegenerate : IsNondegenerate g)
  (h_zero : 0 ∈ effDom g)
  (h_nonempty_domain : Set.Nonempty ((Set.image (fun v => A₀ v + y₀) Set.univ) ∩
    (intrinsicInterior ℝ (effDom g)))) :
  let gA := fun x => g (A₀ x + y₀)
  let A_star_g_star := imageFun A₀.adjoint (conjugate g)
  ∀ s ∈ effDom ((conjugate gA)), ∃ p',
  (A₀.adjoint p' = s) ∧
  ((conjugate g p') - inner ℝ p' y₀ =
  imageFun A₀.adjoint (fun p => conjugate g p - inner ℝ p y₀) s) ∧
  ((conjugate gA s) = (conjugate g p') - inner ℝ p' y₀) := by
  sorry
