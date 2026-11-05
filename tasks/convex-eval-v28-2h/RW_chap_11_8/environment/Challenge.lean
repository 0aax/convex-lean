import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsRegularSubgradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar v : E) : Prop :=
  (⊥ < f x_bar) ∧ (f x_bar < ⊤) ∧
  ∃ (r : E → ℝ),
    r =o[𝓝 x_bar] (fun x => ‖x - x_bar‖) ∧
    ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V,
      f x_bar + (((inner ℝ v (x - x_bar) + r x) : ℝ) : EReal) ≤ f x

def IsSubgradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x_bar v : E) : Prop :=
  (⊥ < f x_bar) ∧ (f x_bar < ⊤) ∧
  ∃ (x : ℕ → E), ∃ (vseq : ℕ → E),
    Filter.Tendsto x Filter.atTop (𝓝 x_bar) ∧
    Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f x_bar)) ∧
    Filter.Tendsto vseq Filter.atTop (𝓝 v) ∧
    (∀ i, IsRegularSubgradientAt f (x i) (vseq i))

def subdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) (x_bar : E) : Set E :=
  {v | IsSubgradientAt f x_bar v}

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def IsDifferentiableAtWithGradientEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → EReal)
  (x_bar grad : E) : Prop :=
  ∃ g : E → ℝ,
    (∃ U ∈ 𝓝 x_bar, ∀ x ∈ U, f x = (g x : EReal)) ∧
    DifferentiableAt ℝ g x_bar ∧
    gradient g x_bar = grad

def sublevelSet {E : Type*}
  (r : ℝ) (f : E → EReal) :
  Set E :=
  {x : E | f x ≤ r}

def IsLevelBounded {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ α : ℝ, Bornology.IsBounded (sublevelSet α f)

noncomputable def IsOneCoerciveFun {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ C : ℝ, ∀ᶠ x in Filter.comap norm Filter.atTop, (C : EReal) ≤ (norm x)⁻¹ * (f x)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem RW_chap_11_8
  (f : E → EReal)
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f)
  (hf_convex : ConvexEReal f) :
  ((sInf (Set.range f) = - conjugate f (0 : E)) ∧
    ({x : E | ∀ (y : E), f x ≤ f y} =
      subdifferential (conjugate f) (0 : E))) ∧
  (∀ (x_bar : E),
    ({x : E | ∀ (y : E), f x ≤ f y} = {x_bar} ↔
      IsDifferentiableAtWithGradientEReal
        (conjugate f)
        (0 : E)
        x_bar)) ∧
  (IsLevelBounded f ↔
    (0 : E) ∈ interior (effDom (conjugate f))) ∧
  (IsOneCoerciveFun f ↔
    effDom (conjugate f) = Set.univ) := by
  sorry
