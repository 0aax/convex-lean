import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def IsFiniteEReal (a : EReal) : Prop :=
  ∃ r : ℝ, a = (r : EReal)

noncomputable def lipModulusRel {E : Type*} [NormedAddCommGroup E] {F : Type*} [NormedAddCommGroup F]
  (F : E → F)
  (X : Set E)
  (x_bar : E) : EReal :=
  Filter.limsup
    (fun p : E × E =>
      ((‖F p.2 - F p.1‖ / ‖p.2 - p.1‖ : ℝ) : EReal))
    (((𝓝[X] x_bar) ×ˢ (𝓝[X] x_bar)) ⊓
      Filter.principal {p : E × E | p.1 ≠ p.2})

noncomputable def lipModulus {E : Type*} [NormedAddCommGroup E] {F : Type*} [NormedAddCommGroup F]
  (F : E → F)
  (x_bar : E) : EReal :=
  lipModulusRel F Set.univ x_bar

def IsStrictlyContinuousAt {E : Type*} [NormedAddCommGroup E] {F : Type*} [NormedAddCommGroup F]
  (F : E → F)
  (x_bar : E) : Prop :=
  IsFiniteEReal (lipModulus F x_bar)

theorem RW_chap_9_10
  [Nontrivial E]
  {ι κ : Type*}
  [Fintype ι]
  [Nonempty ι]
  [Nonempty κ]
  (O : Set E)
  (f : ι → E → ℝ)
  (g : κ → E → ℝ)
  (k : E → ℝ)
  (hO_open : IsOpen O)
  (hk_usc : ∀ x ∈ O, UpperSemicontinuousWithinAt k O x)
  (hg_lip_bound : ∀ x ∈ O, ∀ (i : κ), lipModulus (g i) x ≤ (k x : EReal)) :
  ((∀ x ∈ O,
      lipModulus (fun y => sSup ((fun (i : ι) => f i y) '' Set.univ)) x
        ≤ sSup ((fun (i : ι) => lipModulus (f i) x) '' Set.univ)) ∧
    (∀ x ∈ O,
      lipModulus (fun y => sInf ((fun (i : ι) => f i y) '' Set.univ)) x
        ≤ sSup ((fun (i : ι) => lipModulus (f i) x) '' Set.univ)) ∧
    (∀ x ∈ O, (∀ (i : ι), IsStrictlyContinuousAt (f i) x) →
      IsStrictlyContinuousAt (fun y => sSup ((fun (i : ι) => f i y) '' Set.univ)) x) ∧
    (∀ x ∈ O, (∀ (i : ι), IsStrictlyContinuousAt (f i) x) →
      IsStrictlyContinuousAt (fun y => sInf ((fun (i : ι) => f i y) '' Set.univ)) x)) ∧
  ((∀ x ∈ O, BddAbove ((fun (i : κ) => g i x) '' Set.univ) →
      lipModulus (fun y => sSup ((fun (i : κ) => g i y) '' Set.univ)) x ≤ (k x : EReal)) ∧
    (∀ x ∈ O, BddBelow ((fun (i : κ) => g i x) '' Set.univ) →
      lipModulus (fun y => sInf ((fun (i : κ) => g i y) '' Set.univ)) x ≤ (k x : EReal)) ∧
    (∀ x ∈ O, BddAbove ((fun (i : κ) => g i x) '' Set.univ) →
      IsStrictlyContinuousAt (fun y => sSup ((fun (i : κ) => g i y) '' Set.univ)) x) ∧
    (∀ x ∈ O, BddBelow ((fun (i : κ) => g i x) '' Set.univ) →
      IsStrictlyContinuousAt (fun y => sInf ((fun (i : κ) => g i y) '' Set.univ)) x)) := by
  sorry
