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

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

def IsSublinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (σ : E → EReal) : Prop :=
  (InConvRn σ) ∧ IsERealPosHomogeneous σ

noncomputable def verticalSlice {E : Type*}
  (S : Set (E × ℝ)) (x : E) : Set ℝ :=
  {r : ℝ | (x, r) ∈ S}

noncomputable def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((fun r : ℝ => (r : EReal)) '' verticalSlice S x))

noncomputable def convexHullFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (g : E → EReal) : E → EReal :=
  funFromSet (convexHull ℝ (epigraph g))

noncomputable def multiInfimalConv {E : Type*} [NormedAddCommGroup E]  (m : ℕ)
  (f : ℕ → (E → EReal))
  (x : E) : EReal :=
  sInf {z : EReal |
        ∃ (y : ℕ → E),
        (x = ∑ i ∈ Finset.range m, (y i)) ∧
        (z = ∑ i ∈ Finset.range m, ((f i) (y i)))}

theorem FCA_chap_C_1_3_2_ii
  {m : ℕ}
  (σ : ℕ → (E → EReal))
  (J : ℕ → ℕ)
  (hσ_sublinear : ∀ i, i ≤ m → IsSublinear ((σ (J i))))
  (hσ_minorized : ∃ (s : E), ∃ (b : ℝ),
    ∀ i, i ≤ m → ∀ (x : E),
    (σ (J i)) x ≥ (inner ℝ s x) + b)
  (hm : 0 < m)
  (hσ_zero : ∀ i, i < m → σ (J i) 0 = 0) :
  let σJ := fun i => σ (J i)
  let σ_infconv := multiInfimalConv m σJ
  let σ_min := fun x => sInf (⋃ i ∈ Finset.range m, {(σ (J i)) x})
  let σ' := convexHullFun σ_min
  ∀ x, σ_infconv x = (σ') x := by
  sorry
