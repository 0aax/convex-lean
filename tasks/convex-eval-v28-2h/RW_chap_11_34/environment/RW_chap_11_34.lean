import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def setLiminf {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) : Set X :=
  {u | ∀ V ∈ 𝓝 u, ∀ᶠ n in Filter.atTop, ∃ v ∈ A n, v ∈ V}

def setLimsup {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) : Set X :=
  {u | ∀ V ∈ 𝓝 u, ∃ᶠ n in Filter.atTop, ∃ v ∈ A n, v ∈ V}

def epiLiminfSet {E : Type*} [NormedAddCommGroup E]
  (fseq : ℕ → E → EReal) : Set (E × ℝ) :=
  setLimsup (fun n => epigraph (fseq n))

def epiLimsupSet {E : Type*} [NormedAddCommGroup E]
  (fseq : ℕ → E → EReal) : Set (E × ℝ) :=
  setLiminf (fun n => epigraph (fseq n))

def EpiConverges {E : Type*} [NormedAddCommGroup E]
  (fseq : ℕ → E → EReal)
  (f : E → EReal) : Prop :=
  epiLiminfSet fseq = epigraph f ∧
  epiLimsupSet fseq = epigraph f

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

def IsMinorizedAt {E : Type*}
  (C : Set (E × ℝ)) (x : E) : Prop :=
  let K := {r : ℝ | ∃ (z : E × ℝ), (z ∈ C) ∧ (x = z.1) ∧ (r = z.2)}
  ∃ (k₀ : ℝ), ∀ r ∈ K, r ≥ k₀

def EpiSetNoNegInf {E : Type*}
  (S : Set (E × ℝ)) : Prop :=
  ∀ x : E, IsMinorizedAt S x

theorem RW_chap_11_34
  (fseq : ℕ → E → EReal)
  (f : E → EReal)
  (hfseq_proper : ∀ (ν : ℕ), IsProper (fseq ν))
  (hfseq_lsc : ∀ (ν : ℕ), LowerSemicontinuous (fseq ν))
  (hfseq_convex : ∀ (ν : ℕ), ConvexEReal (fseq ν))
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f)
  (hf_convex : ConvexEReal f) :
  (EpiConverges fseq f ↔
    EpiConverges
      (fun (ν : ℕ) => conjugate (fseq ν))
      (conjugate f)) ∧
  ((EpiSetNoNegInf (epiLiminfSet fseq) ∧
      (∃ (B : Set E), Bornology.IsBounded B ∧
        Filter.limsup
          (fun (ν : ℕ) => sInf ((fun (x : E) => fseq ν x) '' B))
          Filter.atTop < ⊤)) →
    ((epiLiminfSet fseq ⊆ epigraph f) ↔
      (epigraph (conjugate f) ⊆
        epiLimsupSet (fun (ν : ℕ) => conjugate (fseq ν)))) ∧
    ((epigraph f ⊆ epiLimsupSet fseq) ↔
      (epiLiminfSet (fun (ν : ℕ) => conjugate (fseq ν)) ⊆
        epigraph (conjugate f)))) := by
  sorry
