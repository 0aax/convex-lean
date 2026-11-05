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

def proximalMapping {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (lam : ℝ)
  (x : E) : Set E :=
  {w : E | f w < ⊤ ∧ ∀ z, f w + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 ≤ f z + (2 * lam)⁻¹ * ‖z - x‖ ^ 2}

def graph {E : Type*} (T : E → Set E) : Set (E × E) :=
  {p | p.2 ∈ T p.1}

def graphSetLiminf {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) : Set (E × E) :=
  setLiminf (fun n => graph (Tseq n))

def graphSetLimsup {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) : Set (E × E) :=
  setLimsup (fun n => graph (Tseq n))

def GraphicallyConverges {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) (T : E → Set E) : Prop :=
  graphSetLimsup Tseq = graph T ∧
  graphSetLiminf Tseq = graph T

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

def pLiminf {E : Type*} [NormedAddCommGroup E] (Tseq : ℕ → E → Set E) : E → Set E :=
  fun x => setLiminf (fun n => Tseq n x)

def pLimsup {E : Type*} [NormedAddCommGroup E] (Tseq : ℕ → E → Set E) : E → Set E :=
  fun x => setLimsup (fun n => Tseq n x)

def PointwiseMapConverges {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) (T : E → Set E) : Prop :=
  pLimsup Tseq = T ∧ pLiminf Tseq = T

def εEnlarge {E : Type*} [NormedAddCommGroup E] (A : Set E) (ε : ℝ) : Set E :=
  {y | ∃ z ∈ A, dist y z < ε}

def UniformlyConvergesOn {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E)
  (T : E → Set E)
  (X : Set E) : Prop :=
  ∀ ε > (0 : ℝ), ∀ ρ > (0 : ℝ),
    ∃ N : ℕ,
      ∀ n ≥ N, ∀ x ∈ X,
        (Tseq n x ∩ Metric.ball 0 ρ) ⊆ εEnlarge (T x) ε ∧
        (T x ∩ Metric.ball 0 ρ) ⊆ εEnlarge (Tseq n x) ε

def UniformlyConvergesOnBounded {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E)
  (T : E → Set E) : Prop :=
  ∀ R > (0 : ℝ),
    UniformlyConvergesOn Tseq T {x | ‖x‖ ≤ R}

def UniformlyConvergesOnBoundedEReal {E : Type*} [NormedAddCommGroup E]
  (gseq : ℕ → E → EReal)
  (g : E → EReal) : Prop :=
  ∀ R > (0 : ℝ), ∀ ε > (0 : ℝ),
    ∃ (N : ℕ), ∀ n ≥ N, ∀ x : E,
      ‖x‖ ≤ R →
        g x - (ε : EReal) ≤ gseq n x ∧
        gseq n x ≤ g x + (ε : EReal)

noncomputable def moreauEnvelope {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (lam : ℝ)
  (x : E) : EReal :=
  sInf {v : EReal | ∃ w, v = f w + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 }

theorem RW_chap_12_35
  (fseq : ℕ → E → EReal)
  (f : E → EReal)
  (lam : ℝ)
  (h_lam : 0 < lam)
  (hfseq_proper : ∀ n, IsProper (f := fseq n))
  (hf_proper : IsProper (f := f))
  (hfseq_lsc : ∀ n, LowerSemicontinuous (f := fseq n))
  (hf_lsc : LowerSemicontinuous (f := f))
  (hfseq_convex : ∀ n, ConvexEReal (f := fseq n))
  (hf_convex : ConvexEReal (f := f)) :
  List.TFAE [
    EpiConverges fseq f,
    GraphicallyConverges
      (fun n => subdifferential (f := fseq n))
      (subdifferential (f := f)) ∧
    ∃ (xbar : E), ∃ (vbar : E),
      ∃ (xseq : ℕ → E), ∃ (vseq : ℕ → E),
        Filter.Tendsto xseq Filter.atTop (𝓝 xbar) ∧
        Filter.Tendsto vseq Filter.atTop (𝓝 vbar) ∧
        (∀ n, vseq n ∈ subdifferential (f := fseq n) (xseq n)) ∧
        vbar ∈ subdifferential (f := f) xbar ∧
        Filter.Tendsto (fun n => fseq n (xseq n)) Filter.atTop (𝓝 (f xbar)),
    PointwiseMapConverges
      (fun n => proximalMapping (f := fseq n) lam)
      (proximalMapping (f := f) lam) ∧
    ∃ (xtilde : E), ∃ (xseq : ℕ → E),
      Filter.Tendsto xseq Filter.atTop (𝓝 xtilde) ∧
      Filter.Tendsto
        (fun n => moreauEnvelope (f := fseq n) lam (xseq n))
        Filter.atTop
        (𝓝 (moreauEnvelope (f := f) lam xtilde))] ∧
  (EpiConverges fseq f →
    ∀ (lamseq : ℕ → ℝ),
      Filter.Tendsto lamseq Filter.atTop (𝓝 lam) →
      (∀ n, 0 < lamseq n) →
        UniformlyConvergesOnBounded
          (fun n => proximalMapping (f := fseq n) (lamseq n))
          (proximalMapping (f := f) lam) ∧
        UniformlyConvergesOnBoundedEReal
          (fun n => moreauEnvelope (f := fseq n) (lamseq n))
          (moreauEnvelope (f := f) lam)) := by
  sorry
