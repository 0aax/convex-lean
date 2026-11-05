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

def proximalMapping {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (lam : ℝ)
  (x : E) : Set E :=
  {w : E | f w < ⊤ ∧ ∀ z, f w + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 ≤ f z + (2 * lam)⁻¹ * ‖z - x‖ ^ 2}

def idMap {E : Type*} (x : E) : Set E := {x}

def IsMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

def IsMaximalMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  IsMonotone T ∧
  ∀ (x_hat v_hat : E),
    v_hat ∉ T x_hat →
    ∃ (x_tilde v_tilde : E),
      v_tilde ∈ T x_tilde ∧
      inner ℝ (v_hat - v_tilde) (x_hat - x_tilde) < 0

def IsNonexpansive {E : Type*} [NormedAddCommGroup E]
  (S : E → Set E) : Prop :=
  ∀ (z₀ z₁ w₀ w₁ : E), w₀ ∈ S z₀ → w₁ ∈ S z₁ →
    ‖w₁ - w₀‖ ≤ ‖z₁ - z₀‖

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

def IsSingleValued {E : Type*}
  (S : E → Set E) : Prop :=
  ∀ z, ∃! x, x ∈ S z

def addMap {E : Type*} [NormedAddCommGroup E]
  (S T : E → Set E) : E → Set E :=
  fun x => {z | ∃ u ∈ S x, ∃ v ∈ T x, z = u + v}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

def invMap {E : Type*}
  (T : E → Set E) : E → Set E :=
  fun y => {x | y ∈ T x}

noncomputable def proxPerturbedFun {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) (lam : ℝ) : E → EReal :=
  fun x => f x + (((2 * lam)⁻¹ * ‖x‖ ^ 2 : ℝ) : EReal)

def smulMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ℝ) (T : E → Set E) : E → Set E :=
  fun x => {v | ∃ w ∈ T x, v = a • w}

def subMap {E : Type*} [NormedAddCommGroup E]
  (S T : E → Set E) : E → Set E :=
  fun x => {z | ∃ u ∈ S x, ∃ v ∈ T x, z = u - v}

theorem RW_chap_12_19
  (f : E → EReal)
  (lam : ℝ)
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f)
  (h_lam : 0 < lam) :
  IsMonotone (proximalMapping f lam) ∧
  (ConvexEReal f → IsMaximalMonotone (proximalMapping f lam)) ∧
  (ConvexEReal f → IsNonexpansive (proximalMapping f lam)) ∧
  (ConvexEReal f → IsSingleValued (proximalMapping f lam)) ∧
  (lam = 1 →
    ConvexEReal f →
    subMap idMap (proximalMapping f lam) =
      proximalMapping (conjugate f) 1) ∧
  (lam = 1 →
    ConvexEReal f →
    ∃ (hP : IsSingleValued (proximalMapping f 1)),
    ∃ (hQ : IsSingleValued (proximalMapping (conjugate f) 1)),
      let Pfun : E → E := fun z => Classical.choose (hP z)
      let Qfun : E → E := fun z => Classical.choose (hQ z)
      ∀ z x v,
        (Pfun z, Qfun z) = (x, v) ↔
        z = x + v ∧ v ∈ subdifferential f x) ∧
  List.TFAE [
    IsMaximalMonotone (proximalMapping f lam),
    ConvexEReal (proxPerturbedFun f lam),
    IsMonotone (addMap idMap (smulMap lam (subdifferential f)))
  ] ∧
  (ConvexEReal (proxPerturbedFun f lam) →
    proximalMapping f lam =
      invMap (addMap idMap (smulMap lam (subdifferential f)))) ∧
  (ConvexEReal (proxPerturbedFun f lam) →
    ∀ (μ : ℝ), 0 < μ → μ < lam →
      IsSingleValued (proximalMapping f μ) ∧
      ∀ (x y : E), ∀ u ∈ proximalMapping f μ x, ∀ v ∈ proximalMapping f μ y,
        ‖u - v‖ ≤ (lam / (lam - μ)) * ‖x - y‖) := by
  sorry
