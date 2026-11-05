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

def IsRegularNormalAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar v : E) : Prop :=
  x_bar ∈ C ∧
  ∃ (r : E → ℝ),
    r =o[𝓝 x_bar] (fun x => ‖x - x_bar‖) ∧
    ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V, x ∈ C →
      inner ℝ v (x - x_bar) ≤ r x

def regularNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar : E) : Set E :=
  {v | IsRegularNormalAt C x_bar v}

def IsNormalAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar v : E) : Prop :=
  ∃ (x : ℕ → E), ∃ (vseq : ℕ → E),
    Filter.Tendsto x Filter.atTop (𝓝 x_bar) ∧
    Filter.Tendsto vseq Filter.atTop (𝓝 v) ∧
    (∀ n, vseq n ∈ regularNormalCone C (x n))

def normalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar : E) : Set E :=
  {v | IsNormalAt C x_bar v}

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

def IsSublinearRW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (0 ∈ effDom f ∧ IsERealPosHomogeneous f) ∧
  ConvexEReal f

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem RW_chap_8_25
  (h : E → EReal)
  (D : Set E)
  (w : E)
  (hh_proper : IsProper h)
  (hh_lsc : LowerSemicontinuous h)
  (hh_sublinear : IsSublinearRW h)
  (hD_rep : ∀ (w : E), h w = supportFunction D w)
  (hD_closed : IsClosed D)
  (hD_convex : Convex ℝ D)
  (hw : w ∈ effDom h) :
  subdifferential h w =
    {v : E | v ∈ D ∧ supportFunction D w = (((inner ℝ v w) : ℝ) : EReal)} ∧
  subdifferential h w =
    {v : E | v ∈ D ∧ w ∈ normalCone D v} := by
  sorry
