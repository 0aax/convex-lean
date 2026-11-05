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

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

def IsSublinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (σ : E → EReal) : Prop :=
  (InConvRn σ) ∧ IsERealPosHomogeneous σ

noncomputable def distOnFunctions {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (σ₁ : E → ℝ)
  (σ₂ : E → ℝ)
  (_ : IsSublinear (liftRealtoEReal σ₁))
  (_ : IsSublinear (liftRealtoEReal σ₂)) : ℝ :=
  sSup (Set.image
       (fun x => AbsoluteValue.abs (σ₁ x - σ₂ x))
       {x | ‖x‖ ≤ 1})

theorem FCA_chap_C_1_3_5
  (σk : ℕ → (E → ℝ))
  (σ : E → ℝ)
  (hσk_sublinear : ∀ k, IsSublinear (liftRealtoEReal (σk k))) :
  List.TFAE [
    (∀ x, Filter.Tendsto (fun k => σk k x)
      Filter.atTop (𝓝 (σ x))),
    (∀ (K : Set E),
      IsCompact K →
      TendstoUniformlyOn σk σ Filter.atTop K),
    (∃ (hσ_sub : IsSublinear (liftRealtoEReal σ)),
      Filter.Tendsto
        (fun k => distOnFunctions (σk k) σ
          (hσk_sublinear k) hσ_sub)
        Filter.atTop (𝓝 0))
  ] := by
  sorry
