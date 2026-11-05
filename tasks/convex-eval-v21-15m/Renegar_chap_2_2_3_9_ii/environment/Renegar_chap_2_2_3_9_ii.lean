import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def hessianOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (x : E)
  : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x

noncomputable def localInnerProd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (x u v : E) : ℝ :=
  inner ℝ u (hessianOperator f x v)

noncomputable def localNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x v : E) : ℝ :=
  Real.sqrt (localInnerProd f x v v)

lemma hessianOperator_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (Df : Set E)
  (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd (f := f) x v v)
  (x : E)
  (hx : x ∈ Df) : Function.Injective (hessianOperator f x) := by
  intro u v huv
  by_contra h
  have hne : u - v ≠ 0 := sub_ne_zero.mpr h
  have hpd := h_pd x hx (u - v) hne
  simp only [localInnerProd] at hpd
  have : hessianOperator f x (u - v) = 0 := by rw [map_sub, huv, sub_self]
  rw [this] at hpd
  simp at hpd

noncomputable def hessianLinearEquiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (x : E)
  (hx : x ∈ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) : E ≃L[ℝ] E := by
  have hinj := hessianOperator_injective f Df h_Df_pd x hx
  exact ContinuousLinearEquiv.ofBijective (hessianOperator f x)
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hinj))

def IsCone {E : Type*} [AddCommMonoid E] [SMul ℝ E]
  (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ (s : ℝ), s > 0 → s • x ∈ K

def IsLogarithmicallyHomogeneousWith {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (v : ℝ) : Prop :=
  ∃ (K : Set E), (Df = interior K) ∧ (IsCone K) ∧
    (∀ x ∈ interior K, ∀ t > 0,
      f (t • x) = f x - v * (Real.log t))

noncomputable def localBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (x v : E) (r : ℝ) : Set E :=
  {y : E | localNorm f x (y - v) < r}

def IsSelfConcordantLocalNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (Df : Set E)
  : Prop :=
  ∀ x ∈ Df,
    (localBall (f := f) x x 1 ⊆ Df) ∧
    (∀ y, y ∈ localBall (f := f) x x 1 →
      (∀ v ≠ 0,
        (1 : ℝ) - (localNorm (f := f) x (y - x)) ≤
          (localNorm (f := f) x v)⁻¹ * (localNorm (f := f) y v) ∧
        (localNorm (f := f) x v)⁻¹ * (localNorm (f := f) y v) ≤
          (1 - (localNorm (f := f) x (y - x)))⁻¹))

noncomputable def localGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x y : E)
  (hx : x ∈ Df) : E :=
  (hessianLinearEquiv (f := f) (Df := Df) (h_Df_pd := h_Df_pd) x hx).symm (gradient f y)

noncomputable def barrierIntegrand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E) (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x : Df) : ℝ :=
  (localNorm f x.1
    (localGradient f Df h_Df_pd x.1 x.1 x.2)) ^ 2

def IsSCBarrier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) : Prop :=
  IsSelfConcordantLocalNorm f Df ∧
  BddAbove (Set.range fun x : Df =>
    barrierIntegrand (f := f) (Df := Df) h_Df_pd x)

noncomputable def barrierParameter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) : ℝ :=
  sSup ((Set.range fun x : Df =>
    barrierIntegrand f Df h_Df_pd x))

def IsLogarithmicallyHomogeneousBarrier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ)
  (Df : Set E)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) : Prop :=
  IsSCBarrier f Df h_Df_pd ∧
  IsLogarithmicallyHomogeneousWith (f := f) (Df := Df) (barrierParameter f Df h_Df_pd)

theorem Renegar_chap_2_2_3_9_ii [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x : E)
  (hx : x ∈ Df)
  (hf_log_homo_barrier : IsLogarithmicallyHomogeneousBarrier f Df h_Df_pd) :
  (∀ t : ℝ, 0 < t →
    hessianOperator f (t • x) = (t ^ 2)⁻¹ • hessianOperator f x) ∧
  (localGradient f Df h_Df_pd x x hx = (-1 : ℝ) • x) ∧
  (localNorm f x (localGradient f Df h_Df_pd x x hx) =
    Real.sqrt (barrierParameter f Df h_Df_pd)) := by
  sorry
