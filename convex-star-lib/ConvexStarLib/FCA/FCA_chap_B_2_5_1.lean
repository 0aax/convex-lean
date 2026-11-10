import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_5_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_5_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_5_1`, so the main result is `FCA_chap_B_2_5_1.FCA_chap_B_2_5_1`.
-/

namespace FCA_chap_B_2_5_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_2_5_1
  (g : E → EReal)
  (hg_nondegenerate : IsNondegenerate g)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  let f₁ := convexHullFun g
  let f₂ := fun x => sSup {z : EReal | ∃ (h : E → EReal),
                                          InConvRn h ∧ Minorizes h g ∧ z = h x}
  let f₃ := fun x => sInf (⋃ k, {z | ∃ (α : EuclideanSpace ℝ (Fin k))
                                    (x₀ : Fin k → E),
                                    α.ofLp ∈ probSimplex k ∧ (∀ j, x₀ j ∈ effDom g) ∧
                                    x = ∑ j, α j • x₀ j ∧
                                    z = ∑ j, ((α j : ℝ) : EReal) * g (x₀ j)})
  InConvRn f₁ ∧ InConvRn f₂ ∧ InConvRn f₃ ∧
    ∀ x, f₁ x = f₂ x ∧ f₂ x = f₃ x := by
  intro f₁ f₂ f₃
  -- the coercion `ℝ → EReal` commutes with finite sums
  have hcoe : ∀ {ι : Type} (t : Finset ι) (f : ι → ℝ),
      ((∑ i ∈ t, f i : ℝ) : EReal) = ∑ i ∈ t, (f i : EReal) := by
    intro ι t f
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]
  -- basic properties of `funFromSet`
  have hle : ∀ {S : Set (E × ℝ)} {x : E} {r : ℝ}, (x, r) ∈ S → funFromSet S x ≤ r :=
    fun h => sInf_le ⟨_, h, rfl⟩
  have hge : ∀ {S : Set (E × ℝ)} {x : E} {z : EReal},
      (∀ r : ℝ, (x, r) ∈ S → z ≤ r) → z ≤ funFromSet S x := by
    intro S x z h
    apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    exact h r hr
  -- the lower boundary function of a convex set is convex
  have hcvx : ∀ {S : Set (E × ℝ)}, Convex ℝ S → ConvexEReal (funFromSet S) := by
    intro S hS p hp q hq a b ha hb hab
    change funFromSet S p.1 ≤ (p.2 : EReal) at hp
    change funFromSet S q.1 ≤ (q.2 : EReal) at hq
    change funFromSet S (a • p + b • q).1 ≤ ((a • p + b • q).2 : EReal)
    apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    induction c using EReal.rec with
    | bot => exact absurd hc not_lt_bot
    | top => exact le_top
    | coe c =>
      have hc' : (a • p + b • q).2 < c := EReal.coe_lt_coe_iff.1 hc
      have h1 : funFromSet S p.1 < ((p.2 + (c - (a • p + b • q).2) : ℝ) : EReal) :=
        lt_of_le_of_lt hp (EReal.coe_lt_coe_iff.2 (by linarith))
      have h2 : funFromSet S q.1 < ((q.2 + (c - (a • p + b • q).2) : ℝ) : EReal) :=
        lt_of_le_of_lt hq (EReal.coe_lt_coe_iff.2 (by linarith))
      obtain ⟨_, ⟨r, hr, rfl⟩, hr'⟩ := sInf_lt_iff.1 h1
      obtain ⟨_, ⟨s, hs, rfl⟩, hs'⟩ := sInf_lt_iff.1 h2
      have hr'' := EReal.coe_lt_coe_iff.1 hr'
      have hs'' := EReal.coe_lt_coe_iff.1 hs'
      have hmem : ((a • p + b • q).1, a * r + b * s) ∈ S := by
        have h := hS (show (p.1, r) ∈ S from hr) (show (q.1, s) ∈ S from hs) ha hb hab
        have e : a • ((p.1, r) : E × ℝ) + b • ((q.1, s) : E × ℝ)
            = ((a • p + b • q).1, a * r + b * s) := by
          ext <;> simp
        rwa [e] at h
      calc funFromSet S (a • p + b • q).1 ≤ ((a * r + b * s : ℝ) : EReal) := hle hmem
        _ ≤ c := by
          apply EReal.coe_le_coe_iff.2
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hr'' hs'' ⊢
          have hb' : b = 1 - a := by linarith
          subst hb'
          nlinarith [mul_le_mul_of_nonneg_left hr''.le ha, mul_le_mul_of_nonneg_left hs''.le hb]
  obtain ⟨⟨x₀, hx₀⟩, ⟨s, b, hsb⟩⟩ := hg_nondegenerate
  have hconv : Convex ℝ (convexHull ℝ (epigraph g)) := convex_convexHull ℝ _
  -- `f₁` minorizes `g`
  have hf₁g : Minorizes f₁ g := by
    intro x
    by_cases hx : g x = ⊤
    · rw [hx]; exact le_top
    · have hgx : ((g x).toReal : EReal) = g x := EReal.coe_toReal hx (g_ne_bot x).ne'
      rw [← hgx]
      apply hle
      apply subset_convexHull
      show g x ≤ ((g x).toReal : EReal)
      rw [hgx]
  -- every convex minorant of `g` lies below `f₁`
  have hmin : ∀ h : E → EReal, ConvexEReal h → Minorizes h g → ∀ x, h x ≤ f₁ x := by
    intro h hh hhg x
    apply hge
    intro r hr
    have hsub : convexHull ℝ (epigraph g) ⊆ epigraph h := by
      apply convexHull_min _ hh
      intro p hp
      exact le_trans (hhg p.1) hp
    exact hsub hr
  -- the affine minorant of `g` lies below `f₁`
  have haff : ∀ x, ((inner ℝ s x - b : ℝ) : EReal) ≤ f₁ x := by
    apply hmin (fun x => ((inner ℝ s x - b : ℝ) : EReal))
    · intro p hp q hq a c ha hc hac
      simp only [epigraph, Set.mem_setOf_eq, EReal.coe_le_coe_iff] at hp hq ⊢
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
        inner_add_right, inner_smul_right]
      have hc' : c = 1 - a := by linarith
      subst hc'
      nlinarith [mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hq hc]
    · intro x
      show ((inner ℝ s x - b : ℝ) : EReal) ≤ g x
      rw [EReal.coe_sub]
      exact hsb x
  have hf₁ : InConvRn f₁ :=
    ⟨fun x => lt_of_lt_of_le (EReal.bot_lt_coe _) (haff x),
      ⟨x₀, lt_of_le_of_lt (hf₁g x₀) (lt_top_iff_ne_top.2 hx₀)⟩, hcvx hconv⟩
  -- `f₁ = f₂`
  have h12 : ∀ x, f₁ x = f₂ x := by
    intro x
    apply le_antisymm
    · apply le_sSup
      exact ⟨f₁, hf₁, hf₁g, rfl⟩
    · apply sSup_le
      rintro _ ⟨h, hh, hhg, rfl⟩
      exact hmin h hh.2.2 hhg x
  -- `f₁ = f₃`
  have h13 : ∀ x, f₁ x = f₃ x := by
    intro x
    apply le_antisymm
    · apply le_sInf
      intro z hz
      obtain ⟨k, α, y, ⟨hα0, hα1⟩, hy, hx, rfl⟩ := Set.mem_iUnion.1 hz
      have hyr : ∀ j, ((g (y j)).toReal : EReal) = g (y j) := fun j =>
        EReal.coe_toReal (hy j).ne (g_ne_bot _).ne'
      have hsum : ∑ j, ((α j : ℝ) : EReal) * g (y j)
          = ((∑ j, α j * (g (y j)).toReal : ℝ) : EReal) := by
        rw [hcoe]
        apply Finset.sum_congr rfl
        intro j _
        rw [EReal.coe_mul, hyr j]
      rw [hsum]
      apply hle
      have hmem : ∑ j, α j • (y j, (g (y j)).toReal) ∈ convexHull ℝ (epigraph g) := by
        apply hconv.sum_mem
        · intro j _; exact hα0 j
        · exact hα1
        · intro j _
          apply subset_convexHull
          show g (y j) ≤ ((g (y j)).toReal : EReal)
          rw [hyr j]
      convert hmem using 1
      ext
      · simp [Prod.fst_sum, hx]
      · simp [Prod.snd_sum]
    · apply hge
      intro r hr
      obtain ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hr
      let e := Fintype.equivFin ι
      let k := Fintype.card ι
      let α : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun j => w (e.symm j))
      let y : Fin k → E := fun j => (z (e.symm j)).1
      have hzr : ∀ i, ((g (z i).1).toReal : EReal) = g (z i).1 := fun i =>
        EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hz i)) (g_ne_bot _).ne'
      have hx : x = ∑ i, w i • (z i).1 := by
        have := congrArg Prod.fst hsum
        simp only [Prod.fst_sum, Prod.smul_fst] at this
        exact this.symm
      have hr2 : r = ∑ i, w i * (z i).2 := by
        have := congrArg Prod.snd hsum
        simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] at this
        exact this.symm
      calc f₃ x ≤ ∑ j, ((α j : ℝ) : EReal) * g (y j) := by
            apply sInf_le
            apply Set.mem_iUnion.2
            refine ⟨k, α, y, ⟨?_, ?_⟩, ?_, ?_, rfl⟩
            · intro j; exact hw0 _
            · show ∑ j, w (e.symm j) = 1
              rw [Equiv.sum_comp e.symm w]; exact hw1
            · intro j
              show g (z (e.symm j)).1 < ⊤
              exact lt_of_le_of_lt (hz _) (EReal.coe_lt_top _)
            · show x = ∑ j, w (e.symm j) • (z (e.symm j)).1
              rw [Equiv.sum_comp e.symm (fun i => w i • (z i).1)]
              exact hx
        _ = ∑ i, ((w i : ℝ) : EReal) * g (z i).1 :=
            Equiv.sum_comp e.symm (fun i => ((w i : ℝ) : EReal) * g (z i).1)
        _ = ((∑ i, w i * (g (z i).1).toReal : ℝ) : EReal) := by
            rw [hcoe]
            apply Finset.sum_congr rfl
            intro i _
            rw [EReal.coe_mul, hzr i]
        _ ≤ r := by
            rw [hr2, EReal.coe_le_coe_iff]
            apply Finset.sum_le_sum
            intro i _
            apply mul_le_mul_of_nonneg_left _ (hw0 i)
            rw [← EReal.coe_le_coe_iff, hzr i]
            exact hz i
  have hf12 : f₂ = f₁ := funext fun x => (h12 x).symm
  have hf13 : f₃ = f₁ := funext fun x => (h13 x).symm
  refine ⟨hf₁, ?_, ?_, fun x => ⟨h12 x, (h12 x).symm.trans (h13 x)⟩⟩
  · rw [hf12]; exact hf₁
  · rw [hf13]; exact hf₁

end FCA_chap_B_2_5_1
