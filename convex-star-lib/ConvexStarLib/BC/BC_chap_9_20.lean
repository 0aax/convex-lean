import ConvexStarLib.Defs

/-!
# `BC_chap_9_20`

Source: Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces.

Statement from the `convex-eval-v28-2h/BC_chap_9_20` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace BC_chap_9_20`, so the main result is `BC_chap_9_20.BC_chap_9_20`.
-/

namespace BC_chap_9_20

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem BC_chap_9_20
  (f : E → EReal)
  (hf : IsProperLSCConvex f) :
  ∃ (p u : E), ∀ (y : E),
    (p ∈ effDom f) ∧
    ((inner ℝ (y - p) u) + f p ≤ f y) := by
  obtain ⟨⟨hbot, x₀, hx₀⟩, hlsc, hconv⟩ := hf
  have hx₀top : f x₀ ≠ ⊤ := ne_of_lt hx₀
  have hx₀bot : f x₀ ≠ ⊥ := ne_of_gt (hbot x₀)
  set r₀ : ℝ := (f x₀).toReal with hr₀
  have hfx₀ : f x₀ = (r₀ : EReal) := (EReal.coe_toReal hx₀top hx₀bot).symm
  -- Project `(x₀, r₀ - 1)` onto the epigraph, viewed in the Hilbert space `WithLp 2 (E × ℝ)`;
  -- the normal vector at the projection `(p, s)` is non-horizontal and yields a subgradient at `p`.
  let K : Set (WithLp 2 (E × ℝ)) := {w | f w.fst ≤ (w.snd : EReal)}
  have hKconv : Convex ℝ K :=
    hconv.linear_preimage (WithLp.linearEquiv 2 ℝ (E × ℝ)).toLinearMap
  have hKclosed : IsClosed K := by
    have h1 : IsClosed {q : E × EReal | f q.1 ≤ q.2} := hlsc.isClosed_epigraph
    have h2 : Continuous (fun w : WithLp 2 (E × ℝ) => (w.fst, (w.snd : EReal))) :=
      Continuous.prodMk (WithLp.continuous_fst 2 E ℝ)
        (continuous_coe_real_ereal.comp (WithLp.continuous_snd 2 E ℝ))
    exact h1.preimage h2
  have hKne : K.Nonempty := ⟨WithLp.toLp 2 (x₀, r₀), by simp [K, hfx₀]⟩
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKclosed.isComplete hKconv
    (WithLp.toLp 2 (x₀, r₀ - 1))
  have key := (norm_eq_iInf_iff_real_inner_le_zero hKconv hvK).1 hv
  set p : E := v.fst with hp
  set s : ℝ := v.snd with hs
  have hps : f p ≤ (s : EReal) := hvK
  have key' : ∀ x : E, ∀ t : ℝ, f x ≤ (t : EReal) →
      inner ℝ (x₀ - p) (x - p) + (r₀ - 1 - s) * (t - s) ≤ 0 := by
    intro x t hxt
    have := key (WithLp.toLp 2 (x, t)) hxt
    simp [WithLp.prod_inner_apply] at this
    rw [hp, hs]
    linarith
  have h1 : r₀ - 1 - s ≤ 0 := by
    have hle : f p ≤ ((s + 1 : ℝ) : EReal) :=
      hps.trans (by exact_mod_cast (by linarith : s ≤ s + 1))
    have := key' p (s + 1) hle
    simpa using this
  have h2 := key' x₀ r₀ (le_of_eq hfx₀)
  have hd : 0 < s - (r₀ - 1) := by
    rcases lt_or_eq_of_le h1 with h | h
    · linarith
    · exfalso
      rw [h, zero_mul, add_zero] at h2
      have h0 : x₀ - p = 0 := by
        rw [← real_inner_self_nonpos]
        exact h2
      have hpx : p = x₀ := (sub_eq_zero.1 h0).symm
      rw [hpx, hfx₀] at hps
      have : r₀ ≤ s := by exact_mod_cast hps
      linarith
  refine ⟨p, (s - (r₀ - 1))⁻¹ • (x₀ - p), fun y => ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_lt hps (EReal.coe_lt_top s)
  · by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · have hybot : f y ≠ ⊥ := ne_of_gt (hbot y)
      set t : ℝ := (f y).toReal with ht
      have hfy : f y = (t : EReal) := (EReal.coe_toReal hy hybot).symm
      have h3 := key' y t (le_of_eq hfy)
      have h4 : inner ℝ (y - p) ((s - (r₀ - 1))⁻¹ • (x₀ - p)) ≤ t - s := by
        rw [real_inner_smul_right, real_inner_comm, inv_mul_le_iff₀ hd]
        linarith
      calc ((inner ℝ (y - p) ((s - (r₀ - 1))⁻¹ • (x₀ - p)) : ℝ) : EReal) + f p
          ≤ ((inner ℝ (y - p) ((s - (r₀ - 1))⁻¹ • (x₀ - p)) : ℝ) : EReal) + (s : EReal) := by
            gcongr
        _ = ((inner ℝ (y - p) ((s - (r₀ - 1))⁻¹ • (x₀ - p)) + s : ℝ) : EReal) := by
            rw [EReal.coe_add]
        _ ≤ (t : EReal) := by
            exact_mod_cast (by linarith : inner ℝ (y - p) ((s - (r₀ - 1))⁻¹ • (x₀ - p)) + s ≤ t)
        _ = f y := hfy.symm

end BC_chap_9_20
