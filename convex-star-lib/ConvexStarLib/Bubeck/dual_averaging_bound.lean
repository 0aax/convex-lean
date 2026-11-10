import ConvexStarLib.Defs

/-!
# `dual_averaging_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/dual_averaging_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace dual_averaging_bound`, so the main result is `dual_averaging_bound.dual_averaging_bound`.
-/

namespace dual_averaging_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem dual_averaging_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {t : ℕ}
  (𝓧 : Set E) (𝓓 : Set E)
  (f : E → ℝ) (phi : E → ℝ)
  (x : ℕ → E) (y : ℕ → E)
  (g : ℕ → E →L[ℝ] ℝ) (ρ L R : ℝ)
  (x_star : E)
  (hR : R ^ 2 = sSup {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi (x 0) = v})
  (hR_pos : R > 0)
  (ht : t ≥ 1) (hρ : ρ > 0) (hL : L > 0)
  (hx_0 : x 0 ∈ 𝓧 ∩ 𝓓)
  (h_da_seq : IsDualAveragingSequence 𝓧 𝓓 f phi x y g ((R / L) * Real.sqrt (ρ / (2 * t))))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓓_convex : Convex ℝ 𝓓)
  (h𝓓_open : IsOpen 𝓓)
  (h𝓓_contains : 𝓧 ⊆ closure 𝓓)
  (h_inter_nonempty : Set.Nonempty (𝓧 ∩ 𝓓))
  (hphi_mirror_map : IsMirrorMap 𝓓 phi)
  (hphi_strong_convex : StrongConvexOn (𝓧 ∩ 𝓓) ρ phi)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hg_bounded : ∀ s, ‖g s‖ ≤ L)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, (x s)) - f x_star ≤
  2 * R * L * Real.sqrt (2 / (ρ * t)) := by
  classical
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hq : 0 < Real.sqrt (ρ / (2 * t)) := Real.sqrt_pos.mpr (by positivity)
  have hη : 0 < (R / L) * Real.sqrt (ρ / (2 * t)) := by positivity
  -- unpack the dual averaging hypotheses
  unfold IsDualAveragingSequence at h_da_seq
  obtain ⟨h0min, -, hmin, hxK, -, -, hsub⟩ := h_da_seq
  generalize hη_def : (R / L) * Real.sqrt (ρ / (2 * t)) = η at hη h0min hmin
  -- bound on the regularizer over the feasible set
  have hphiR : ∀ u ∈ 𝓧 ∩ 𝓓, phi u - phi (x 0) ≤ R ^ 2 := by
    intro u hu
    by_cases hb : BddAbove {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi (x 0) = v}
    · rw [hR]; exact le_csSup hb ⟨u, hu, rfl⟩
    · rw [Real.sSup_of_not_bddAbove hb] at hR
      nlinarith
  -- be-the-leader lemma
  have hbtl : ∀ T : ℕ, ∀ u ∈ 𝓧 ∩ 𝓓,
      η * ∑ s ∈ Finset.range T, g s (x (s + 1)) + phi (x 0)
        ≤ η * ∑ s ∈ Finset.range T, g s u + phi u := by
    intro T
    induction T with
    | zero =>
      intro u hu
      simpa using isMinOn_iff.mp h0min u hu
    | succ T ih =>
      intro u hu
      have h1 := ih (x (T + 1)) (hxK (T + 1))
      have h2 := isMinOn_iff.mp (hmin (T + 1)) u hu
      simp only [Finset.sum_range_succ] at h1 h2 ⊢
      linarith
  -- stability of consecutive iterates
  have hstab : ∀ s, g s (x s - x (s + 1)) ≤ 2 * η * L ^ 2 / ρ := by
    intro s
    have hw := hxK s
    have hz := hxK (s + 1)
    have hm : (1 / 2 : ℝ) • x s + (1 / 2 : ℝ) • x (s + 1) ∈ 𝓧 ∩ 𝓓 :=
      hphi_strong_convex.1 hw hz (by norm_num) (by norm_num) (by norm_num)
    have ha := isMinOn_iff.mp (hmin s) _ hm
    have hb := isMinOn_iff.mp (hmin (s + 1)) _ hm
    have hc := hphi_strong_convex.2 hw hz (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [Finset.sum_range_succ, map_add, map_smul, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum] at ha hb hc
    have hgd : g s (x s - x (s + 1)) ≤ L * ‖x s - x (s + 1)‖ := by
      calc g s (x s - x (s + 1)) ≤ ‖g s (x s - x (s + 1))‖ := Real.le_norm_self _
        _ ≤ ‖g s‖ * ‖x s - x (s + 1)‖ := (g s).le_opNorm _
        _ ≤ L * ‖x s - x (s + 1)‖ := by gcongr; exact hg_bounded s
    have hkey : ρ / 2 * ‖x s - x (s + 1)‖ ^ 2 ≤ η * g s (x s - x (s + 1)) := by
      rw [map_sub]
      nlinarith
    have hnorm : ρ * ‖x s - x (s + 1)‖ ≤ 2 * η * L := by
      rcases (norm_nonneg (x s - x (s + 1))).eq_or_lt with h0 | hpos
      · rw [← h0]; nlinarith
      · nlinarith
    rw [le_div_iff₀ hρ]
    nlinarith
  -- regret against any comparator in the feasible set
  have hreg : ∀ u ∈ 𝓧 ∩ 𝓓, ∑ s ∈ Finset.range t, (g s (x s) - g s u)
      ≤ t * (2 * η * L ^ 2 / ρ) + R ^ 2 / η := by
    intro u hu
    have h1 := hbtl t u hu
    have h2 := hphiR u hu
    have h3 : ∑ s ∈ Finset.range t, g s (x s - x (s + 1)) ≤ t * (2 * η * L ^ 2 / ρ) := by
      calc ∑ s ∈ Finset.range t, g s (x s - x (s + 1))
          ≤ ∑ s ∈ Finset.range t, (2 * η * L ^ 2 / ρ) := Finset.sum_le_sum (fun s _ => hstab s)
        _ = t * (2 * η * L ^ 2 / ρ) := by simp
    have h4 : ∑ s ∈ Finset.range t, (g s (x s) - g s u)
        = ∑ s ∈ Finset.range t, g s (x s - x (s + 1))
          + (∑ s ∈ Finset.range t, g s (x (s + 1)) - ∑ s ∈ Finset.range t, g s u) := by
      simp only [map_sub, Finset.sum_sub_distrib]; ring
    have h5 : ∑ s ∈ Finset.range t, g s (x (s + 1)) - ∑ s ∈ Finset.range t, g s u ≤ R ^ 2 / η := by
      rw [le_div_iff₀ hη]
      linarith
    linarith
  -- regret against x_star (which may lie on the boundary of 𝓓)
  have hreg_star : ∑ s ∈ Finset.range t, (g s (x s) - g s x_star)
      ≤ t * (2 * η * L ^ 2 / ρ) + R ^ 2 / η := by
    obtain ⟨hp𝓧, hp𝓓⟩ := hx_0
    set B := t * (2 * η * L ^ 2 / ρ) + R ^ 2 / η with hB
    set A := ∑ s ∈ Finset.range t, (g s (x s) - g s x_star) with hA
    set C := ∑ s ∈ Finset.range t, (g s (x s) - g s (x 0)) with hC
    have key : ∀ n : ℕ, (1 - 1 / ((n : ℝ) + 1)) * A + (1 / ((n : ℝ) + 1)) * C ≤ B := by
      intro n
      have hc0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hc1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      set c := 1 / ((n : ℝ) + 1) with hc
      have hu𝓓 : (1 - c) • x_star + c • x 0 ∈ 𝓓 := by
        have := h𝓓_convex.combo_closure_interior_mem_interior (h𝓓_contains hx_star_mem)
          (by rwa [h𝓓_open.interior_eq]) (by linarith : (0 : ℝ) ≤ 1 - c) hc0 (by ring)
        rwa [h𝓓_open.interior_eq] at this
      have hu𝓧 : (1 - c) • x_star + c • x 0 ∈ 𝓧 :=
        h𝓧_convex hx_star_mem hp𝓧 (by linarith) hc0.le (by ring)
      have := hreg _ ⟨hu𝓧, hu𝓓⟩
      simp only [map_add, map_smul, smul_eq_mul] at this
      have e : ∑ s ∈ Finset.range t, (g s (x s) - ((1 - c) * g s x_star + c * g s (x 0)))
          = (1 - c) * A + c * C := by
        simp only [hA, hC, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro s _; ring
      linarith
    have hlim : Filter.Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 1)) * A + (1 / ((n : ℝ) + 1)) * C)
        Filter.atTop (𝓝 ((1 - 0) * A + 0 * C)) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact ((tendsto_const_nhds.sub h).mul tendsto_const_nhds).add (h.mul tendsto_const_nhds)
    have := le_of_tendsto' hlim key
    simpa using this
  -- subgradient inequality summed
  have hfsum : ∑ s ∈ Finset.range t, (f (x s) - f x_star)
      ≤ ∑ s ∈ Finset.range t, (g s (x s) - g s x_star) := by
    apply Finset.sum_le_sum
    intro s _
    have := hsub s x_star hx_star_mem
    rw [map_sub] at this
    linarith
  -- Jensen
  have hjensen : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s)
      ≤ ∑ s ∈ Finset.range t, (1 / (t : ℝ)) * f (x s) := by
    rw [Finset.smul_sum]
    have := hf_convex.map_sum_le (t := Finset.range t) (w := fun _ => 1 / (t : ℝ)) (p := x)
      (fun i _ => by positivity) (by simp; field_simp) (fun i _ => (hxK i).1)
    simpa using this
  have hsumf : (∑ s ∈ Finset.range t, (1 / (t : ℝ)) * f (x s)) - f x_star
      = (1 / (t : ℝ)) * ∑ s ∈ Finset.range t, (f (x s) - f x_star) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
    field_simp
    ring
  -- final arithmetic
  have hfinal : (1 / (t : ℝ)) * (t * (2 * η * L ^ 2 / ρ) + R ^ 2 / η)
      ≤ 2 * R * L * Real.sqrt (2 / (ρ * t)) := by
    rw [← hη_def]
    have hs2 : 0 < Real.sqrt (2 / (ρ * t)) := Real.sqrt_pos.mpr (by positivity)
    have hq2 : Real.sqrt (ρ / (2 * t)) ^ 2 = ρ / (2 * t) := Real.sq_sqrt (by positivity)
    have hs22 : Real.sqrt (2 / (ρ * t)) ^ 2 = 2 / (ρ * t) := Real.sq_sqrt (by positivity)
    generalize Real.sqrt (ρ / (2 * t)) = q at hq hq2 ⊢
    generalize Real.sqrt (2 / (ρ * t)) = s2 at hs2 hs22 ⊢
    have hqs : q * s2 * t = 1 := by
      have h1 : (q * s2 * t) ^ 2 = 1 := by
        rw [mul_pow, mul_pow, hq2, hs22]; field_simp
      have h2 : 0 < q * s2 * t := by positivity
      nlinarith
    have hs2eq : s2 = 1 / (q * t) := by
      field_simp; linarith [hqs]
    have hρq : ρ = 2 * t * q ^ 2 := by rw [hq2]; field_simp
    rw [hs2eq, hρq]
    field_simp
    norm_num
  calc f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s) - f x_star
      ≤ (∑ s ∈ Finset.range t, (1 / (t : ℝ)) * f (x s)) - f x_star := by linarith
    _ = (1 / (t : ℝ)) * ∑ s ∈ Finset.range t, (f (x s) - f x_star) := hsumf
    _ ≤ (1 / (t : ℝ)) * (t * (2 * η * L ^ 2 / ρ) + R ^ 2 / η) := by
        gcongr; linarith
    _ ≤ 2 * R * L * Real.sqrt (2 / (ρ * t)) := hfinal

end dual_averaging_bound
