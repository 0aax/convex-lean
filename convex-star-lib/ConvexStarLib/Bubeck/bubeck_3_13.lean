import ConvexStarLib.Defs

/-!
# `bubeck_3_13`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/bubeck_3_13` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace bubeck_3_13`, so the main result is `bubeck_3_13.bubeck_3_13`.
-/

namespace bubeck_3_13

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem bubeck_3_13 {n t : ℕ}
  (L R α : ℝ)
  (ht : t ≤ n)
  (ht_pos : 0 < t)
  (hL : L > 0)
  (hR : R > 0)
  (hα : α > 0) :
  (∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
     (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
     x_star ∈ Metric.closedBall 0 R ∧
     ConvexOn ℝ (Metric.closedBall 0 R) f ∧
     LipschitzOnWith (Real.toNNReal L) f (Metric.closedBall 0 R) ∧
     IsMinOn f (Metric.closedBall 0 R) x_star ∧
     IsSubgradientOracle (Metric.closedBall 0 R) f G ∧
     (∀ z ∈ Metric.closedBall 0 R, ‖G z‖ ≤ L) ∧
     ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)),
       IsBlackBoxSpanProcedure (Metric.closedBall 0 R) G x →
       ∀ s, s < t →
         f (x s) - f x_star ≥ R * L / (2 * (1 + Real.sqrt (t : ℝ)))) ∧
  (∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
     (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
     x_star ∈ Metric.closedBall 0 (L / (2 * α)) ∧
     StrongConvexOn (Metric.closedBall 0 (L / (2 * α))) α f ∧
     LipschitzOnWith (Real.toNNReal L) f (Metric.closedBall 0 (L / (2 * α))) ∧
     IsMinOn f (Metric.closedBall 0 (L / (2 * α))) x_star ∧
     IsSubgradientOracle (Metric.closedBall 0 (L / (2 * α))) f G ∧
     (∀ z ∈ Metric.closedBall 0 (L / (2 * α)), ‖G z‖ ≤ L) ∧
     ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)),
       IsBlackBoxSpanProcedure (Metric.closedBall 0 (L / (2 * α))) G x →
       ∀ s, s < t →
         f (x s) - f x_star ≥ L ^ 2 / (8 * α * (t : ℝ))) := by
  have key : ∀ (R α γ : ℝ), 0 < α → 0 ≤ γ → 0 ≤ R → (γ / α) ^ 2 / t ≤ R ^ 2 →
      α * R + γ ≤ L →
      ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
        (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
        x_star ∈ Metric.closedBall 0 R ∧
        StrongConvexOn (Metric.closedBall 0 R) α f ∧
        LipschitzOnWith (Real.toNNReal L) f (Metric.closedBall 0 R) ∧
        IsMinOn f (Metric.closedBall 0 R) x_star ∧
        IsSubgradientOracle (Metric.closedBall 0 R) f G ∧
        (∀ z ∈ Metric.closedBall 0 R, ‖G z‖ ≤ L) ∧
        ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)),
          IsBlackBoxSpanProcedure (Metric.closedBall 0 R) G x →
          ∀ s, s < t →
            f (x s) - f x_star ≥ γ ^ 2 / (2 * α * t) := by
    intro R α γ hα hγ hR hxR hL
    classical
    set S : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => (j : ℕ) < t) with hS_def
    have memS : ∀ j : Fin n, j ∈ S ↔ (j : ℕ) < t := by
      intro j; simp [S]
    have hSne : S.Nonempty := ⟨⟨0, by omega⟩, (memS _).2 ht_pos⟩
    have hScard : S.card = t := by
      rw [hS_def, Fin.card_filter_val_lt]; omega
    -- max function
    obtain ⟨M, hM_le, hM_ex, hM_conv⟩ : ∃ M : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x, ∀ j ∈ S, x j ≤ M x) ∧ (∀ x, ∃ j ∈ S, x j = M x) ∧ ConvexOn ℝ Set.univ M := by
      refine ⟨fun x => S.sup' hSne (fun j => x j), fun x j hj => Finset.le_sup' (fun j => x j) hj,
        fun x => ?_, ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩⟩
      · obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_sup' hSne (fun j => x j)
        exact ⟨j, hj, hj'.symm⟩
      · apply Finset.sup'_le
        intro j hj
        simp only [smul_eq_mul, PiLp.add_apply, PiLp.smul_apply]
        have h1 := Finset.le_sup' (fun j => x j) hj
        have h2 := Finset.le_sup' (fun j => y j) hj
        simp only at h1 h2
        nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    -- first argmax
    obtain ⟨I, hI_mem, hI_eq, hI_min⟩ : ∃ I : EuclideanSpace ℝ (Fin n) → Fin n,
        (∀ x, I x ∈ S) ∧ (∀ x, x (I x) = M x) ∧ (∀ x, ∀ j ∈ S, x j = M x → I x ≤ j) := by
      have hne : ∀ x : EuclideanSpace ℝ (Fin n), (S.filter (fun j => x j = M x)).Nonempty := by
        intro x
        obtain ⟨j, hj, hj'⟩ := hM_ex x
        exact ⟨j, Finset.mem_filter.2 ⟨hj, hj'⟩⟩
      refine ⟨fun x => (S.filter (fun j => x j = M x)).min' (hne x), fun x => ?_, fun x => ?_,
        fun x j hj hjx => ?_⟩
      · exact (Finset.mem_filter.1 (Finset.min'_mem _ (hne x))).1
      · exact (Finset.mem_filter.1 (Finset.min'_mem _ (hne x))).2
      · exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hj, hjx⟩)
    -- the function, oracle, and minimizer
    set f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => γ * M x + α / 2 * ‖x‖ ^ 2 with hf
    set G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun x => α • x + γ • EuclideanSpace.single (I x) (1 : ℝ) with hG
    set u : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun j : Fin n => if (j : ℕ) < t then (1 / (t : ℝ)) else 0) with hu
    have htR : (0 : ℝ) < t := by exact_mod_cast ht_pos
    have hu_apply : ∀ j : Fin n, u j = if (j : ℕ) < t then (1 / (t : ℝ)) else 0 := fun j => rfl
    have hinner_u : ∀ y : EuclideanSpace ℝ (Fin n),
        inner ℝ y u = (1 / (t : ℝ)) * ∑ j ∈ S, y j := by
      intro y
      rw [PiLp.inner_apply, Finset.mul_sum, hS_def, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hu_apply]
      split_ifs <;> simp
    have hu_norm : ‖u‖ ^ 2 = 1 / (t : ℝ) := by
      rw [← real_inner_self_eq_norm_sq, hinner_u]
      have : ∑ j ∈ S, u j = ∑ j ∈ S, (1 / (t : ℝ)) :=
        Finset.sum_congr rfl (fun j hj => by rw [hu_apply, if_pos ((memS j).1 hj)])
      rw [this, Finset.sum_const, hScard, nsmul_eq_mul]
      field_simp
    have hM_ge_u : ∀ y, inner ℝ y u ≤ M y := by
      intro y
      have h1 : ∑ j ∈ S, y j ≤ ∑ j ∈ S, M y := Finset.sum_le_sum (fun j hj => hM_le y j hj)
      rw [Finset.sum_const, hScard, nsmul_eq_mul] at h1
      rw [hinner_u]
      calc 1 / (t : ℝ) * ∑ j ∈ S, y j ≤ 1 / t * (t * M y) := by gcongr
        _ = M y := by field_simp
    set xs : EuclideanSpace ℝ (Fin n) := -(γ / α) • u with hxs
    have hxs_norm : ‖xs‖ ^ 2 = (γ / α) ^ 2 / t := by
      rw [hxs, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hu_norm]
      ring
    have hM_xs : M xs = -(γ / α) / t := by
      obtain ⟨j, hj, hj'⟩ := hM_ex xs
      rw [← hj', hxs, PiLp.smul_apply, hu_apply, if_pos ((memS j).1 hj), smul_eq_mul]
      ring
    have hf_xs : f xs ≤ -(γ ^ 2 / (2 * α * t)) := by
      simp only [hf]
      rw [hxs_norm, hM_xs]
      have e : γ * (-(γ / α) / t) + α / 2 * ((γ / α) ^ 2 / t) = -(γ ^ 2 / (2 * α * t)) := by
        field_simp; ring
      linarith
    have hf_lb : ∀ y, -(γ ^ 2 / (2 * α * t)) ≤ f y := by
      intro y
      have h1 : γ * inner ℝ y u ≤ γ * M y := mul_le_mul_of_nonneg_left (hM_ge_u y) hγ
      have h2 : 0 ≤ ‖y + (γ / α) • u‖ ^ 2 := sq_nonneg _
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        hu_norm] at h2
      simp only [hf]
      have e : α / 2 * (‖y‖ ^ 2 + 2 * (γ / α * inner ℝ y u) + (γ / α) ^ 2 * (1 / t))
          = α / 2 * ‖y‖ ^ 2 + γ * inner ℝ y u + γ ^ 2 / (2 * α * t) := by
        field_simp
      have h3 := mul_nonneg (le_of_lt (half_pos hα)) h2
      rw [e] at h3
      linarith
    -- subgradient inequality
    have hsub : ∀ y z, f y ≥ f z + inner ℝ (y - z) (G z) := by
      intro y z
      simp only [hf, hG]
      rw [inner_add_right, inner_smul_right, inner_smul_right, EuclideanSpace.inner_single_right]
      simp only [PiLp.sub_apply, conj_trivial, one_mul]
      have h1 : y (I z) ≤ M y := hM_le y (I z) (hI_mem z)
      have h2 := hI_eq z
      have h3 : 0 ≤ ‖y - z‖ ^ 2 := sq_nonneg _
      rw [norm_sub_sq_real] at h3
      rw [inner_sub_left, real_inner_self_eq_norm_sq, h2]
      nlinarith [mul_le_mul_of_nonneg_left h1 hγ, mul_nonneg hα.le h3]
    -- norm bound
    have hGnorm : ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, ‖G z‖ ≤ L := by
      intro z hz
      rw [mem_closedBall_zero_iff] at hz
      calc ‖G z‖ ≤ ‖α • z‖ + ‖γ • EuclideanSpace.single (I z) (1 : ℝ)‖ := norm_add_le _ _
        _ = α * ‖z‖ + γ := by
          rw [norm_smul, norm_smul, EuclideanSpace.norm_single, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hα, abs_of_nonneg hγ, abs_one, mul_one]
        _ ≤ α * R + γ := by gcongr
        _ ≤ L := hL
    -- the subspaces V s of vectors supported on the first s coordinates
    let V : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun s =>
      { carrier := {v | ∀ j : Fin n, s ≤ (j : ℕ) → v j = 0}
        add_mem' := fun {a b} ha hb j hj => by simp [PiLp.add_apply, ha j hj, hb j hj]
        zero_mem' := fun j _ => by simp
        smul_mem' := fun c {v} hv j hj => by simp [PiLp.smul_apply, hv j hj] }
    have memV : ∀ s v, v ∈ V s ↔ ∀ j : Fin n, s ≤ (j : ℕ) → v j = 0 := fun s v => Iff.rfl
    have V_mono : ∀ a b, a ≤ b → V a ≤ V b := by
      intro a b hab v hv
      rw [memV] at hv ⊢
      exact fun j hj => hv j (le_trans hab hj)
    have hGV : ∀ s, s < t → ∀ v ∈ V s, G v ∈ V (s + 1) := by
      intro s hs v hv
      rw [memV] at hv
      have hsn : s < n := lt_of_lt_of_le hs ht
      have hIv : (I v : ℕ) ≤ s := by
        by_contra hcon
        push_neg at hcon
        have h0 : v (I v) = 0 := hv (I v) (by omega)
        have hM0 : M v = 0 := by rw [← hI_eq v, h0]
        have hsS : (⟨s, hsn⟩ : Fin n) ∈ S := (memS _).2 hs
        have hle := hI_min v ⟨s, hsn⟩ hsS (by rw [hM0]; exact hv _ le_rfl)
        rw [Fin.le_def] at hle
        simp at hle
        omega
      rw [memV]
      intro j hj
      simp only [hG, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul]
      rw [hv j (by omega), if_neg (by intro h; rw [h] at hj; omega)]
      ring
    have hxV : ∀ x, IsBlackBoxSpanProcedure (Metric.closedBall 0 R) G x →
        ∀ s, s ≤ t → x s ∈ V s := by
      intro x hx s
      induction s using Nat.strong_induction_on with
      | _ s ih =>
        intro hs
        rcases s with _ | s
        · rw [hx.1]; exact (V 0).zero_mem
        · have hspan := hx.2.2 s
          refine (Submodule.span_le.2 ?_) hspan
          rintro _ ⟨j, hj, rfl⟩
          rw [Set.mem_Iic] at hj
          have hjV : x j ∈ V j := ih j (by omega) (by omega)
          exact V_mono (j + 1) (s + 1) (by omega) (hGV j (by omega) (x j) hjV)
    refine ⟨f, xs, G, ?_, ?_, ?_, ?_, ?_, hGnorm, ?_⟩
    · -- xs in ball
      rw [mem_closedBall_zero_iff]
      rw [← hxs_norm] at hxR
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hxR
    · -- strong convexity
      rw [strongConvexOn_iff_convex]
      have : (fun x => f x - α / 2 * ‖x‖ ^ 2) = fun x => γ • M x := by
        funext x; simp only [hf, smul_eq_mul]; ring
      rw [this]
      exact (hM_conv.subset (Set.subset_univ _) (convex_closedBall 0 R)).smul hγ
    · -- Lipschitz
      apply LipschitzOnWith.of_dist_le'
      intro y hy z hz
      rw [Real.dist_eq, dist_eq_norm]
      have h1 := hsub y z
      have h2 := hsub z y
      have hGy := hGnorm y hy
      have hGz := hGnorm z hz
      have i1 := abs_real_inner_le_norm (y - z) (G z)
      have i2 := abs_real_inner_le_norm (z - y) (G y)
      rw [norm_sub_rev z y] at i2
      have a1 := neg_abs_le (inner ℝ (y - z) (G z))
      have a2 := neg_abs_le (inner ℝ (z - y) (G y))
      have m1 : ‖y - z‖ * ‖G z‖ ≤ ‖y - z‖ * L := mul_le_mul_of_nonneg_left hGz (norm_nonneg _)
      have m2 : ‖y - z‖ * ‖G y‖ ≤ ‖y - z‖ * L := mul_le_mul_of_nonneg_left hGy (norm_nonneg _)
      rw [abs_sub_le_iff]
      constructor
      · linarith
      · linarith
    · -- IsMinOn
      rw [isMinOn_iff]
      intro y _
      exact le_trans hf_xs (hf_lb y)
    · -- subgradient oracle
      intro z _ y _
      exact hsub y z
    · -- lower bound
      intro x hx s hs
      have hxs_V := hxV x hx s hs.le
      rw [memV] at hxs_V
      have hsn : s < n := lt_of_lt_of_le hs ht
      have h0 : x s ⟨s, hsn⟩ = 0 := hxs_V ⟨s, hsn⟩ le_rfl
      have hM0 : 0 ≤ M (x s) := by
        have := hM_le (x s) ⟨s, hsn⟩ ((memS _).2 hs)
        rw [h0] at this; exact this
      have hfx : 0 ≤ f (x s) := by
        simp only [hf]
        exact add_nonneg (mul_nonneg hγ hM0) (mul_nonneg (by linarith) (sq_nonneg _))
      linarith [hf_xs]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht_pos
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht_pos
  constructor
  · -- Part 1: γ = L √t / (1 + √t), α' = L / (R (1 + √t))
    set q := Real.sqrt (t : ℝ) with hq
    have hq0 : 0 < q := Real.sqrt_pos.2 htR
    have hsq : q ^ 2 = t := Real.sq_sqrt htR.le
    have hq1 : 0 < 1 + q := by linarith
    obtain ⟨f, xs, G, h1, h2, h3, h4, h5, h6, h7⟩ :=
      key R (L / (R * (1 + q))) (L * q / (1 + q)) (by positivity)
        (by positivity) hR.le
        (by
          rw [← hsq]
          apply le_of_eq
          field_simp)
        (by
          apply le_of_eq
          field_simp)
    refine ⟨f, xs, G, h1, strongConvexOn_zero.1 (h2.mono (by positivity)), h3, h4, h5, h6, ?_⟩
    intro x hx s hs
    have e : (L * q / (1 + q)) ^ 2 / (2 * (L / (R * (1 + q))) * t) = R * L / (2 * (1 + q)) := by
      rw [← hsq]
      field_simp
    have := h7 x hx s hs
    rw [e] at this
    exact this
  · -- Part 2: γ = L / 2, radius L / (2 α)
    obtain ⟨f, xs, G, h1, h2, h3, h4, h5, h6, h7⟩ :=
      key (L / (2 * α)) α (L / 2) hα (by positivity) (by positivity)
        (by
          rw [show L / 2 / α = L / (2 * α) by rw [div_div]]
          exact div_le_self (sq_nonneg _) ht1)
        (by
          apply le_of_eq
          field_simp
          ring)
    refine ⟨f, xs, G, h1, h2, h3, h4, h5, h6, ?_⟩
    intro x hx s hs
    have e : (L / 2) ^ 2 / (2 * α * t) = L ^ 2 / (8 * α * t) := by
      field_simp
      ring
    have := h7 x hx s hs
    rw [e] at this
    exact this

end bubeck_3_13
