import ConvexStarLib.Defs

/-!
# `FCA_chap_D_ex7`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_ex7` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_ex7`, so the main result is `FCA_chap_D_ex7.FCA_chap_D_ex7`.
-/

namespace FCA_chap_D_ex7

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_ex7
  (f : E → ℝ)
  (g : E → ℝ)
  (hf_convex : InConvRn (liftRealtoEReal f))
  (hg_convex : InConvRn (liftRealtoEReal g))
  (hfg_subdiff : ∀ x, Set.Nonempty ((directionalSubdifferential (liftRealtoEReal f) x) ∩
    (directionalSubdifferential (liftRealtoEReal g) x))) :
  ∃ (c : ℝ), ∀ (x : E), (f x) - (g x) = c := by
  -- Step 1: convexity of the real-valued functions
  have hconv : ∀ (F : E → ℝ), InConvRn (liftRealtoEReal F) → ConvexOn ℝ Set.univ F := by
    intro F hF
    rw [convexOn_iff_convex_epigraph]
    have h := hF.2.2
    unfold ConvexEReal epigraph liftRealtoEReal at h
    convert h using 1
    ext p
    simp [EReal.coe_le_coe_iff]
  -- Step 2: elements of the directional subdifferential are subgradients
  have hsub : ∀ (F : E → ℝ), ConvexOn ℝ Set.univ F → ∀ x s,
      s ∈ directionalSubdifferential (liftRealtoEReal F) x →
      ∀ d, inner ℝ s d ≤ F (x + d) - F x := by
    intro F hF x s hs d
    set Q : ℝ → EReal := fun t => differenceQuotient (liftRealtoEReal F) x d t with hQ
    have hQq : ∀ t, Q t = (((F (x + t • d) - F x) / t : ℝ) : EReal) := fun t => rfl
    have hmono : MonotoneOn Q (Set.Ioi 0) := by
      intro a ha b hb hab
      rw [hQq, hQq, EReal.coe_le_coe_iff]
      have ha' : (0:ℝ) < a := ha
      have hb' : (0:ℝ) < b := hb
      have key : F (x + a • d) ≤ (a / b) * F (x + b • d) + (1 - a / b) * F x := by
        have h1 : x + a • d = (a / b) • (x + b • d) + (1 - a / b) • x := by
          rw [smul_add, smul_smul, div_mul_cancel₀ a hb'.ne', sub_smul, one_smul]
          abel
        rw [h1]
        have := hF.2 (Set.mem_univ (x + b • d)) (Set.mem_univ x)
          (show (0:ℝ) ≤ a / b from div_nonneg ha'.le hb'.le)
          (show (0:ℝ) ≤ 1 - a / b by rw [sub_nonneg, div_le_one hb']; exact hab)
          (show a / b + (1 - a / b) = 1 by ring)
        simp only [smul_eq_mul] at this
        exact this
      rw [div_le_div_iff₀ ha' hb']
      have h2 : (F (x + a • d) - F x) * b ≤ ((a / b) * F (x + b • d) + (1 - a / b) * F x - F x) * b := by
        apply mul_le_mul_of_nonneg_right _ hb'.le
        linarith
      calc (F (x + a • d) - F x) * b
          ≤ ((a / b) * F (x + b • d) + (1 - a / b) * F x - F x) * b := h2
        _ = (F (x + b • d) - F x) * a := by field_simp; ring
    have htend : Filter.Tendsto Q (𝓝[>] 0) (𝓝 (sInf (Q '' Set.Ioi 0))) :=
      hmono.tendsto_nhdsGT (OrderBot.bddBelow _)
    have hlim : directionalDeriv (liftRealtoEReal F) x d = sInf (Q '' Set.Ioi 0) :=
      htend.limUnder_eq
    have h1 : ((inner ℝ s d : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal F) x d := hs d
    have h2 : sInf (Q '' Set.Ioi 0) ≤ Q 1 :=
      sInf_le (Set.mem_image_of_mem Q (Set.mem_Ioi.mpr one_pos))
    have h3 : ((inner ℝ s d : ℝ) : EReal) ≤ (((F (x + (1:ℝ) • d) - F x) / 1 : ℝ) : EReal) := by
      calc ((inner ℝ s d : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal F) x d := h1
        _ = sInf (Q '' Set.Ioi 0) := hlim
        _ ≤ Q 1 := h2
        _ = _ := hQq 1
    rw [EReal.coe_le_coe_iff, one_smul, div_one] at h3
    exact h3
  have hfc := hconv f hf_convex
  have hgc := hconv g hg_convex
  choose S hS using hfg_subdiff
  have hSf : ∀ z w, inner ℝ (S z) (w - z) ≤ f w - f z := by
    intro z w
    have := hsub f hfc z (S z) (hS z).1 (w - z)
    simpa using this
  have hSg : ∀ z w, inner ℝ (S z) (w - z) ≤ g w - g z := by
    intro z w
    have := hsub g hgc z (S z) (hS z).2 (w - z)
    simpa using this
  -- Step 3: key estimate
  have hkey : ∀ z w, |(f w - g w) - (f z - g z)| ≤ inner ℝ (S w - S z) (w - z) := by
    intro z w
    have a1 := hSf z w
    have a2 := hSf w z
    have a3 := hSg z w
    have a4 := hSg w z
    have e1 : inner ℝ (S w) (z - w) = - inner ℝ (S w) (w - z) := by
      rw [← inner_neg_right, neg_sub]
    rw [inner_sub_left, abs_le]
    constructor <;> linarith
  -- Step 4: telescoping
  refine ⟨f 0 - g 0, fun y => ?_⟩
  set x : E := 0 with hx
  set C : ℝ := inner ℝ (S y - S x) (y - x) with hC
  have htel : ∀ n : ℕ, 0 < n → |(f y - g y) - (f x - g x)| ≤ C / n := by
    intro n hn
    have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    set p : ℕ → E := fun i => x + ((i:ℝ) / n) • (y - x) with hp
    have hp0 : p 0 = x := by simp [hp]
    have hpn : p n = y := by simp [hp, div_self hn']
    have hstep : ∀ i, p (i+1) - p i = (1 / (n:ℝ)) • (y - x) := by
      intro i
      simp only [hp]
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      push_cast
      ring
    set u : ℕ → ℝ := fun i => f (p i) - g (p i) with hu
    set v : ℕ → ℝ := fun i => inner ℝ (S (p i)) (y - x) with hv
    have hbound : ∀ i, |u (i+1) - u i| ≤ (1 / (n:ℝ)) * (v (i+1) - v i) := by
      intro i
      have := hkey (p i) (p (i+1))
      rw [hstep, inner_smul_right, inner_sub_left] at this
      simpa [hu, hv] using this
    have hsum_u : ∑ i ∈ Finset.range n, (u (i+1) - u i) = u n - u 0 := Finset.sum_range_sub u n
    have hsum_v : ∑ i ∈ Finset.range n, (v (i+1) - v i) = v n - v 0 := Finset.sum_range_sub v n
    calc |(f y - g y) - (f x - g x)| = |u n - u 0| := by simp [hu, hp0, hpn]
      _ = |∑ i ∈ Finset.range n, (u (i+1) - u i)| := by rw [hsum_u]
      _ ≤ ∑ i ∈ Finset.range n, |u (i+1) - u i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, (1 / (n:ℝ)) * (v (i+1) - v i) :=
          Finset.sum_le_sum (fun i _ => hbound i)
      _ = (1 / (n:ℝ)) * (v n - v 0) := by rw [← Finset.mul_sum, hsum_v]
      _ = C / n := by simp [hv, hp0, hpn, hC, inner_sub_left]; ring
  by_contra hne
  have hpos : 0 < |(f y - g y) - (f x - g x)| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hC0 : 0 ≤ C := by
    have := htel 1 one_pos
    have h0 := abs_nonneg ((f y - g y) - (f x - g x))
    simp at this
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |(f y - g y) - (f x - g x)|)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg hC0 hpos.le) hn
  have h1 := htel n (by exact_mod_cast hn0)
  rw [div_lt_iff₀ hpos] at hn
  rw [le_div_iff₀ hn0] at h1
  linarith

end FCA_chap_D_ex7
