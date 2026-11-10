import ConvexStarLib.Defs

/-!
# `RW_chap_12_41`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_41` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_41`, so the main result is `RW_chap_12_41.RW_chap_12_41`.
-/

namespace RW_chap_12_41

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem RW_chap_12_41
  (T : E → Set E)
  (hT : IsMaximalMonotone T) :
  let domT : Set E := {x | (T x).Nonempty}
  let rgeT : Set E := {v | ∃ x, v ∈ T x}
  (∃ C : Set E, Convex ℝ C ∧ C ⊆ domT ∧ domT ⊆ closure C) ∧
  (∃ C : Set E, Convex ℝ C ∧ C ⊆ rgeT ∧ rgeT ⊆ closure C) := by
  -- Finite extension lemma: a finite monotone family can be extended at any point `x`.
  have finite_ext : ∀ (s : Finset (E × E)),
      (∀ q ∈ s, ∀ q' ∈ s, 0 ≤ inner ℝ (q.2 - q'.2) (q.1 - q'.1)) → ∀ (x : E),
      ∃ p : E, ∀ q ∈ s, 0 ≤ inner ℝ (p - q.2) (x - q.1) := by
    intro s hs x
    classical
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, by simp⟩
    by_contra hcon
    let Φ : E → (s → ℝ) := fun p i => inner ℝ (p - i.1.2) (x - i.1.1)
    let A : Set E := convexHull ℝ ((fun q : E × E => q.2) '' (s : Set (E × E)))
    let S : Set (s → ℝ) := Φ '' A
    let P : Set (s → ℝ) := {f | ∀ i, 0 ≤ f i}
    have hΦc : Continuous Φ := by
      refine continuous_pi (fun i => ?_)
      exact (continuous_id.sub continuous_const).inner continuous_const
    have hSconv : Convex ℝ S := by
      rintro _ ⟨p₁, hp₁, rfl⟩ _ ⟨p₂, hp₂, rfl⟩ a b ha hb hab
      refine ⟨a • p₁ + b • p₂, (convex_convexHull ℝ _) hp₁ hp₂ ha hb hab, ?_⟩
      funext i
      simp only [Φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hb' : b = 1 - a := by linarith
      subst hb'
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    have hScomp : IsCompact S := by
      refine IsCompact.image ?_ hΦc
      exact (s.finite_toSet.image _).isCompact_convexHull
    have hPconv : Convex ℝ P := by
      intro f hf g hg a b ha hb _ i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hf i)) (mul_nonneg hb (hg i))
    have hPclosed : IsClosed P := by
      have : P = ⋂ i, {f : s → ℝ | 0 ≤ f i} := by
        ext f; simp [P]
      rw [this]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
    have hdisj : Disjoint S P := by
      rw [Set.disjoint_left]
      rintro _ ⟨p, _, rfl⟩ hP
      exact hcon ⟨p, fun q hq => hP ⟨q, hq⟩⟩
    obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
      geometric_hahn_banach_compact_closed hSconv hScomp hPconv hPclosed hdisj
    set lam : s → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hlam
    have hf_eq : ∀ g : s → ℝ, f g = ∑ i, g i * lam i := by
      intro g
      have := LinearMap.pi_apply_eq_sum_univ (f : (s → ℝ) →ₗ[ℝ] ℝ) g
      simpa [lam, smul_eq_mul] using this
    have hv0 : v < 0 := by
      have := hfv 0 (fun i => le_refl _)
      simpa using this
    have hlam_nonneg : ∀ i, 0 ≤ lam i := by
      intro i
      by_contra hneg
      push_neg at hneg
      have hpos : 0 < v / lam i := div_pos_of_neg_of_neg hv0 hneg
      have hmem : (v / lam i) • (fun j : s => if i = j then (1:ℝ) else 0) ∈ P := by
        intro j
        simp only [Pi.smul_apply, smul_eq_mul]
        split_ifs
        · simpa using hpos.le
        · simp
      have := hfv _ hmem
      rw [map_smul, smul_eq_mul] at this
      have h2 : v / lam i * f (fun j : s => if i = j then (1:ℝ) else 0) = v := by
        change v / lam i * lam i = v
        exact div_mul_cancel₀ v hneg.ne
      linarith
    have hS_neg : ∀ p ∈ A, ∑ i, Φ p i * lam i < 0 := by
      intro p hp
      have := hfu (Φ p) ⟨p, hp, rfl⟩
      rw [hf_eq] at this
      linarith
    rcases (Finset.sum_nonneg (fun i _ => hlam_nonneg i) :
        (0:ℝ) ≤ ∑ i, lam i).eq_or_lt with hΛ | hΛ
    · have hall : ∀ i, lam i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hlam_nonneg i)).mp hΛ.symm i
          (Finset.mem_univ i)
      obtain ⟨q, hq⟩ := hne
      have := hS_neg q.2 (subset_convexHull ℝ _ ⟨q, hq, rfl⟩)
      simp [hall] at this
    · set Λ := ∑ i, lam i with hΛdef
      set w : s → E := fun i => i.1.2 with hw
      set y : s → E := fun i => i.1.1 with hy
      set pstar := Finset.univ.centerMass lam w with hpstar
      have hmem : pstar ∈ A :=
        Finset.centerMass_mem_convexHull _ (fun i _ => hlam_nonneg i) hΛ
          (fun i _ => ⟨i.1, i.2, rfl⟩)
      have hneg := hS_neg pstar hmem
      -- compute
      have hdiff : ∀ i, pstar - w i = Λ⁻¹ • ∑ j, lam j • (w j - w i) := by
        intro i
        have h1 : ∑ j, lam j • (w j - w i) = Λ • pstar - Λ • w i := by
          simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
          rw [hpstar, Finset.centerMass, smul_smul, mul_inv_cancel₀ hΛ.ne', one_smul]
        rw [h1, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hΛ.ne', one_smul, one_smul]
      have hinner : ∀ i, Φ pstar i = Λ⁻¹ * ∑ j, lam j * inner ℝ (w j - w i) (x - y i) := by
        intro i
        change inner ℝ (pstar - w i) (x - y i) = _
        rw [hdiff i, real_inner_smul_left, sum_inner]
        simp only [real_inner_smul_left]
      set B : s → s → ℝ := fun i j => lam i * lam j * inner ℝ (w j - w i) (x - y i) with hB
      have hBsym : ∀ i j, B i j + B j i = lam i * lam j * inner ℝ (w j - w i) (y j - y i) := by
        intro i j
        simp only [hB, inner_sub_left, inner_sub_right]
        ring
      have hBnn : 0 ≤ ∑ i, ∑ j, B i j := by
        have h1 : ∑ i, ∑ j, B i j = ∑ i, ∑ j, B j i := Finset.sum_comm
        have h2 : 0 ≤ ∑ i, ∑ j, (B i j + B j i) := by
          refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
          rw [hBsym]
          refine mul_nonneg (mul_nonneg (hlam_nonneg i) (hlam_nonneg j)) ?_
          exact hs j.1 j.2 i.1 i.2
        simp only [Finset.sum_add_distrib] at h2
        linarith
      have heq : ∑ i, Φ pstar i * lam i = Λ⁻¹ * ∑ i, ∑ j, B i j := by
        simp only [hinner, hB, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
      have : 0 ≤ ∑ i, Φ pstar i * lam i := by
        rw [heq]
        exact mul_nonneg (inv_nonneg.mpr hΛ.le) hBnn
      linarith
  -- Points of the "relative interior" of `conv (dom T)` belong to `dom T`.
  have mem_dom : ∀ (T : E → Set E), IsMaximalMonotone T → ∀ (x : E),
      (∀ a, (T a).Nonempty →
        ∃ ε > (0:ℝ), x + ε • (x - a) ∈ convexHull ℝ {z | (T z).Nonempty}) →
      (T x).Nonempty := by
    intro T hT x hx
    classical
    set D : Set E := {z | (T z).Nonempty} with hD
    set L : Submodule ℝ E := Submodule.span ℝ ((fun a => a - x) '' D) with hL
    have key : ∀ d ∈ L, (∀ a ∈ D, 0 ≤ inner ℝ d (x - a)) → d = 0 := by
      intro d hdL hd
      have hzero : ∀ a ∈ D, inner ℝ d (a - x) = 0 := by
        intro a ha
        have hneg : inner ℝ d (a - x) = - inner ℝ d (x - a) := by
          rw [← inner_neg_right, neg_sub]
        have h1 : inner ℝ d (a - x) ≤ 0 := by
          have := hd a ha
          linarith
        obtain ⟨ε, hε, hmem⟩ := hx a ha
        have hsub : convexHull ℝ D ⊆ {z | inner ℝ d z ≤ inner ℝ d x} := by
          refine convexHull_min ?_ ?_
          · intro z hz
            have := hd z hz
            simp only [Set.mem_setOf_eq]
            rw [inner_sub_right] at this
            linarith
          · exact convex_halfSpace_le (innerₛₗ ℝ d).isLinear _
        have h2 := hsub hmem
        simp only [Set.mem_setOf_eq, inner_add_right, real_inner_smul_right] at h2
        have h3 : 0 ≤ inner ℝ d (x - a) := hd a ha
        have h4 : ε * inner ℝ d (x - a) ≤ 0 := by linarith
        have h5 : inner ℝ d (x - a) ≤ 0 := by
          by_contra h
          push_neg at h
          have := mul_pos hε h
          linarith
        linarith
      have hker : L ≤ LinearMap.ker (innerₛₗ ℝ d) := by
        rw [hL, Submodule.span_le]
        rintro _ ⟨a, ha, rfl⟩
        simp [innerₛₗ_apply_apply, hzero a ha]
      have := hker hdL
      simpa [innerₛₗ_apply_apply] using this
    have proj : ∀ p : E, ∃ p' ∈ L, ∀ a ∈ D, inner ℝ p' (x - a) = inner ℝ p (x - a) := by
      intro p
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := L) p
      refine ⟨y, hy, fun a ha => ?_⟩
      have hxa : x - a ∈ L := by
        have h1 : a - x ∈ L := Submodule.subset_span ⟨a, ha, rfl⟩
        have h2 := L.neg_mem h1
        simpa using h2
      rw [inner_add_left, Submodule.inner_left_of_mem_orthogonal hxa hz, add_zero]
    set Kc : Set (E × ℝ) :=
      (Prod.fst ⁻¹' (L : Set E)) ∩ ({q | ‖q.1‖ + q.2 = 1} ∩ {q | 0 ≤ q.2}) with hKc
    have hKcomp : IsCompact Kc := by
      apply Metric.isCompact_of_isClosed_isBounded
      · refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
        · exact (L.closed_of_finiteDimensional).preimage continuous_fst
        · exact isClosed_eq ((continuous_norm.comp continuous_fst).add continuous_snd)
            continuous_const
        · exact isClosed_le continuous_const continuous_snd
      · rw [Metric.isBounded_iff_subset_closedBall 0]
        refine ⟨1, fun q hq => ?_⟩
        rw [mem_closedBall_zero_iff, Prod.norm_def]
        obtain ⟨_, h1, h2⟩ := hq
        simp only [Set.mem_setOf_eq] at h1 h2
        have hn := norm_nonneg q.1
        refine max_le (by linarith) ?_
        rw [Real.norm_eq_abs, abs_of_nonneg h2]
        linarith
    let H : {q : E × E // q.2 ∈ T q.1} → Set (E × ℝ) :=
      fun g => {q | 0 ≤ inner ℝ (q.1 - q.2 • g.1.2) (x - g.1.1)}
    have hHc : ∀ g, IsClosed (H g) := by
      intro g
      exact isClosed_le continuous_const
        ((continuous_fst.sub (continuous_snd.smul continuous_const)).inner continuous_const)
    have hfin : ∀ u : Finset {q : E × E // q.2 ∈ T q.1}, (Kc ∩ ⋂ g ∈ u, H g).Nonempty := by
      intro u
      obtain ⟨p, hp⟩ := finite_ext (u.image Subtype.val) (by
        intro q hq q' hq'
        obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨g', _, rfl⟩ := Finset.mem_image.mp hq'
        exact hT.1 _ _ _ _ g'.2 g.2) x
      obtain ⟨p', hp'L, hp'⟩ := proj p
      set c : ℝ := (1 + ‖p'‖)⁻¹ with hc
      have hden : 0 < 1 + ‖p'‖ := by positivity
      have hcpos : 0 < c := by positivity
      refine ⟨(c • p', c), ⟨?_, ?_, hcpos.le⟩, ?_⟩
      · exact L.smul_mem c hp'L
      · simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
        rw [hc]
        field_simp
        ring
      · simp only [Set.mem_iInter]
        intro g hg
        simp only [H, Set.mem_setOf_eq]
        have hga : g.1.1 ∈ D := ⟨g.1.2, g.2⟩
        have := hp g.1 (Finset.mem_image_of_mem _ hg)
        rw [← smul_sub, real_inner_smul_left, inner_sub_left, hp' g.1.1 hga, ← inner_sub_left]
        exact mul_nonneg hcpos.le this
    obtain ⟨⟨p, t⟩, ⟨hpL, hnorm, ht⟩, hH⟩ := hKcomp.inter_iInter_nonempty H hHc hfin
    simp only [Set.mem_iInter] at hH
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe] at hpL hnorm ht
    rcases ht.eq_or_lt with rfl | htpos
    · exfalso
      have hp0 : p = 0 := key p hpL (by
        intro a ha
        obtain ⟨b, hb⟩ := ha
        have := hH ⟨(a, b), hb⟩
        simpa [H] using this)
      simp [hp0] at hnorm
    · refine ⟨t⁻¹ • p, ?_⟩
      by_contra hnot
      obtain ⟨x', v', hv', hlt⟩ := hT.2 x (t⁻¹ • p) hnot
      have := hH ⟨(x', v'), hv'⟩
      simp only [H, Set.mem_setOf_eq] at this
      have heq : p - t • v' = t • (t⁻¹ • p - v') := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
      rw [heq, real_inner_smul_left] at this
      have := (mul_nonneg_iff_of_pos_left htpos).mp this
      linarith
  -- The domain of a maximal monotone operator is nearly convex.
  have dom_nc : ∀ (T : E → Set E), IsMaximalMonotone T →
      ∃ C : Set E, Convex ℝ C ∧ C ⊆ {x | (T x).Nonempty} ∧
        {x | (T x).Nonempty} ⊆ closure C := by
    intro T hT
    classical
    set D : Set E := {x | (T x).Nonempty} with hD
    set K : Set E := convexHull ℝ D with hK
    have hKconv : Convex ℝ K := convex_convexHull ℝ D
    have hDK : D ⊆ K := subset_convexHull ℝ D
    have shrink : ∀ z a : E, ∀ ε δ : ℝ, z ∈ K → 0 < ε → z + ε • (z - a) ∈ K → 0 ≤ δ → δ ≤ ε →
        z + δ • (z - a) ∈ K := by
      intro z a ε δ hz hε hzε hδ hδε
      have := hKconv.add_smul_mem hz hzε (t := δ / ε) ⟨div_nonneg hδ hε.le, (div_le_one hε).mpr hδε⟩
      rwa [smul_smul, div_mul_cancel₀ _ hε.ne'] at this
    refine ⟨{z | z ∈ K ∧ ∀ a ∈ D, ∃ ε > (0:ℝ), z + ε • (z - a) ∈ K}, ?_, ?_, ?_⟩
    · rintro z₁ ⟨hz₁, h₁⟩ z₂ ⟨hz₂, h₂⟩ α β hα hβ hαβ
      refine ⟨hKconv hz₁ hz₂ hα hβ hαβ, fun a ha => ?_⟩
      obtain ⟨ε₁, hε₁, hm₁⟩ := h₁ a ha
      obtain ⟨ε₂, hε₂, hm₂⟩ := h₂ a ha
      refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
      have k₁ := shrink z₁ a ε₁ (min ε₁ ε₂) hz₁ hε₁ hm₁ (le_min hε₁.le hε₂.le) (min_le_left _ _)
      have k₂ := shrink z₂ a ε₂ (min ε₁ ε₂) hz₂ hε₂ hm₂ (le_min hε₁.le hε₂.le) (min_le_right _ _)
      have := hKconv k₁ k₂ hα hβ hαβ
      have hβ' : β = 1 - α := by linarith
      subst hβ'
      have heq : α • z₁ + (1 - α) • z₂ + min ε₁ ε₂ • (α • z₁ + (1 - α) • z₂ - a) =
          α • (z₁ + min ε₁ ε₂ • (z₁ - a)) + (1 - α) • (z₂ + min ε₁ ε₂ • (z₂ - a)) := by
        module
      rw [heq]
      exact this
    · rintro z ⟨_, h⟩
      exact mem_dom T hT z h
    · rcases D.eq_empty_or_nonempty with hDe | hDne
      · rw [hDe]; exact Set.empty_subset _
      obtain ⟨c, hc⟩ := (hDne.mono hDK).intrinsicInterior hKconv
      have hcK : c ∈ K := intrinsicInterior_subset hc
      have hcC : ∀ a ∈ D, ∃ ε > (0:ℝ), c + ε • (c - a) ∈ K := by
        intro a ha
        obtain ⟨c', hc'int, rfl⟩ := hc
        have haA : a ∈ affineSpan ℝ K := subset_affineSpan ℝ K (hDK ha)
        have hmemA : ∀ s : ℝ, (c' : E) + s • ((c' : E) - a) ∈ affineSpan ℝ K := by
          intro s
          have h1 : (c' : E) -ᵥ a ∈ (affineSpan ℝ K).direction :=
            AffineSubspace.vsub_mem_direction c'.2 haA
          have h2 := AffineSubspace.vadd_mem_of_mem_direction
            ((affineSpan ℝ K).direction.smul_mem s h1) c'.2
          rw [vsub_eq_sub, vadd_eq_add, add_comm] at h2
          exact h2
        let γ : ℝ → affineSpan ℝ K := fun s => ⟨(c' : E) + s • ((c' : E) - a), hmemA s⟩
        have hγc : Continuous γ := by
          apply Continuous.subtype_mk
          exact continuous_const.add (continuous_id.smul continuous_const)
        have hγ0 : γ 0 = c' := by
          apply Subtype.ext
          simp [γ]
        have hopen : IsOpen (γ ⁻¹' interior ((↑) ⁻¹' K)) := isOpen_interior.preimage hγc
        have h0 : (0:ℝ) ∈ γ ⁻¹' interior ((↑) ⁻¹' K) := by
          rw [Set.mem_preimage, hγ0]
          exact hc'int
        obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
        refine ⟨δ / 2, by positivity, ?_⟩
        have hmem : δ / 2 ∈ Metric.ball (0:ℝ) δ := by
          rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos (by positivity)]
          linarith
        have h3 : γ (δ / 2) ∈ interior ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := hball hmem
        have h4 : γ (δ / 2) ∈ ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := interior_subset h3
        exact h4
      intro d hd
      have hseg : openSegment ℝ c d ⊆ {z | z ∈ K ∧ ∀ a ∈ D, ∃ ε > (0:ℝ), z + ε • (z - a) ∈ K} := by
        rintro z ⟨α, β, hα, hβ, hαβ, rfl⟩
        refine ⟨hKconv hcK (hDK hd) hα.le hβ.le hαβ, fun a ha => ?_⟩
        obtain ⟨ε₀, hε₀, hm₀⟩ := hcC a ha
        have hden : 0 < 1 + ε₀ * β := by positivity
        set ε : ℝ := ε₀ * α / (1 + ε₀ * β) with hε
        set α' : ℝ := α / (1 + ε₀ * β) with hα'
        set β' : ℝ := β * (1 + ε₀) / (1 + ε₀ * β) with hβ'
        have hcomb := hKconv hm₀ (hDK hd) (a := α') (b := β') (by positivity) (by positivity)
          (by rw [hα', hβ']; field_simp; linarith)
        have e1 : (1 + ε) * α = α' * (1 + ε₀) := by
          rw [hε, hα']; field_simp; linear_combination ε₀ * hαβ
        have e2 : (1 + ε) * β = β' := by
          rw [hε, hβ']; field_simp; linear_combination ε₀ * hαβ
        have e3 : ε = α' * ε₀ := by
          rw [hε, hα']; ring
        refine ⟨ε, by positivity, ?_⟩
        have heq : α • c + β • d + ε • (α • c + β • d - a) =
            α' • (c + ε₀ • (c - a)) + β' • d := by
          calc α • c + β • d + ε • (α • c + β • d - a)
              = ((1 + ε) * α) • c + ((1 + ε) * β) • d - ε • a := by module
            _ = (α' * (1 + ε₀)) • c + β' • d - (α' * ε₀) • a := by rw [e1, e2, ← e3]
            _ = α' • (c + ε₀ • (c - a)) + β' • d := by module
        rw [heq]
        exact hcomb
      exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ c d))
  -- The inverse of a maximal monotone operator is maximal monotone.
  have inv_max : IsMaximalMonotone (fun v => {x | v ∈ T x}) := by
    refine ⟨?_, ?_⟩
    · intro x₀ x₁ v₀ v₁ h₀ h₁
      have := hT.1 v₀ v₁ x₀ x₁ h₀ h₁
      rwa [real_inner_comm] at this
    · intro xh vh hnot
      obtain ⟨xt, vt, hvt, hlt⟩ := hT.2 vh xh hnot
      exact ⟨vt, xt, hvt, by rwa [real_inner_comm]⟩
  intro domT rgeT
  refine ⟨dom_nc T hT, ?_⟩
  obtain ⟨C, hC, h1, h2⟩ := dom_nc _ inv_max
  have hset : {v | ({x | v ∈ T x} : Set E).Nonempty} = rgeT := by
    ext v
    simp [rgeT, Set.Nonempty]
  rw [hset] at h1 h2
  exact ⟨C, hC, h1, h2⟩

end RW_chap_12_41
