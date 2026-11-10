import ConvexStarLib.Defs

/-!
# `Duchi_Q9_1`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_Q9_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_Q9_1`, so the main result is `Duchi_Q9_1.Duchi_Q9_1`.
-/

namespace Duchi_Q9_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace DuchiPL

lemma bm1_homothety (c r x : ℝ) : AffineMap.homothety c r x = r * x + (1 - r) * c := by
  simp [AffineMap.homothety_apply]; ring

lemma bm1_compact {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {K L C : Set ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hC : ∀ x ∈ K, ∀ y ∈ L, l * x + (1 - l) * y ∈ C) :
    ENNReal.ofReal l * volume K + ENNReal.ofReal (1 - l) * volume L ≤ volume C := by
  have ha : sSup K ∈ K := hK.sSup_mem hKne
  have hb : sInf L ∈ L := hL.sInf_mem hLne
  have hX : volume (AffineMap.homothety (sInf L) l '' K) = ENNReal.ofReal l * volume K := by
    rw [Measure.addHaar_image_homothety, Module.finrank_self, pow_one, abs_of_pos hl0]
  have hY : volume (AffineMap.homothety (sSup K) (1 - l) '' L)
      = ENNReal.ofReal (1 - l) * volume L := by
    rw [Measure.addHaar_image_homothety, Module.finrank_self, pow_one,
      abs_of_pos (by linarith)]
  have hXC : AffineMap.homothety (sInf L) l '' K ∪ AffineMap.homothety (sSup K) (1 - l) '' L
      ⊆ C := by
    rintro z (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · rw [bm1_homothety]; exact hC x hx _ hb
    · rw [bm1_homothety]; convert hC _ ha y hy using 1; ring
  have hXY : AffineMap.homothety (sInf L) l '' K ∩ AffineMap.homothety (sSup K) (1 - l) '' L
      ⊆ {l * sSup K + (1 - l) * sInf L} := by
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyz⟩⟩
    have hxa : x ≤ sSup K := le_csSup hK.bddAbove hx
    have hby : sInf L ≤ y := csInf_le hL.bddBelow hy
    simp only [bm1_homothety] at hyz ⊢
    rw [Set.mem_singleton_iff]
    have h1 := mul_le_mul_of_nonneg_left hxa hl0.le
    have h2 := mul_le_mul_of_nonneg_left hby (sub_nonneg.2 hl1.le)
    linarith
  have hYm : MeasurableSet (AffineMap.homothety (sSup K) (1 - l) '' L) :=
    (hL.image (AffineMap.homothety_continuous _ _)).measurableSet
  calc ENNReal.ofReal l * volume K + ENNReal.ofReal (1 - l) * volume L
      = volume (AffineMap.homothety (sInf L) l '' K)
        + volume (AffineMap.homothety (sSup K) (1 - l) '' L) := by rw [hX, hY]
    _ = volume (AffineMap.homothety (sInf L) l '' K
          ∪ AffineMap.homothety (sSup K) (1 - l) '' L) :=
        (measure_union₀ hYm.nullMeasurableSet (measure_mono_null hXY (measure_singleton _))).symm
    _ ≤ volume C := measure_mono hXC

lemma bm1_vol_le_iSup {A : Set ℝ} (hA : MeasurableSet A) (hAne : A.Nonempty) (d : ℝ≥0∞) :
    d * volume A ≤ ⨆ K : {K : Set ℝ // K ⊆ A ∧ IsCompact K ∧ K.Nonempty}, d * volume K.1 := by
  rw [← ENNReal.mul_iSup]
  gcongr
  rw [hA.measure_eq_iSup_isCompact]
  obtain ⟨a0, ha0⟩ := hAne
  refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
  refine le_trans (measure_mono (Set.subset_union_left : K ⊆ K ∪ {a0})) ?_
  exact le_iSup (fun K : {K : Set ℝ // K ⊆ A ∧ IsCompact K ∧ K.Nonempty} => volume K.1)
    ⟨K ∪ {a0}, Set.union_subset hKA (Set.singleton_subset_iff.2 ha0),
      hK.union isCompact_singleton, ⟨a0, Or.inr rfl⟩⟩

/-- 1D Brunn–Minkowski. -/
lemma bm1 {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hC : ∀ x ∈ A, ∀ y ∈ B, l * x + (1 - l) * y ∈ C) :
    ENNReal.ofReal l * volume A + ENNReal.ofReal (1 - l) * volume B ≤ volume C := by
  haveI : Nonempty {K : Set ℝ // K ⊆ A ∧ IsCompact K ∧ K.Nonempty} :=
    ⟨⟨{hAne.some}, Set.singleton_subset_iff.2 hAne.some_mem, isCompact_singleton,
      Set.singleton_nonempty _⟩⟩
  haveI : Nonempty {L : Set ℝ // L ⊆ B ∧ IsCompact L ∧ L.Nonempty} :=
    ⟨⟨{hBne.some}, Set.singleton_subset_iff.2 hBne.some_mem, isCompact_singleton,
      Set.singleton_nonempty _⟩⟩
  calc ENNReal.ofReal l * volume A + ENNReal.ofReal (1 - l) * volume B
      ≤ (⨆ K : {K : Set ℝ // K ⊆ A ∧ IsCompact K ∧ K.Nonempty}, ENNReal.ofReal l * volume K.1)
        + ⨆ L : {L : Set ℝ // L ⊆ B ∧ IsCompact L ∧ L.Nonempty},
            ENNReal.ofReal (1 - l) * volume L.1 :=
        add_le_add (bm1_vol_le_iSup hA hAne _) (bm1_vol_le_iSup hB hBne _)
    _ ≤ volume C := ENNReal.iSup_add_iSup_le fun K L =>
        bm1_compact hl0 hl1 K.2.2.1 L.2.2.1 K.2.2.2 L.2.2.2
          (fun x hx y hy => hC x (K.2.1 hx) y (L.2.1 hy))

/-- Layer cake for a finite-valued `ℝ≥0∞` function on `ℝ`. -/
lemma pl1core_layercake {u : ℝ → ℝ≥0∞} (hu : Measurable u) (hu1 : ∀ x, u x ≠ ⊤) :
    ∫⁻ x, u x = ∫⁻ t in Set.Ioi 0, volume {x | ENNReal.ofReal t < u x} := by
  have h1 : (fun x => u x) = fun x => ENNReal.ofReal ((u x).toReal) := by
    funext x; rw [ENNReal.ofReal_toReal (hu1 x)]
  rw [h1, lintegral_eq_lintegral_meas_lt volume
    (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg)) hu.ennreal_toReal.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hu1 x)).symm

/-- Superlevel-set measure is antitone, hence measurable. -/
lemma pl1core_meas {u : ℝ → ℝ≥0∞} :
    Measurable (fun t : ℝ => volume {x | ENNReal.ofReal t < u x}) := by
  apply Antitone.measurable
  intro s t hst
  apply measure_mono
  intro x hx
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hx

/-- Layer-cake core: normalized 1D Prékopa–Leindler (sup f = sup g = 1). -/
lemma pl1_core {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ t < (1 : ℝ≥0∞), ∃ x, t < f x) (hgs : ∀ t < (1 : ℝ≥0∞), ∃ x, t < g x)
    (H : ∀ x y, f x ^ l * g y ^ (1 - l) ≤ h (l * x + (1 - l) * y)) :
    ENNReal.ofReal l * (∫⁻ x, f x) + ENNReal.ofReal (1 - l) * (∫⁻ x, g x) ≤ ∫⁻ x, h x := by
  have hF := pl1core_layercake hf (fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 x))
  have hG := pl1core_layercake hg (fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 x))
  have hK := pl1core_layercake (u := fun x => min (h x) 1) (hh.min measurable_const)
    (fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  have key : ∀ t ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal l * volume {x | ENNReal.ofReal t < f x}
        + ENNReal.ofReal (1 - l) * volume {x | ENNReal.ofReal t < g x}
        ≤ volume {x | ENNReal.ofReal t < min (h x) 1} := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rcases lt_or_ge t 1 with ht1 | ht1
    · have ht1' : ENNReal.ofReal t < 1 := ENNReal.ofReal_lt_one.mpr ht1
      apply bm1 hl0 hl1 (measurableSet_lt measurable_const hf)
        (measurableSet_lt measurable_const hg)
      · obtain ⟨x, hx⟩ := hfs (ENNReal.ofReal t) ht1'
        exact ⟨x, hx⟩
      · obtain ⟨x, hx⟩ := hgs (ENNReal.ofReal t) ht1'
        exact ⟨x, hx⟩
      · intro x hx y hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        refine lt_min ?_ ht1'
        have hne0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht0).ne'
        calc ENNReal.ofReal t = ENNReal.ofReal t ^ (l + (1 - l)) := by
              rw [add_sub_cancel, ENNReal.rpow_one]
          _ = ENNReal.ofReal t ^ l * ENNReal.ofReal t ^ (1 - l) :=
              ENNReal.rpow_add _ _ hne0 ENNReal.ofReal_ne_top
          _ < f x ^ l * g y ^ (1 - l) :=
              ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx hl0)
                (ENNReal.rpow_lt_rpow hy (by linarith))
          _ ≤ h (l * x + (1 - l) * y) := H x y
    · have h1t : (1 : ℝ≥0∞) ≤ ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ht1
      have hF0 : volume {x | ENNReal.ofReal t < f x} = 0 := by
        have : {x | ENNReal.ofReal t < f x} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
          exact (hf1 x).trans h1t
        rw [this, measure_empty]
      have hG0 : volume {x | ENNReal.ofReal t < g x} = 0 := by
        have : {x | ENNReal.ofReal t < g x} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
          exact (hg1 x).trans h1t
        rw [this, measure_empty]
      rw [hF0, hG0, mul_zero, mul_zero, add_zero]
      exact zero_le _
  calc ENNReal.ofReal l * (∫⁻ x, f x) + ENNReal.ofReal (1 - l) * (∫⁻ x, g x)
      = ∫⁻ t in Set.Ioi 0, (ENNReal.ofReal l * volume {x | ENNReal.ofReal t < f x}
          + ENNReal.ofReal (1 - l) * volume {x | ENNReal.ofReal t < g x}) := by
        rw [hF, hG, lintegral_add_left (pl1core_meas.const_mul _),
          lintegral_const_mul _ pl1core_meas, lintegral_const_mul _ pl1core_meas]
    _ ≤ ∫⁻ t in Set.Ioi 0, volume {x | ENNReal.ofReal t < min (h x) 1} :=
        setLIntegral_mono' measurableSet_Ioi key
    _ = ∫⁻ x, min (h x) 1 := hK.symm
    _ ≤ ∫⁻ x, h x := lintegral_mono (fun x => min_le_left _ _)

lemma pl1_amgm {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (X Y : ℝ≥0∞) :
    X ^ l * Y ^ (1 - l) ≤ ENNReal.ofReal l * X + ENNReal.ofReal (1 - l) * Y := by
  have hl1' : 0 < 1 - l := by linarith
  rcases eq_or_ne X ⊤ with rfl | hX
  · have : ENNReal.ofReal l * ⊤ = ⊤ := ENNReal.mul_top (by simpa using hl0)
    rw [this, top_add]; exact le_top
  rcases eq_or_ne Y ⊤ with rfl | hY
  · have : ENNReal.ofReal (1 - l) * ⊤ = ⊤ := ENNReal.mul_top (by simpa using hl1')
    rw [this, add_top]; exact le_top
  lift X to ℝ≥0 using hX
  lift Y to ℝ≥0 using hY
  have key := NNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal l) (Real.toNNReal (1 - l))
    X Y (by rw [← Real.toNNReal_add hl0.le hl1'.le]; simp)
  rw [Real.coe_toNNReal _ hl0.le, Real.coe_toNNReal _ hl1'.le] at key
  rw [← ENNReal.coe_rpow_of_nonneg _ hl0.le, ← ENNReal.coe_rpow_of_nonneg _ hl1'.le,
    ENNReal.ofReal, ENNReal.ofReal]
  exact_mod_cast key

lemma pl1_bdd {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (N : ℝ≥0∞) (hN : N ≠ ⊤)
    (hfN : ∀ x, f x ≤ N) (hgN : ∀ x, g x ≤ N)
    (H : ∀ x y, f x ^ l * g y ^ (1 - l) ≤ h (l * x + (1 - l) * y)) :
    (∫⁻ x, f x) ^ l * (∫⁻ x, g x) ^ (1 - l) ≤ ∫⁻ x, h x := by
  have hl1' : 0 < 1 - l := by linarith
  set a := ⨆ x, f x with ha_def
  set b := ⨆ x, g x with hb_def
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top hN (iSup_le hfN)
  have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top hN (iSup_le hgN)
  by_cases ha0 : a = 0
  · have : ∀ x, f x = 0 := fun x => le_antisymm (ha0 ▸ le_iSup f x) (zero_le _)
    simp [this, ENNReal.zero_rpow_of_pos hl0]
  by_cases hb0 : b = 0
  · have : ∀ x, g x = 0 := fun x => le_antisymm (hb0 ▸ le_iSup g x) (zero_le _)
    simp [this, ENNReal.zero_rpow_of_pos hl1']
  set c := (a ^ l)⁻¹ * (b ^ (1 - l))⁻¹ with hc_def
  have hc0 : c ≠ 0 := by
    apply mul_ne_zero
    · exact ENNReal.inv_ne_zero.2 (ENNReal.rpow_ne_top_of_nonneg hl0.le hatop)
    · exact ENNReal.inv_ne_zero.2 (ENNReal.rpow_ne_top_of_nonneg hl1'.le hbtop)
  have hctop : c ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.2 (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hatop).ne'
    · exact ENNReal.inv_ne_top.2 (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hbtop).ne'
  have core := pl1_core hl0 hl1 (f := fun x => f x * a⁻¹) (g := fun x => g x * b⁻¹)
    (h := fun x => h x * c) (hf.mul_const _) (hg.mul_const _) (hh.mul_const _)
    (fun x => by
      calc f x * a⁻¹ ≤ a * a⁻¹ := by gcongr; exact le_iSup f x
        _ = 1 := ENNReal.mul_inv_cancel ha0 hatop)
    (fun x => by
      calc g x * b⁻¹ ≤ b * b⁻¹ := by gcongr; exact le_iSup g x
        _ = 1 := ENNReal.mul_inv_cancel hb0 hbtop)
    (fun t ht => by
      have h1 : t * a < a := by
        simpa using ENNReal.mul_lt_mul_left ha0 hatop ht
      obtain ⟨x, hx⟩ := lt_iSup_iff.1 h1
      refine ⟨x, ?_⟩
      show t < f x * a⁻¹
      rw [← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)]
      exact hx)
    (fun t ht => by
      have h1 : t * b < b := by
        simpa using ENNReal.mul_lt_mul_left hb0 hbtop ht
      obtain ⟨x, hx⟩ := lt_iSup_iff.1 h1
      refine ⟨x, ?_⟩
      show t < g x * b⁻¹
      rw [← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl hb0) (Or.inl hbtop)]
      exact hx)
    (fun x y => by
      simp only
      rw [ENNReal.mul_rpow_of_nonneg _ _ hl0.le, ENNReal.mul_rpow_of_nonneg _ _ hl1'.le,
        ENNReal.inv_rpow, ENNReal.inv_rpow, mul_mul_mul_comm]
      gcongr
      exact H x y)
  rw [lintegral_mul_const _ hf, lintegral_mul_const _ hg, lintegral_mul_const _ hh] at core
  have am := pl1_amgm hl0 hl1 ((∫⁻ x, f x) * a⁻¹) ((∫⁻ x, g x) * b⁻¹)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hl0.le, ENNReal.mul_rpow_of_nonneg _ _ hl1'.le,
    ENNReal.inv_rpow, ENNReal.inv_rpow, mul_mul_mul_comm] at am
  exact (ENNReal.mul_le_mul_iff_left hc0 hctop).1 (am.trans core)

lemma pl1_lim {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {a b : ℕ → ℝ≥0∞} (ha : Monotone a)
    (hb : Monotone b) {C : ℝ≥0∞} (hC : ∀ n, a n ^ l * b n ^ (1 - l) ≤ C) :
    (⨆ n, a n) ^ l * (⨆ n, b n) ^ (1 - l) ≤ C := by
  have hl1' : 0 < 1 - l := by linarith
  have e1 : (⨆ n, a n) ^ l = ⨆ n, a n ^ l := (ENNReal.orderIsoRpow l hl0).map_iSup a
  have e2 : (⨆ n, b n) ^ (1 - l) = ⨆ n, b n ^ (1 - l) :=
    (ENNReal.orderIsoRpow (1 - l) hl1').map_iSup b
  rw [e1, e2, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  calc a n ^ l * b m ^ (1 - l) ≤ a (max n m) ^ l * b (max n m) ^ (1 - l) := by
        gcongr
        · exact ha (le_max_left n m)
        · exact hb (le_max_right n m)
    _ ≤ C := hC _

/-- 1D Prékopa–Leindler. -/
lemma pl1 {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (H : ∀ x y, f x ^ l * g y ^ (1 - l) ≤ h (l * x + (1 - l) * y)) :
    (∫⁻ x, f x) ^ l * (∫⁻ x, g x) ^ (1 - l) ≤ ∫⁻ x, h x := by
  have hl1' : 0 < 1 - l := by linarith
  let fN : ℕ → ℝ → ℝ≥0∞ := fun n x => min (f x) (n : ℝ≥0∞)
  let gN : ℕ → ℝ → ℝ≥0∞ := fun n x => min (g x) (n : ℝ≥0∞)
  have hfNm : ∀ n, Measurable (fN n) := fun n => hf.min measurable_const
  have hgNm : ∀ n, Measurable (gN n) := fun n => hg.min measurable_const
  have hfNmono : Monotone fN := fun m n hmn x =>
    min_le_min_left _ (by exact_mod_cast hmn)
  have hgNmono : Monotone gN := fun m n hmn x =>
    min_le_min_left _ (by exact_mod_cast hmn)
  have hsup : ∀ u : ℝ≥0∞, ⨆ n : ℕ, min u (n : ℝ≥0∞) = u := by
    intro u
    have := (inf_iSup_eq u (fun n : ℕ => (n : ℝ≥0∞))).symm
    rw [ENNReal.iSup_natCast] at this
    simpa using this
  have hFlim : ∫⁻ x, f x = ⨆ n, ∫⁻ x, fN n x := by
    rw [← lintegral_iSup hfNm hfNmono]
    simp only [fN, hsup]
  have hGlim : ∫⁻ x, g x = ⨆ n, ∫⁻ x, gN n x := by
    rw [← lintegral_iSup hgNm hgNmono]
    simp only [gN, hsup]
  rw [hFlim, hGlim]
  refine pl1_lim hl0 hl1 (fun m n hmn => lintegral_mono (hfNmono hmn))
    (fun m n hmn => lintegral_mono (hgNmono hmn)) (fun n => ?_)
  refine pl1_bdd hl0 hl1 (hfNm n) (hgNm n) hh (n : ℝ≥0∞) (ENNReal.natCast_ne_top n)
    (fun x => min_le_right _ _) (fun x => min_le_right _ _) (fun x y => ?_)
  calc fN n x ^ l * gN n y ^ (1 - l) ≤ f x ^ l * g y ^ (1 - l) := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_left _ _
    _ ≤ h (l * x + (1 - l) * y) := H x y

/-- Prékopa–Leindler property of a measure on a real vector space. -/
def PLHolds (X : Type*) [AddCommGroup X] [Module ℝ X] [MeasurableSpace X] (μ : Measure X) :
    Prop :=
  ∀ l : ℝ, 0 < l → l < 1 → ∀ f g h : X → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ l * g y ^ (1 - l) ≤ h (l • x + (1 - l) • y)) →
    (∫⁻ x, f x ∂μ) ^ l * (∫⁻ x, g x ∂μ) ^ (1 - l) ≤ ∫⁻ x, h x ∂μ

lemma plh_lin_symm {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y]
    (e : X ≃ᵐ Y)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y) :
    ∀ (a b : ℝ) (x y : Y), e.symm (a • x + b • y) = a • e.symm x + b • e.symm y := by
  intro a b x y
  apply e.injective
  rw [hlin]
  simp

lemma plHolds_real : PLHolds ℝ volume := by
  intro l hl0 hl1 f g h hf hg hh H
  exact pl1 hl0 hl1 hf hg hh (fun x y => by simpa only [smul_eq_mul] using H x y)

lemma plHolds_prod {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν]
    (hX : PLHolds X μ) (hY : PLHolds Y ν) : PLHolds (X × Y) (μ.prod ν) := by
  intro l hl0 hl1 f g h hf hg hh H
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable,
    lintegral_prod _ hh.aemeasurable]
  refine hX l hl0 hl1 (fun s => ∫⁻ y, f (s, y) ∂ν) (fun s => ∫⁻ y, g (s, y) ∂ν)
    (fun s => ∫⁻ y, h (s, y) ∂ν) hf.lintegral_prod_right' hg.lintegral_prod_right'
    hh.lintegral_prod_right' ?_
  intro s t
  refine hY l hl0 hl1 (fun y => f (s, y)) (fun y => g (t, y))
    (fun y => h (l • s + (1 - l) • t, y))
    (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)
    (hh.comp measurable_prodMk_left) ?_
  intro x y
  have := H (s, x) (t, y)
  simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

lemma plHolds_map {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y)
    (hmp : MeasurePreserving e μ ν) (hX : PLHolds X μ) : PLHolds Y ν := by
  intro l hl0 hl1 f g h hf hg hh H
  have key := hX l hl0 hl1 (fun x => f (e x)) (fun x => g (e x)) (fun x => h (e x))
    (hf.comp e.measurable) (hg.comp e.measurable) (hh.comp e.measurable)
    (fun x y => by simpa only [hlin] using H (e x) (e y))
  simpa only [hmp.lintegral_comp_emb e.measurableEmbedding] using key

lemma plHolds_pi_fin : ∀ n : ℕ, PLHolds (Fin n → ℝ) volume := by
  intro n
  induction n with
  | zero =>
    intro l hl0 hl1 f g h hf hg hh H
    have h1 : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
      rw [Measure.volume_pi_eq_dirac]; exact measure_univ
    simp only [lintegral_unique, h1, mul_one]
    convert H default default
  | succ n ih =>
    have hprod : PLHolds (ℝ × (Fin n → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      plHolds_prod plHolds_real ih
    refine plHolds_map (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm ?_ ?_ hprod
    · apply plh_lin_symm
      intro a b x y
      ext <;> simp [Fin.tail]
    · exact (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0).symm _

lemma plHolds_euclidean (n : ℕ) : PLHolds (EuclideanSpace ℝ (Fin n)) volume := by
  refine plHolds_map (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ?_
    (PiLp.volume_preserving_toLp (Fin n)) (plHolds_pi_fin n)
  intro a b x y
  rfl





lemma explc_conv_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u : F → EReal) (hu : ConvexEReal u) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x y : F)
    (a b : ℝ) (ha : u x ≤ (a : EReal)) (hb : u y ≤ (b : EReal)) :
    u (c • x + (1 - c) • y) ≤ ((c * a + (1 - c) * b : ℝ) : EReal) := by
  have hpx : (x, a) ∈ epigraph u := ha
  have hpy : (y, b) ∈ epigraph u := hb
  have h := hu hpx hpy hc0 (by linarith : (0:ℝ) ≤ 1 - c) (by ring)
  have h2 : (c • (x, a) + (1 - c) • (y, b) : F × ℝ) =
      (c • x + (1 - c) • y, c * a + (1 - c) * b) := by
    ext <;> simp [smul_eq_mul]
  rw [h2] at h
  exact h

/-- Log-concavity of `exp(-u)` for convex `u`. -/
lemma expNegWT_logconcave {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u : F → EReal) (hu : InConvRn u) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (x y : F) :
    ENNReal.ofReal (expNegWT (u x)) ^ c * ENNReal.ofReal (expNegWT (u y)) ^ (1 - c) ≤
      ENNReal.ofReal (expNegWT (u (c • x + (1 - c) • y))) := by
  have hc1' : 0 < 1 - c := by linarith
  by_cases hx : u x = ⊤
  · rw [hx]; simp [expNegWT, ENNReal.zero_rpow_of_pos hc0]
  by_cases hy : u y = ⊤
  · rw [hy]; simp [expNegWT, ENNReal.zero_rpow_of_pos hc1']
  have hxa : u x = ((u x).toReal : EReal) := (EReal.coe_toReal hx (hu.1 x).ne').symm
  have hyb : u y = ((u y).toReal : EReal) := (EReal.coe_toReal hy (hu.1 y).ne').symm
  have hz := explc_conv_le u hu.2.2 hc0.le hc1.le x y (u x).toReal (u y).toReal hxa.le hyb.le
  have hzt : u (c • x + (1 - c) • y) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hz
  have hzb : u (c • x + (1 - c) • y) ≠ ⊥ := (hu.1 _).ne'
  have hzle : (u (c • x + (1 - c) • y)).toReal ≤ c * (u x).toReal + (1 - c) * (u y).toReal := by
    have := EReal.toReal_le_toReal hz hzb (EReal.coe_ne_top _)
    simpa using this
  simp only [expNegWT, hx, hy, hzt, if_false]
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hc0.le,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hc1'.le,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A measure with log-concave density is log-concave (from Prékopa–Leindler). -/
lemma logconcave_of_density {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f)
    (hlc : ∀ c : ℝ, 0 < c → c < 1 → ∀ x y, f x ^ c * f y ^ (1 - c) ≤ f (c • x + (1 - c) • y)) :
    IsLogConcaveMeasure (volume.withDensity f) := by
  intro A B c hA hB hc0 hc1
  have hS : IsCompact (c • A + (1 - c) • B) := (hA.smul c).add (hB.smul (1 - c))
  have hAm : MeasurableSet A := hA.measurableSet
  have hBm : MeasurableSet B := hB.measurableSet
  have hSm : MeasurableSet (c • A + (1 - c) • B) := hS.measurableSet
  have hc1' : 0 < 1 - c := sub_pos.mpr hc1
  have key := plHolds_euclidean n c hc0 hc1 (A.indicator f) (B.indicator f)
    ((c • A + (1 - c) • B).indicator f) (hf.indicator hAm) (hf.indicator hBm)
    (hf.indicator hSm) ?_
  · rw [lintegral_indicator hAm, lintegral_indicator hBm, lintegral_indicator hSm] at key
    rw [withDensity_apply f hAm, withDensity_apply f hBm, withDensity_apply f hSm]
    exact key
  · intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hmem : c • x + (1 - c) • y ∈ c • A + (1 - c) • B :=
          Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hmem]
        exact hlc c hc0 hc1 x y
      · rw [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hc1', mul_zero]
        exact zero_le _
    · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hc0, zero_mul]
      exact zero_le _

lemma part1 {n : ℕ} : ∀ (u : EuclideanSpace ℝ (Fin n) → EReal),
    InConvRn u →
    Measurable (fun x => ENNReal.ofReal (expNegWT (u x))) →
    let P := Measure.withDensity volume (fun x => ENNReal.ofReal (expNegWT (u x)))
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P := by
  intro u hu hmeas P _hP
  exact logconcave_of_density _ hmeas
    (fun c hc0 hc1 x y => expNegWT_logconcave u hu hc0 hc1 x y)


/-- Geometric inclusion for convex combinations of closed balls. -/
lemma p2m_subset {n : ℕ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (x y : EuclideanSpace ℝ (Fin n))
    {ε : ℝ} :
    c • Metric.closedBall x ε + (1 - c) • Metric.closedBall y ε ⊆
      Metric.closedBall (c • x + (1 - c) • y) ε := by
  intro w hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hw
  obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.mp hu
  obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.mp hv
  rw [Metric.mem_closedBall] at ha hb ⊢
  have h1c : 0 ≤ 1 - c := by linarith
  calc dist (c • a + (1 - c) • b) (c • x + (1 - c) • y)
      ≤ dist (c • a) (c • x) + dist ((1 - c) • b) ((1 - c) • y) := dist_add_add_le _ _ _ _
    _ = c * dist a x + (1 - c) * dist b y := by
        rw [dist_smul₀, dist_smul₀, Real.norm_of_nonneg hc0.le, Real.norm_of_nonneg h1c]
    _ ≤ c * ε + (1 - c) * ε := by gcongr
    _ = ε := by ring

/-- Core inequality for a fixed `δ`. -/
lemma p2m_core {n : ℕ} (P : Measure (EuclideanSpace ℝ (Fin n)))
    (p : EuclideanSpace ℝ (Fin n) → ℝ)
    (hlc : IsLogConcaveMeasure P) (hp : Continuous p) (hp0 : ∀ x, 0 ≤ p x)
    (hP : P = Measure.withDensity volume (fun x => ENNReal.ofReal (p x)))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (x y : EuclideanSpace ℝ (Fin n))
    {δ : ℝ} (hδ : 0 < δ) (hδx : δ < p x) (hδy : δ < p y) :
    (p x - δ) ^ c * (p y - δ) ^ (1 - c) ≤ p (c • x + (1 - c) • y) + δ := by
  set z := c • x + (1 - c) • y with hz
  have h1c : 0 < 1 - c := by linarith
  have ex : ∀ᶠ w in 𝓝 x, p x - δ < p w := (hp.tendsto x).eventually (lt_mem_nhds (by linarith))
  have ey : ∀ᶠ w in 𝓝 y, p y - δ < p w := (hp.tendsto y).eventually (lt_mem_nhds (by linarith))
  have ez : ∀ᶠ w in 𝓝 z, p w < p z + δ := (hp.tendsto z).eventually (gt_mem_nhds (by linarith))
  obtain ⟨εx, hεx, hx'⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp ex
  obtain ⟨εy, hεy, hy'⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp ey
  obtain ⟨εz, hεz, hz'⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp ez
  set ε := min εx (min εy εz) with hε
  have hε0 : 0 < ε := lt_min hεx (lt_min hεy hεz)
  have hεx' : ε ≤ εx := min_le_left _ _
  have hεy' : ε ≤ εy := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεz' : ε ≤ εz := le_trans (min_le_right _ _) (min_le_right _ _)
  set V := volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε) with hV
  have hVc : ∀ w : EuclideanSpace ℝ (Fin n), volume (Metric.closedBall w ε) = V := fun w =>
    Measure.addHaar_closedBall_center volume w ε
  have hV0 : V ≠ 0 := (Metric.measure_closedBall_pos volume _ hε0).ne'
  have hVt : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hmeas : Measurable (fun w => ENNReal.ofReal (p w)) := hp.measurable.ennreal_ofReal
  have hPball : ∀ w, P (Metric.closedBall w ε) =
      ∫⁻ u in Metric.closedBall w ε, ENNReal.ofReal (p u) := by
    intro w
    rw [hP, withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  have hLx : ENNReal.ofReal (p x - δ) * V ≤ P (Metric.closedBall x ε) := by
    rw [hPball, ← hVc x, ← setLIntegral_const]
    apply setLIntegral_mono hmeas
    intro w hw
    exact ENNReal.ofReal_le_ofReal (hx' (Metric.closedBall_subset_closedBall hεx' hw)).le
  have hLy : ENNReal.ofReal (p y - δ) * V ≤ P (Metric.closedBall y ε) := by
    rw [hPball, ← hVc y, ← setLIntegral_const]
    apply setLIntegral_mono hmeas
    intro w hw
    exact ENNReal.ofReal_le_ofReal (hy' (Metric.closedBall_subset_closedBall hεy' hw)).le
  have hUz : P (Metric.closedBall z ε) ≤ ENNReal.ofReal (p z + δ) * V := by
    rw [hPball, ← hVc z, ← setLIntegral_const]
    apply setLIntegral_mono measurable_const
    intro w hw
    exact ENNReal.ofReal_le_ofReal (hz' (Metric.closedBall_subset_closedBall hεz' hw)).le
  have hLC := hlc (Metric.closedBall x ε) (Metric.closedBall y ε) c (isCompact_closedBall x ε)
    (isCompact_closedBall y ε) hc0 hc1
  simp only [ENNReal.rpow_eq_pow, ge_iff_le] at hLC
  have hmono : P (c • Metric.closedBall x ε + (1 - c) • Metric.closedBall y ε) ≤
      P (Metric.closedBall z ε) := measure_mono (p2m_subset hc0 hc1 x y)
  have hpxd : 0 ≤ p x - δ := by linarith
  have hpyd : 0 ≤ p y - δ := by linarith
  have hVV : V ^ c * V ^ (1 - c) = V := by
    rw [← ENNReal.rpow_add _ _ hV0 hVt]; simp
  have key : ENNReal.ofReal ((p x - δ) ^ c * (p y - δ) ^ (1 - c)) * V ≤
      ENNReal.ofReal (p z + δ) * V := by
    calc ENNReal.ofReal ((p x - δ) ^ c * (p y - δ) ^ (1 - c)) * V
        = (ENNReal.ofReal (p x - δ) * V) ^ c * (ENNReal.ofReal (p y - δ) * V) ^ (1 - c) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hc0.le, ENNReal.mul_rpow_of_nonneg _ _ h1c.le,
            ENNReal.ofReal_mul (Real.rpow_nonneg hpxd _),
            ← ENNReal.ofReal_rpow_of_nonneg hpxd hc0.le,
            ← ENNReal.ofReal_rpow_of_nonneg hpyd h1c.le, mul_mul_mul_comm, hVV]
      _ ≤ P (Metric.closedBall x ε) ^ c * P (Metric.closedBall y ε) ^ (1 - c) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hLx hc0.le) (ENNReal.rpow_le_rpow hLy h1c.le)
      _ ≤ P (c • Metric.closedBall x ε + (1 - c) • Metric.closedBall y ε) := hLC
      _ ≤ P (Metric.closedBall z ε) := hmono
      _ ≤ ENNReal.ofReal (p z + δ) * V := hUz
  have key2 := (ENNReal.mul_le_mul_iff_left hV0 hVt).mp key
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith [hp0 z])).mp key2

/-- Pointwise log-concavity of a continuous density of a log-concave measure. -/
lemma part2_mult {n : ℕ} (P : Measure (EuclideanSpace ℝ (Fin n)))
    (p : EuclideanSpace ℝ (Fin n) → ℝ)
    (hlc : IsLogConcaveMeasure P) (hp : Continuous p) (hp0 : ∀ x, 0 ≤ p x)
    (hP : P = Measure.withDensity volume (fun x => ENNReal.ofReal (p x)))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (x y : EuclideanSpace ℝ (Fin n)) :
    p x ^ c * p y ^ (1 - c) ≤ p (c • x + (1 - c) • y) := by
  have h1c : 0 < 1 - c := by linarith
  rcases (hp0 x).lt_or_eq with hpx | hpx
  · rcases (hp0 y).lt_or_eq with hpy | hpy
    · have key : ∀ δ : ℝ, δ ∈ Set.Ioo 0 (min (p x) (p y)) →
          (p x - δ) ^ c * (p y - δ) ^ (1 - c) ≤ p (c • x + (1 - c) • y) + δ := by
        intro δ hδ
        exact p2m_core P p hlc hp hp0 hP hc0 hc1 x y hδ.1
          (lt_of_lt_of_le hδ.2 (min_le_left _ _)) (lt_of_lt_of_le hδ.2 (min_le_right _ _))
      have h1 : Filter.Tendsto (fun δ : ℝ => (p x - δ) ^ c * (p y - δ) ^ (1 - c)) (𝓝[>] 0)
          (𝓝 (p x ^ c * p y ^ (1 - c))) := by
        have hc : ContinuousAt (fun δ : ℝ => (p x - δ) ^ c * (p y - δ) ^ (1 - c)) 0 := by
          apply ContinuousAt.mul
          · exact (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr hc0.le)
          · exact (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr h1c.le)
        have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa using this
      have h2 : Filter.Tendsto (fun δ : ℝ => p (c • x + (1 - c) • y) + δ) (𝓝[>] 0)
          (𝓝 (p (c • x + (1 - c) • y))) := by
        have : Filter.Tendsto (fun δ : ℝ => p (c • x + (1 - c) • y) + δ) (𝓝 0)
            (𝓝 (p (c • x + (1 - c) • y) + 0)) := tendsto_const_nhds.add Filter.tendsto_id
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto_of_tendsto h1 h2
        (Filter.eventually_of_mem (Ioo_mem_nhdsGT (lt_min hpx hpy)) key)
    · rw [← hpy, Real.zero_rpow h1c.ne', mul_zero]; exact hp0 _
  · rw [← hpx, Real.zero_rpow hc0.ne', zero_mul]; exact hp0 _

/-- Auxiliary: the EReal value `-log q` (or `⊤` if `q = 0`) is below `s` iff `exp (-s) ≤ q`. -/
lemma p2c_le_iff (q s : ℝ) (hq : 0 ≤ q) :
    (if q = 0 then (⊤ : EReal) else ((-Real.log q : ℝ) : EReal)) ≤ (s : EReal) ↔
      Real.exp (-s) ≤ q := by
  split_ifs with h
  · constructor
    · intro h1
      exact absurd (top_le_iff.mp h1) (EReal.coe_ne_top s)
    · intro h1
      rw [h] at h1
      exact absurd h1 (not_le.mpr (Real.exp_pos _))
  · have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm h)
    rw [EReal.coe_le_coe_iff]
    constructor
    · intro h1
      calc Real.exp (-s) ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr (by linarith)
        _ = q := Real.exp_log hq'
    · intro h1
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rw [Real.log_exp] at h2
      linarith

/-- Auxiliary: multiplicative log-concavity transfers lower bounds `exp (-s)`. -/
lemma p2c_conv_aux {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (p : F → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hmult : ∀ c : ℝ, 0 < c → c < 1 → ∀ x y, p x ^ c * p y ^ (1 - c) ≤ p (c • x + (1 - c) • y))
    {a b s t : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (x y : F)
    (hx : Real.exp (-s) ≤ p x) (hy : Real.exp (-t) ≤ p y) :
    Real.exp (-(a * s + b * t)) ≤ p (a • x + b • y) := by
  have ha1 : a < 1 := by linarith
  have hb' : b = 1 - a := by linarith
  subst hb'
  calc Real.exp (-(a * s + (1 - a) * t)) = Real.exp (-s) ^ a * Real.exp (-t) ^ (1 - a) := by
        rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]; ring_nf
    _ ≤ p x ^ a * p y ^ (1 - a) := by
        apply mul_le_mul (Real.rpow_le_rpow (Real.exp_pos _).le hx ha.le)
          (Real.rpow_le_rpow (Real.exp_pos _).le hy hb.le)
          (Real.rpow_nonneg (Real.exp_pos _).le _) (Real.rpow_nonneg (hp0 x) _)
    _ ≤ p (a • x + (1 - a) • y) := hmult a ha ha1 x y

/-- A nonnegative, not identically zero, multiplicatively log-concave function is `exp(-u)`
for a proper convex `u`. -/
lemma part2_construct {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (p : F → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hpos : ∃ x, 0 < p x)
    (hmult : ∀ c : ℝ, 0 < c → c < 1 → ∀ x y, p x ^ c * p y ^ (1 - c) ≤ p (c • x + (1 - c) • y)) :
    ∃ u : F → EReal, InConvRn u ∧ ∀ x, p x = expNegWT (u x) := by
  classical
  refine ⟨fun x => if p x = 0 then (⊤ : EReal) else ((-Real.log (p x) : ℝ) : EReal),
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x
    dsimp only
    split_ifs
    · exact bot_lt_top
    · exact EReal.bot_lt_coe _
  · obtain ⟨x, hx⟩ := hpos
    refine ⟨x, ?_⟩
    dsimp only
    rw [if_neg hx.ne']
    exact EReal.coe_lt_top _
  · unfold ConvexEReal
    rintro ⟨x, s⟩ hz ⟨y, t⟩ hw a b ha hb hab
    simp only [epigraph, Set.mem_setOf_eq] at hz hw ⊢
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rcases ha.eq_or_lt with ha0 | hapos
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hw
    rcases hb.eq_or_lt with hb0 | hbpos
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      simpa using hz
    rw [p2c_le_iff _ _ (hp0 x)] at hz
    rw [p2c_le_iff _ _ (hp0 y)] at hw
    rw [p2c_le_iff _ _ (hp0 _)]
    exact p2c_conv_aux p hp0 hmult hapos hbpos hab x y hz hw
  · intro x
    dsimp only
    split_ifs with h
    · simp [expNegWT, h]
    · have hpx : 0 < p x := lt_of_le_of_ne (hp0 x) (Ne.symm h)
      simp [expNegWT, Real.exp_log hpx]

lemma part2 {n : ℕ} : ∀ (P : Measure (EuclideanSpace ℝ (Fin n)))
      (p : EuclideanSpace ℝ (Fin n) → ℝ),
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P →
    Continuous p →
    (∀ x, 0 ≤ p x) →
    P = Measure.withDensity volume (fun x => ENNReal.ofReal (p x)) →
    ∃ (u : EuclideanSpace ℝ (Fin n) → EReal),
      InConvRn u ∧ ∀ x, p x = expNegWT (u x) := by
  intro P p hprob hlc hp hp0 hP
  have hpos : ∃ x, 0 < p x := by
    by_contra hcon
    push_neg at hcon
    have hzero : (fun x => ENNReal.ofReal (p x)) = fun _ => 0 := by
      funext x
      have : p x = 0 := le_antisymm (hcon x) (hp0 x)
      simp [this]
    have hP0 : P = 0 := by
      rw [hP, hzero]
      exact withDensity_zero
    have h1 : P Set.univ = 1 := measure_univ
    rw [hP0] at h1
    simp at h1
  exact part2_construct p hp0 hpos (fun c hc0 hc1 x y => part2_mult P p hlc hp hp0 hP hc0 hc1 x y)


lemma p3i_rpow_iSup_isCompact {n : ℕ} (P : Measure (EuclideanSpace ℝ (Fin n)))
    [IsFiniteMeasure P] {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    {c : ℝ} (hc0 : 0 < c) :
    P S ^ c = ⨆ (K : Set (EuclideanSpace ℝ (Fin n))) (_ : K ⊆ S) (_ : IsCompact K), P K ^ c := by
  rw [hS.measure_eq_iSup_isCompact]
  simp only [← ENNReal.orderIsoRpow_apply c hc0, OrderIso.map_iSup]

/-- Log-concavity extended from compact sets to measurable sets (inner regularity). -/
lemma part3_ineq {n : ℕ} (P : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure P]
    (hlc : IsLogConcaveMeasure P) {S T U : Set (EuclideanSpace ℝ (Fin n))}
    (hS : MeasurableSet S) (hT : MeasurableSet T) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hU : c • S + (1 - c) • T ⊆ U) :
    P S ^ c * P T ^ (1 - c) ≤ P U := by
  have key : ∀ K, K ⊆ S → IsCompact K → ∀ L, L ⊆ T → IsCompact L →
      P K ^ c * P L ^ (1 - c) ≤ P U := by
    intro K hKS hK L hLT hL
    have h1 := hlc K L c hK hL hc0 hc1
    have h2 : c • K + (1 - c) • L ⊆ U :=
      (Set.add_subset_add (Set.smul_set_mono hKS) (Set.smul_set_mono hLT)).trans hU
    exact le_trans h1 (measure_mono h2)
  rw [p3i_rpow_iSup_isCompact P hS hc0, p3i_rpow_iSup_isCompact P hT (sub_pos.2 hc1)]
  simp only [ENNReal.iSup_mul, ENNReal.mul_iSup, iSup_le_iff]
  intro L hLT hL K hKS hK
  exact key K hKS hK L hLT hL

lemma p3_zero_mem {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ A)
    (hsymm : ∀ x, x ∈ A ↔ -x ∈ A) (hne : A.Nonempty) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ A := by
  obtain ⟨a, ha⟩ := hne
  have hna : -a ∈ A := (hsymm a).1 ha
  have h := hconv ha hna (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  simpa [smul_neg] using h

lemma p3_subset {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ A)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ A) {r : ℝ} (hr : 1 ≤ r) :
    A ⊆ r • A := by
  intro x hx
  have hr0 : r ≠ 0 := by positivity
  have hmem : r⁻¹ • x ∈ A := by
    apply hconv.smul_mem_of_zero_mem h0 hx
    constructor
    · positivity
    · exact inv_le_one_of_one_le₀ hr
  refine ⟨r⁻¹ • x, hmem, ?_⟩
  simp [smul_smul, mul_inv_cancel₀ hr0]

lemma p3_incl {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ A)
    (hsymm : ∀ x, x ∈ A ↔ -x ∈ A) {r : ℝ} (hr : 1 < r) :
    (2 / (r + 1)) • (r • A)ᶜ + (1 - 2 / (r + 1)) • A ⊆ Aᶜ := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩ hy
  apply hx
  have hna : -a ∈ A := (hsymm a).1 ha
  have hr0 : r ≠ 0 := by positivity
  have hr1 : r + 1 ≠ 0 := by positivity
  have hmem := hconv hy hna (a := (r + 1) / (2 * r)) (b := (r - 1) / (2 * r))
    (by positivity) (div_nonneg (by linarith) (by positivity)) (by field_simp; ring)
  have e1 : (r + 1) / (2 * r) * (2 / (r + 1)) = r⁻¹ := by field_simp
  have e2 : (r + 1) / (2 * r) * (1 - 2 / (r + 1)) = (r - 1) / (2 * r) := by field_simp; ring
  have key : r⁻¹ • x = ((r + 1) / (2 * r)) • ((2 / (r + 1)) • x + (1 - 2 / (r + 1)) • a) +
      ((r - 1) / (2 * r)) • (-a) := by
    simp only [smul_add, smul_smul, smul_neg, e1, e2]
    abel
  rw [← key] at hmem
  refine ⟨r⁻¹ • x, hmem, ?_⟩
  simp [smul_smul, mul_inv_cancel₀ hr0]

lemma p3_alg (θ Q r : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hQ : 0 < Q)
    (h : 2 * Real.log Q + (r - 1) * Real.log θ ≤ (r + 1) * Real.log (1 - θ)) :
    Q ≤ Real.rpow ((1 - θ) / θ) (r / 2) * Real.sqrt (θ * (1 - θ)) := by
  rw [Real.rpow_eq_pow]
  have h1θ : 0 < 1 - θ := by linarith
  have hA : 0 < ((1 - θ) / θ) ^ (r / 2) := Real.rpow_pos_of_pos (div_pos h1θ hθ0) _
  have hB : 0 < Real.sqrt (θ * (1 - θ)) := Real.sqrt_pos.2 (_root_.mul_pos hθ0 h1θ)
  rw [← Real.log_le_log_iff hQ (_root_.mul_pos hA hB)]
  rw [Real.log_mul hA.ne' hB.ne', Real.log_rpow (div_pos h1θ hθ0), Real.log_div h1θ.ne' hθ0.ne',
    Real.log_sqrt (_root_.mul_pos hθ0 h1θ).le, Real.log_mul hθ0.ne' h1θ.ne']
  linarith

lemma part3 {n : ℕ} : ∀ (P : Measure (EuclideanSpace ℝ (Fin n)))
      (A : Set (EuclideanSpace ℝ (Fin n)))
      (r : ℝ),
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P →
    Convex ℝ A →
    (∀ x, x ∈ A ↔ -x ∈ A) →
    MeasurableSet A →
    P A ≠ 0 →
    r ≥ 1 →
    1 - (P (r • A)).toReal ≤
      Real.rpow ((1 - (P A).toReal) / (P A).toReal) (r / 2) *
        Real.sqrt ((P A).toReal * (1 - (P A).toReal)) := by
  intro P A r hP hlc hconv hsymm hA hPA hr
  have hne : A.Nonempty := nonempty_of_measure_ne_zero hPA
  have h0 := p3_zero_mem hconv hsymm hne
  have hsub : A ⊆ r • A := p3_subset hconv h0 hr
  have hr0 : r ≠ 0 := (by linarith : (0:ℝ) < r).ne'
  have hrA : MeasurableSet (r • A) := hA.const_smul_of_ne_zero hr0
  have hθ0 : 0 < (P A).toReal := ENNReal.toReal_pos hPA (measure_ne_top P A)
  have hθ1 : (P A).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P) (s := A))
  have hcompl : (P (r • A)ᶜ).toReal = 1 - (P (r • A)).toReal := by
    rw [prob_compl_eq_one_sub hrA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have hcomplA : (P Aᶜ).toReal = 1 - (P A).toReal := by
    rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have hQ0 : 0 ≤ 1 - (P (r • A)).toReal := by rw [← hcompl]; exact ENNReal.toReal_nonneg
  have hQle : 1 - (P (r • A)).toReal ≤ 1 - (P A).toReal := by
    have : (P A).toReal ≤ (P (r • A)).toReal :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
    linarith
  have hRnonneg : 0 ≤ Real.rpow ((1 - (P A).toReal) / (P A).toReal) (r / 2) *
      Real.sqrt ((P A).toReal * (1 - (P A).toReal)) := by
    apply mul_nonneg
    · rw [Real.rpow_eq_pow]; exact Real.rpow_nonneg (div_nonneg (by linarith) hθ0.le) _
    · exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hθ1 with hθe | hθlt
  · linarith
  rcases eq_or_lt_of_le hQ0 with hQe | hQpos
  · rw [← hQe]; exact hRnonneg
  apply p3_alg _ _ _ hθ0 hθlt hQpos
  have h1θ : 0 < 1 - (P A).toReal := by linarith
  rcases eq_or_lt_of_le hr with hr1 | hr1
  · have := Real.log_le_log hQpos hQle
    rw [show r - 1 = 0 by linarith, show r + 1 = 2 by linarith]
    linarith
  · have hc0 : 0 < 2 / (r + 1) := by positivity
    have hc1 : 2 / (r + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have key := part3_ineq P hlc hrA.compl hA hc0 hc1 (p3_incl hconv hsymm hr1)
    have key' := ENNReal.toReal_mono (measure_ne_top P _) key
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, hcompl,
      hcomplA] at key'
    have hl := Real.log_le_log (_root_.mul_pos (Real.rpow_pos_of_pos hQpos _)
      (Real.rpow_pos_of_pos hθ0 _)) key'
    rw [Real.log_mul (Real.rpow_pos_of_pos hQpos _).ne' (Real.rpow_pos_of_pos hθ0 _).ne',
      Real.log_rpow hQpos, Real.log_rpow hθ0] at hl
    have hcr : 2 / (r + 1) * (r + 1) = 2 := by field_simp
    have hm := mul_le_mul_of_nonneg_left hl (by linarith : (0:ℝ) ≤ r + 1)
    have e : (r + 1) * (2 / (r + 1) * Real.log (1 - (P (r • A)).toReal) +
        (1 - 2 / (r + 1)) * Real.log (P A).toReal) =
        2 * Real.log (1 - (P (r • A)).toReal) + (r - 1) * Real.log (P A).toReal := by
      linear_combination (Real.log (1 - (P (r • A)).toReal) - Real.log (P A).toReal) * hcr
    linarith

end DuchiPL

theorem Duchi_Q9_1
  {n : ℕ} :
  (∀ (u : EuclideanSpace ℝ (Fin n) → EReal),
    InConvRn u →
    Measurable (fun x => ENNReal.ofReal (expNegWT (u x))) →
    let P := Measure.withDensity volume (fun x => ENNReal.ofReal (expNegWT (u x)))
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P) ∧
  (∀ (P : Measure (EuclideanSpace ℝ (Fin n)))
      (p : EuclideanSpace ℝ (Fin n) → ℝ),
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P →
    Continuous p →
    (∀ x, 0 ≤ p x) →
    P = Measure.withDensity volume (fun x => ENNReal.ofReal (p x)) →
    ∃ (u : EuclideanSpace ℝ (Fin n) → EReal),
      InConvRn u ∧ ∀ x, p x = expNegWT (u x)) ∧
  (∀ (P : Measure (EuclideanSpace ℝ (Fin n)))
      (A : Set (EuclideanSpace ℝ (Fin n)))
      (r : ℝ),
    IsProbabilityMeasure P →
    IsLogConcaveMeasure P →
    Convex ℝ A →
    (∀ x, x ∈ A ↔ -x ∈ A) →
    MeasurableSet A →
    P A ≠ 0 →
    r ≥ 1 →
    1 - (P (r • A)).toReal ≤
      Real.rpow ((1 - (P A).toReal) / (P A).toReal) (r / 2) *
        Real.sqrt ((P A).toReal * (1 - (P A).toReal))) := by
  exact ⟨DuchiPL.part1, DuchiPL.part2, DuchiPL.part3⟩

end Duchi_Q9_1
