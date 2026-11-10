import ConvexStarLib.Defs

/-!
# `RW_chap_8_24`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_24` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_24`, so the main result is `RW_chap_8_24.RW_chap_8_24`.
-/

namespace RW_chap_8_24

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma sep_E {S : Set E} (hc : Convex ℝ S) (hcl : IsClosed S) {v : E} (hv : v ∉ S) :
    ∃ u : E, ∃ c : ℝ, (∀ a ∈ S, inner ℝ a u < c) ∧ c < inner ℝ v u := by
  obtain ⟨f, c, hf, hc⟩ := geometric_hahn_banach_closed_point hc hcl hv
  refine ⟨(InnerProductSpace.toDual ℝ E).symm f, c, ?_, ?_⟩
  · intro a ha
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    exact hf a ha
  · rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    exact hc

lemma sep_prod {C : Set (E × ℝ)} (hc : Convex ℝ C) (hcl : IsClosed C) {p : E × ℝ} (hp : p ∉ C) :
    ∃ u : E, ∃ α c : ℝ, (∀ q ∈ C, inner ℝ q.1 u + α * q.2 < c) ∧
      c < inner ℝ p.1 u + α * p.2 := by
  obtain ⟨f, c, hf, hc⟩ := geometric_hahn_banach_closed_point hc hcl hp
  set fE : StrongDual ℝ E := f.comp (ContinuousLinearMap.inl ℝ E ℝ) with hfE
  have key : ∀ q : E × ℝ, f q =
      inner ℝ q.1 ((InnerProductSpace.toDual ℝ E).symm fE) + f (0, 1) * q.2 := by
    intro q
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have : q = (q.1, 0) + q.2 • ((0:E), (1:ℝ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul]
    simp [fE, smul_eq_mul, mul_comm]
  refine ⟨(InnerProductSpace.toDual ℝ E).symm fE, f (0, 1), c, ?_, ?_⟩
  · intro q hq; rw [← key]; exact hf q hq
  · rw [← key]; exact hc

lemma ereal_mul_sSup {t : ℝ} (ht : 0 < t) (S : Set EReal) :
    sSup ((fun a => (t:EReal) * a) '' S) = (t:EReal) * sSup S := by
  have ht' : (0:EReal) ≤ (t:EReal) := by exact_mod_cast ht.le
  have hti : (0:EReal) ≤ ((t⁻¹:ℝ):EReal) := by exact_mod_cast (inv_pos.mpr ht).le
  have h1 : ∀ a : EReal, ((t⁻¹:ℝ):EReal) * ((t:EReal) * a) = a := by
    intro a
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ht.ne', EReal.coe_one, one_mul]
  have h2 : ∀ a : EReal, (t:EReal) * (((t⁻¹:ℝ):EReal) * a) = a := by
    intro a
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht.ne', EReal.coe_one, one_mul]
  apply le_antisymm
  · apply sSup_le
    rintro b ⟨a, ha, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_sSup ha) ht'
  · have : sSup S ≤ ((t⁻¹:ℝ):EReal) * sSup ((fun a => (t:EReal) * a) '' S) := by
      apply sSup_le
      intro a ha
      calc a = ((t⁻¹:ℝ):EReal) * ((t:EReal) * a) := (h1 a).symm
        _ ≤ ((t⁻¹:ℝ):EReal) * sSup ((fun a => (t:EReal) * a) '' S) :=
          mul_le_mul_of_nonneg_left (le_sSup ⟨a, ha, rfl⟩) hti
    calc (t:EReal) * sSup S
        ≤ (t:EReal) * (((t⁻¹:ℝ):EReal) * sSup ((fun a => (t:EReal) * a) '' S)) :=
          mul_le_mul_of_nonneg_left this ht'
      _ = _ := h2 _

lemma supportFunction_le_iff (D : Set E) (w : E) (r : EReal) :
    supportFunction D w ≤ r ↔ ∀ v ∈ D, ((inner ℝ v w : ℝ) : EReal) ≤ r := by
  unfold supportFunction
  rw [sSup_le_iff]
  constructor
  · intro h v hv; exact h _ ⟨v, hv, rfl⟩
  · rintro h _ ⟨v, hv, rfl⟩; exact h v hv

lemma le_supportFunction (D : Set E) (w : E) {v : E} (hv : v ∈ D) :
    ((inner ℝ v w : ℝ) : EReal) ≤ supportFunction D w :=
  le_sSup ⟨v, hv, rfl⟩

lemma supportFunction_zero_le (D : Set E) : supportFunction D 0 ≤ 0 := by
  rw [supportFunction_le_iff]
  intro v _; simp

lemma supportFunction_sublinear (D : Set E) : IsSublinearRW (supportFunction D) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show supportFunction D 0 < ⊤
    exact lt_of_le_of_lt (supportFunction_zero_le D) EReal.zero_lt_top
  · intro x t ht
    unfold supportFunction
    rw [← ereal_mul_sSup ht, Set.image_image]
    congr 1
    apply Set.image_congr
    intro v _
    rw [real_inner_smul_right, EReal.coe_mul]
  · intro p hp q hq a b ha hb hab
    show supportFunction D (a • p + b • q).1 ≤ ((a • p + b • q).2 : EReal)
    rw [supportFunction_le_iff]
    intro v hv
    have h1 : inner ℝ v p.1 ≤ p.2 := by
      have := (supportFunction_le_iff D p.1 _).mp hp v hv
      exact_mod_cast this
    have h2 : inner ℝ v q.1 ≤ q.2 := by
      have := (supportFunction_le_iff D q.1 _).mp hq v hv
      exact_mod_cast this
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have : a * inner ℝ v p.1 + b * inner ℝ v q.1 ≤ a * p.2 + b * q.2 := by nlinarith
    exact_mod_cast this

lemma supportFunction_lsc (D : Set E) : LowerSemicontinuous (supportFunction D) := by
  have : supportFunction D = fun w => ⨆ v ∈ D, ((inner ℝ v w : ℝ) : EReal) := by
    funext w; unfold supportFunction; rw [sSup_image]
  rw [this]
  apply lowerSemicontinuous_biSup
  intro v _
  apply Continuous.lowerSemicontinuous
  exact continuous_coe_real_ereal.comp (continuous_const.inner continuous_id)

lemma supportFunction_proper (D : Set E) (hD : D.Nonempty) : IsProper (supportFunction D) := by
  obtain ⟨v, hv⟩ := hD
  refine ⟨fun x => lt_of_lt_of_le (EReal.bot_lt_coe _) (le_supportFunction D x hv), ⟨0, ?_⟩⟩
  exact lt_of_le_of_lt (supportFunction_zero_le D) EReal.zero_lt_top

lemma supportSublevelSet_closed (h : E → EReal) : IsClosed (supportSublevelSet h) := by
  have : supportSublevelSet h = ⋂ w, {v : E | ((inner ℝ v w : ℝ) : EReal) ≤ h w} := by
    ext v; simp [supportSublevelSet]
  rw [this]
  apply isClosed_iInter
  intro w
  exact isClosed_le (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const))
    continuous_const

lemma supportSublevelSet_convex (h : E → EReal) : Convex ℝ (supportSublevelSet h) := by
  intro x hx y hy a b ha hb hab w
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hxw := hx w
  have hyw := hy w
  generalize h w = c at hxw hyw ⊢
  induction c using EReal.rec with
  | bot => exact absurd hxw (not_le.mpr (EReal.bot_lt_coe _))
  | top => exact le_top
  | coe r =>
    have h1 : inner ℝ x w ≤ r := by exact_mod_cast hxw
    have h2 : inner ℝ y w ≤ r := by exact_mod_cast hyw
    have e : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
    have : a * inner ℝ x w + b * inner ℝ y w ≤ r := by
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    exact_mod_cast this

lemma closure_convexHull_eq (D : Set E) :
    closure (convexHull ℝ D) = supportSublevelSet (supportFunction D) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (supportSublevelSet_closed _)
    apply convexHull_min _ (supportSublevelSet_convex _)
    intro v hv w
    exact le_supportFunction D w hv
  · intro v hv
    by_contra hcon
    obtain ⟨u, c, hS, hc⟩ := sep_E (convex_convexHull ℝ D).closure isClosed_closure hcon
    have h1 : supportFunction D u ≤ (c : EReal) := by
      rw [supportFunction_le_iff]
      intro a ha
      exact_mod_cast (hS a (subset_closure (subset_convexHull ℝ D ha))).le
    have h2 := hv u
    have : ((inner ℝ v u : ℝ) : EReal) ≤ (c : EReal) := h2.trans h1
    have : inner ℝ v u ≤ c := by exact_mod_cast this
    linarith

lemma posHom_zero_le {h : E → EReal} (h0 : 0 ∈ effDom h) (hh : IsERealPosHomogeneous h) :
    h 0 ≤ 0 := by
  have h2 := hh 0 2 (by norm_num)
  rw [smul_zero] at h2
  have h0' : h 0 < ⊤ := h0
  generalize h 0 = c at h2 h0' ⊢
  induction c using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd h0' (lt_irrefl _)
  | coe r =>
    have : r = 2 * r := by exact_mod_cast h2
    have : r = 0 := by linarith
    simp [this]

lemma epi_cone {h : E → EReal} (hh : IsERealPosHomogeneous h) {x : E} {r t : ℝ}
    (hxr : (x, r) ∈ epigraph h) (ht : 0 < t) : (t • x, t * r) ∈ epigraph h := by
  show h (t • x) ≤ ((t * r : ℝ) : EReal)
  rw [hh x t ht, EReal.coe_mul]
  exact mul_le_mul_of_nonneg_left (show h x ≤ (r : EReal) from hxr) (by exact_mod_cast ht.le)

lemma sep_epi {h : E → EReal} (h0 : 0 ∈ effDom h) (hh : IsERealPosHomogeneous h)
    {p : E × ℝ} (hp : p ∉ closure (convexHull ℝ (epigraph h))) :
    ∃ u : E, ∃ α c : ℝ, α ≤ 0 ∧ 0 < c ∧
      (∀ q ∈ closure (convexHull ℝ (epigraph h)), inner ℝ q.1 u + α * q.2 < c) ∧
      (∀ q ∈ epigraph h, inner ℝ q.1 u + α * q.2 ≤ 0) ∧
      c < inner ℝ p.1 u + α * p.2 := by
  obtain ⟨u, α, c, hC, hp'⟩ := sep_prod (convex_convexHull ℝ _).closure isClosed_closure hp
  have hsub : epigraph h ⊆ closure (convexHull ℝ (epigraph h)) :=
    (subset_convexHull ℝ _).trans subset_closure
  have hz : ∀ r : ℝ, 0 ≤ r → ((0:E), r) ∈ epigraph h := by
    intro r hr
    show h 0 ≤ (r : EReal)
    exact (posHom_zero_le h0 hh).trans (by exact_mod_cast hr)
  have hc : 0 < c := by
    have := hC _ (hsub (hz 0 le_rfl))
    simpa using this
  have hepi : ∀ q ∈ epigraph h, inner ℝ q.1 u + α * q.2 ≤ 0 := by
    intro q hq
    by_contra hneg
    push_neg at hneg
    have hne := hneg.ne'
    have ht : 0 < (c + 1) / (inner ℝ q.1 u + α * q.2) := div_pos (by linarith) hneg
    have hmem := epi_cone hh (x := q.1) (r := q.2) hq ht
    have := hC _ (hsub hmem)
    simp only at this
    rw [real_inner_smul_left] at this
    have e : (c + 1) / (inner ℝ q.1 u + α * q.2) * inner ℝ q.1 u +
        α * ((c + 1) / (inner ℝ q.1 u + α * q.2) * q.2) = c + 1 := by
      field_simp
    linarith
  have hα : α ≤ 0 := by
    have := hepi _ (hz 1 zero_le_one)
    simpa using this
  exact ⟨u, α, c, hα, hc, hC, hepi, hp'⟩

lemma mem_sublevel_of_sep {h : E → EReal} {u : E} {α : ℝ} (hα : α < 0)
    (hepi : ∀ q ∈ epigraph h, inner ℝ q.1 u + α * q.2 ≤ 0) :
    (-α)⁻¹ • u ∈ supportSublevelSet h := by
  intro w
  rw [real_inner_smul_left, real_inner_comm w u]
  have key : ∀ r : ℝ, h w ≤ r → inner ℝ w u + α * r ≤ 0 := fun r hr => hepi (w, r) hr
  generalize h w = c at key ⊢
  induction c using EReal.rec with
  | bot =>
    exfalso
    have := key ((1 - inner ℝ w u) / α) bot_le
    have hα0 : α ≠ 0 := hα.ne
    have e : α * ((1 - inner ℝ w u) / α) = 1 - inner ℝ w u := by
      field_simp
    linarith
  | top => exact le_top
  | coe r =>
    have := key r le_rfl
    have : (-α)⁻¹ * inner ℝ w u ≤ r := by
      rw [inv_mul_le_iff₀ (by linarith)]
      linarith
    exact_mod_cast this

lemma mem_sublevel_add {h : E → EReal} {u v0 : E} {t : ℝ} (ht : 0 ≤ t)
    (hv0 : v0 ∈ supportSublevelSet h)
    (hepi : ∀ q ∈ epigraph h, inner ℝ q.1 u ≤ 0) :
    v0 + t • u ∈ supportSublevelSet h := by
  intro w
  rw [inner_add_left, real_inner_smul_left, real_inner_comm w u]
  have hv0w := hv0 w
  have key : ∀ r : ℝ, h w ≤ r → inner ℝ w u ≤ 0 := fun r hr => hepi (w, r) hr
  generalize h w = c at key hv0w ⊢
  induction c using EReal.rec with
  | bot => exact absurd hv0w (not_le.mpr (EReal.bot_lt_coe _))
  | top => exact le_top
  | coe r =>
    have h1 := key r le_rfl
    have h2 : inner ℝ v0 w ≤ r := by exact_mod_cast hv0w
    have : inner ℝ v0 w + t * inner ℝ w u ≤ r := by
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ht h1]
    exact_mod_cast this

lemma funFromSet_le {S : Set (E × ℝ)} {x : E} {r : ℝ} (h : (x, r) ∈ S) :
    funFromSet S x ≤ r :=
  sInf_le ⟨r, h, rfl⟩

lemma le_funFromSet_iff {S : Set (E × ℝ)} {x : E} {c : EReal} :
    c ≤ funFromSet S x ↔ ∀ r : ℝ, (x, r) ∈ S → c ≤ r := by
  unfold funFromSet
  rw [le_sInf_iff]
  constructor
  · intro h r hr; exact h _ ⟨r, hr, rfl⟩
  · rintro h _ ⟨r, hr, rfl⟩; exact h r hr

lemma exists_of_funFromSet_lt_top {S : Set (E × ℝ)} {x : E} (h : funFromSet S x < ⊤) :
    ∃ r : ℝ, (x, r) ∈ S := by
  by_contra hne
  push_neg at hne
  have : (⊤ : EReal) ≤ funFromSet S x := le_funFromSet_iff.mpr (fun r hr => absurd hr (hne r))
  exact absurd h (not_lt.mpr this)

lemma funFromSet_epigraph (h : E → EReal) (x : E) : funFromSet (epigraph h) x = h x := by
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    exact (funFromSet_le (show h x ≤ (r : EReal) from hr1.le)).trans hr2.le
  · rw [le_funFromSet_iff]
    intro r hr
    exact hr

lemma part2_c {h : E → EReal} (h0 : 0 ∈ effDom h) (hh : IsERealPosHomogeneous h)
    (hne : (supportSublevelSet h).Nonempty) (w : E) :
    supportFunction (supportSublevelSet h) w = closedConvexHullFun h w := by
  obtain ⟨v0, hv0⟩ := hne
  apply le_antisymm
  · rw [supportFunction_le_iff]
    intro v hv
    unfold closedConvexHullFun
    rw [le_funFromSet_iff]
    intro r hr
    have hH : closure (convexHull ℝ (epigraph h)) ⊆ {q : E × ℝ | inner ℝ v q.1 ≤ q.2} := by
      apply closure_minimal
      · apply convexHull_min
        · intro q hq
          have := (hv q.1).trans hq
          exact_mod_cast this
        · intro p hp q hq a b ha hb hab
          simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
            smul_eq_mul, inner_add_right, real_inner_smul_right] at hp hq ⊢
          nlinarith [mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hq hb]
      · exact isClosed_le (continuous_const.inner continuous_fst) continuous_snd
    have := hH hr
    exact_mod_cast this
  · by_contra hlt
    push_neg at hlt
    have hbot : ((inner ℝ v0 w : ℝ) : EReal) ≤ supportFunction (supportSublevelSet h) w :=
      le_supportFunction _ w hv0
    have htop : supportFunction (supportSublevelSet h) w ≠ ⊤ := ne_top_of_lt hlt
    have hbot' : supportFunction (supportSublevelSet h) w ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hbot
    have hs := EReal.coe_toReal htop hbot'
    set s := (supportFunction (supportSublevelSet h) w).toReal with hsdef
    have hnot : (w, s) ∉ closure (convexHull ℝ (epigraph h)) := by
      intro hmem
      have h1 : closedConvexHullFun h w ≤ s := funFromSet_le hmem
      rw [hs] at h1
      exact absurd hlt (not_lt.mpr h1)
    obtain ⟨u, α, c, hα, hc, hCsep, hepi, hp⟩ := sep_epi h0 hh hnot
    simp only at hp
    rcases hα.lt_or_eq with hα' | hα'
    · have hmem := mem_sublevel_of_sep hα' hepi
      have h1 := le_supportFunction _ w hmem
      rw [← hs, real_inner_smul_left, real_inner_comm w u] at h1
      have h1' : (-α)⁻¹ * inner ℝ w u ≤ s := by exact_mod_cast h1
      rw [inv_mul_le_iff₀ (by linarith)] at h1'
      linarith
    · subst hα'
      simp only [zero_mul, add_zero] at hepi hp
      have hv0s : inner ℝ v0 w ≤ s := by
        rw [← hs] at hbot; exact_mod_cast hbot
      have hu : 0 < inner ℝ w u := by linarith
      have ht : 0 ≤ (s - inner ℝ v0 w + 1) / inner ℝ w u := div_nonneg (by linarith) hu.le
      have hmem := mem_sublevel_add ht hv0 hepi
      have h1 := le_supportFunction _ w hmem
      rw [← hs, inner_add_left, real_inner_smul_left, real_inner_comm w u] at h1
      have h1' : inner ℝ v0 w + (s - inner ℝ v0 w + 1) / inner ℝ w u * inner ℝ w u ≤ s := by
        exact_mod_cast h1
      rw [div_mul_cancel₀ _ hu.ne'] at h1'
      linarith

lemma part2_d {h : E → EReal} (h0 : 0 ∈ effDom h) (hh : IsERealPosHomogeneous h)
    (hempty : supportSublevelSet h = ∅) (w : E) :
    closedConvexHullFun h w = ⊥ ∨ closedConvexHullFun h w = ⊤ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hb, ht⟩ := hcon
  have hq := EReal.coe_toReal ht hb
  set q := (closedConvexHullFun h w).toReal with hqdef
  have hnot : (w, q - 1) ∉ closure (convexHull ℝ (epigraph h)) := by
    intro hmem
    have h1 : closedConvexHullFun h w ≤ ((q - 1 : ℝ) : EReal) := funFromSet_le hmem
    rw [← hq] at h1
    have : q ≤ q - 1 := by exact_mod_cast h1
    linarith
  obtain ⟨s', hs'⟩ := exists_of_funFromSet_lt_top
    (S := closure (convexHull ℝ (epigraph h))) (lt_top_iff_ne_top.mpr ht)
  obtain ⟨u, α, c, hα, hc, hCsep, hepi, hp⟩ := sep_epi h0 hh hnot
  rcases hα.lt_or_eq with hα' | hα'
  · have hmem := mem_sublevel_of_sep hα' hepi
    rw [hempty] at hmem
    exact hmem
  · subst hα'
    have := hCsep _ hs'
    simp only [zero_mul, add_zero] at this hp
    linarith

lemma part2_d' {h : E → EReal} (h0 : 0 ∈ effDom h) (hh : IsERealPosHomogeneous h)
    (hempty : supportSublevelSet h = ∅) : ¬ IsProper (closedConvexHullFun h) := by
  rintro ⟨hbot, -⟩
  have h1 : closedConvexHullFun h 0 ≤ ((0:ℝ):EReal) := by
    apply funFromSet_le
    apply subset_closure
    apply subset_convexHull
    show h 0 ≤ ((0:ℝ):EReal)
    simpa using posHom_zero_le h0 hh
  rcases part2_d h0 hh hempty 0 with h2 | h2
  · exact absurd h2 (hbot 0).ne'
  · rw [h2] at h1; exact absurd h1 (by simp)

lemma epigraph_closed {h : E → EReal} (hlsc : LowerSemicontinuous h) :
    IsClosed (epigraph h) := by
  have := hlsc.isClosed_epigraph
  exact this.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

lemma cchf_eq {h : E → EReal} (hlsc : LowerSemicontinuous h) (hconv : ConvexEReal h) (x : E) :
    closedConvexHullFun h x = h x := by
  unfold closedConvexHullFun
  rw [Convex.convexHull_eq hconv, (epigraph_closed hlsc).closure_eq, funFromSet_epigraph]

lemma effDom_eq_image (h : E → EReal) : effDom h = Prod.fst '' epigraph h := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, -⟩ := EReal.lt_iff_exists_real_btwn.mp (show h x < ⊤ from hx)
    exact ⟨(x, r), hr.le, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact lt_of_le_of_lt hp (EReal.coe_lt_top _)

lemma effDom_convex {h : E → EReal} (hconv : ConvexEReal h) : Convex ℝ (effDom h) := by
  rw [effDom_eq_image]
  exact Convex.linear_image hconv (LinearMap.fst ℝ E ℝ)

lemma ereal_mul_lt_top {t : ℝ} (ht : 0 < t) {a : EReal} (ha : a < ⊤) : (t:EReal) * a < ⊤ := by
  induction a using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ht]; exact bot_lt_top
  | top => exact absurd ha (lt_irrefl _)
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_lt_top _

lemma polarCone_closed (K : Set E) : IsClosed (polarCone K) := by
  have : polarCone K = ⋂ x ∈ K, {s : E | inner ℝ s x ≤ 0} := by
    ext s; simp [polarCone]
  rw [this]
  exact isClosed_biInter
    (fun x _ => isClosed_le (continuous_id.inner continuous_const) continuous_const)

lemma polar_horizon {h : E → EReal} (hprop : IsProper h) (hconv : ConvexEReal h)
    (h0 : 0 ∈ effDom h) (hh : IsERealPosHomogeneous h) (hne : (supportSublevelSet h).Nonempty) :
    polarCone (horizonCone (supportSublevelSet h)) = closure (effDom h) := by
  apply Set.Subset.antisymm
  · intro s hs
    by_contra hcon
    obtain ⟨u, c, hS, hc⟩ := sep_E (effDom_convex hconv).closure isClosed_closure hcon
    have hc0 : 0 < c := by
      have := hS 0 (subset_closure h0)
      simpa using this
    have hcone : ∀ x ∈ effDom h, inner ℝ x u ≤ 0 := by
      intro x hx
      by_contra hpos
      push_neg at hpos
      have ht : 0 < (c + 1) / inner ℝ x u := div_pos (by linarith) hpos
      have hmem : ((c + 1) / inner ℝ x u) • x ∈ effDom h := by
        show h _ < ⊤
        rw [hh x _ ht]
        exact ereal_mul_lt_top ht hx
      have := hS _ (subset_closure hmem)
      rw [real_inner_smul_left, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    obtain ⟨v0, hv0⟩ := hne
    have hu : u ∈ horizonCone (supportSublevelSet h) := by
      refine ⟨fun i => v0 + ((i:ℝ) + 1) • u, fun i => 1 / ((i:ℝ) + 1), ?_, ?_, ?_⟩
      · intro i
        apply mem_sublevel_add (by positivity) hv0
        intro q hq
        exact hcone q.1 (lt_of_le_of_lt hq (EReal.coe_lt_top _))
      · apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
        exact Filter.Eventually.of_forall (fun i => by simp only [Set.mem_Ioi]; positivity)
      · have e : (fun i : ℕ => (1 / ((i:ℝ) + 1)) • (v0 + ((i:ℝ) + 1) • u)) =
            fun i : ℕ => (1 / ((i:ℝ) + 1)) • v0 + u := by
          funext i
          have : ((i:ℝ) + 1) ≠ 0 := by positivity
          rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ this, one_smul]
        rw [e]
        have h1 : Filter.Tendsto (fun i : ℕ => (1 / ((i:ℝ) + 1)) • v0) Filter.atTop (𝓝 0) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const v0
          simpa using this
        simpa using h1.add_const u
    have := hs u hu
    linarith
  · apply closure_minimal _ (polarCone_closed _)
    intro x hx d hd
    obtain ⟨xseq, l, hmem, hl, hlim⟩ := hd
    have hxt : h x ≠ ⊤ := ne_of_lt hx
    have hxb : h x ≠ ⊥ := (hprop.1 x).ne'
    have hr := EReal.coe_toReal hxt hxb
    set r := (h x).toReal with hrdef
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := hl.mono_right nhdsWithin_le_nhds
    have hlpos : ∀ᶠ i in Filter.atTop, l i ∈ Set.Ioi 0 := (tendsto_nhdsWithin_iff.mp hl).2
    have h1 : Filter.Tendsto (fun i => inner ℝ x (l i • xseq i)) Filter.atTop (𝓝 (inner ℝ x d)) :=
      tendsto_const_nhds.inner hlim
    have h2 : Filter.Tendsto (fun i => l i * r) Filter.atTop (𝓝 (0 * r)) := hl0.mul_const r
    rw [zero_mul] at h2
    apply le_of_tendsto_of_tendsto h1 h2
    filter_upwards [hlpos] with i hi
    rw [real_inner_smul_right, real_inner_comm]
    have hxi := hmem i x
    rw [← hr] at hxi
    have : inner ℝ (xseq i) x ≤ r := by exact_mod_cast hxi
    exact mul_le_mul_of_nonneg_left this (le_of_lt hi)

theorem RW_chap_8_24
  (D : Set E)
  (h : E → EReal) :
  (IsSublinearRW (supportFunction D) ∧
    LowerSemicontinuous (supportFunction D) ∧
    (D.Nonempty → IsProper (supportFunction D)) ∧
    closure (convexHull ℝ D) =
      supportSublevelSet (supportFunction D)) ∧
  ((0 ∈ effDom h ∧ IsERealPosHomogeneous h) →
    let D' := supportSublevelSet h
    IsClosed D' ∧
    Convex ℝ D' ∧
    (D'.Nonempty → ∀ (w : E), supportFunction D' w = closedConvexHullFun h w) ∧
    (D' = ∅ →
      ¬ IsProper (closedConvexHullFun h) ∧
      ∀ (w : E), closedConvexHullFun h w = ⊥ ∨ closedConvexHullFun h w = ⊤)) ∧
  ((D.Nonempty ∧ IsClosed D ∧ Convex ℝ D) →
    IsProper (supportFunction D) ∧
    LowerSemicontinuous (supportFunction D) ∧
    IsSublinearRW (supportFunction D) ∧
    supportSublevelSet (supportFunction D) = D) ∧
  ((IsProper h ∧ LowerSemicontinuous h ∧ IsSublinearRW h) →
    let D' := supportSublevelSet h
    D'.Nonempty ∧
    IsClosed D' ∧
    Convex ℝ D' ∧
    (∀ (w : E), h w = supportFunction D' w) ∧
    (polarCone (horizonCone D') = closure (effDom h))) := by
  refine ⟨⟨supportFunction_sublinear D, supportFunction_lsc D, supportFunction_proper D,
    closure_convexHull_eq D⟩, ?_, ?_, ?_⟩
  · rintro ⟨h0, hh⟩
    exact ⟨supportSublevelSet_closed h, supportSublevelSet_convex h,
      fun hne w => part2_c h0 hh hne w,
      fun hempty => ⟨part2_d' h0 hh hempty, part2_d h0 hh hempty⟩⟩
  · rintro ⟨hne, hcl, hcv⟩
    refine ⟨supportFunction_proper D hne, supportFunction_lsc D, supportFunction_sublinear D, ?_⟩
    rw [← closure_convexHull_eq D, hcv.convexHull_eq, hcl.closure_eq]
  · rintro ⟨hprop, hlsc, ⟨h0, hh⟩, hconv⟩
    have hne : (supportSublevelSet h).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      apply part2_d' h0 hh hcon
      have : closedConvexHullFun h = h := funext (cchf_eq hlsc hconv)
      rw [this]
      exact hprop
    refine ⟨hne, supportSublevelSet_closed h, supportSublevelSet_convex h, ?_, ?_⟩
    · intro w
      rw [part2_c h0 hh hne w, cchf_eq hlsc hconv]
    · exact polar_horizon hprop hconv h0 hh hne

end RW_chap_8_24
