import ConvexStarLib.Defs

/-!
# `FCA_chap_E_2_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_2_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_2_2_1`, so the main result is `FCA_chap_E_2_2_1.FCA_chap_E_2_2_1`.
-/

namespace FCA_chap_E_2_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma FCA_E221_ereal_sub_le_iff (r c : ℝ) (y : EReal) :
    (r : EReal) - y ≤ c ↔ ((r - c : ℝ) : EReal) ≤ y := by
  induction y using EReal.rec with
  | bot =>
    constructor
    · intro h; simp at h
    · intro h; exact absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)
  | top => simp
  | coe y =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma FCA_E221_le_conjugate {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (ψ : X → EReal) (v x : X) : ((inner ℝ v x : ℝ) : EReal) - ψ x ≤ conjugate ψ v :=
  le_sSup ⟨x, Set.mem_univ _, rfl⟩

lemma FCA_E221_conjugate_le_iff {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (ψ : X → EReal) (v : X) (c : EReal) :
    conjugate ψ v ≤ c ↔ ∀ x, ((inner ℝ v x : ℝ) : EReal) - ψ x ≤ c := by
  unfold conjugate
  rw [sSup_le_iff]
  constructor
  · intro h x; exact h _ ⟨x, Set.mem_univ _, rfl⟩
  · rintro h _ ⟨x, -, rfl⟩; exact h x

lemma FCA_E221_conjugate_le_real_iff {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (ψ : X → EReal) (v : X) (c : ℝ) :
    conjugate ψ v ≤ c ↔ ∀ x, ((inner ℝ v x - c : ℝ) : EReal) ≤ ψ x := by
  rw [FCA_E221_conjugate_le_iff]
  simp only [FCA_E221_ereal_sub_le_iff]

lemma FCA_E221_biconj_ge_affine {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (ψ : X → EReal) (w : X) (c : ℝ) (hw : ∀ x, (((inner ℝ w x) - c : ℝ) : EReal) ≤ ψ x)
    (x₀ : X) :
    (((inner ℝ w x₀) - c : ℝ) : EReal) ≤ conjugate (conjugate ψ) x₀ := by
  have h1 : conjugate ψ w ≤ (c : EReal) := (FCA_E221_conjugate_le_real_iff ψ w c).mpr hw
  calc (((inner ℝ w x₀) - c : ℝ) : EReal) = ((inner ℝ x₀ w : ℝ) : EReal) - (c : EReal) := by
        rw [real_inner_comm, EReal.coe_sub]
    _ ≤ ((inner ℝ x₀ w : ℝ) : EReal) - conjugate ψ w := EReal.sub_le_sub le_rfl h1
    _ ≤ _ := FCA_E221_le_conjugate _ _ _

lemma FCA_E221_conjugate_lsc {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (ψ : X → EReal) : LowerSemicontinuous (conjugate ψ) := by
  intro v c hc
  unfold conjugate at hc
  obtain ⟨_, ⟨x, -, rfl⟩, hx⟩ := lt_sSup_iff.mp hc
  simp only at hx
  have : ∀ᶠ v' in 𝓝 v, c < ((inner ℝ v' x : ℝ) : EReal) - ψ x := by
    induction hψ : ψ x using EReal.rec with
    | bot =>
      rw [hψ] at hx
      filter_upwards with v'
      simp only [EReal.coe_sub_bot]
      exact lt_of_lt_of_le hx le_top
    | top =>
      rw [hψ] at hx
      simp at hx
    | coe y =>
      rw [hψ] at hx
      have hcont : Continuous (fun v' : X => ((inner ℝ v' x - y : ℝ) : EReal)) :=
        continuous_coe_real_ereal.comp (by fun_prop)
      rw [← EReal.coe_sub] at hx
      filter_upwards [(hcont.tendsto v).eventually (lt_mem_nhds hx)] with v' hv'
      rw [← EReal.coe_sub]
      exact hv'
  filter_upwards [this] with v' hv'
  exact lt_of_lt_of_le hv' (FCA_E221_le_conjugate ψ v' x)

lemma FCA_E221_lscHull_le_biconj {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X]
    (ψ : X → EReal) (S : Set (X × ℝ)) (hS : Convex ℝ S)
    (hS1 : ∀ x (t : ℝ), ψ x < t → (x, t) ∈ S)
    (hS2 : ∀ p ∈ S, ψ p.1 ≤ p.2)
    (w₀ : X) (c₀ : ℝ) (hmin : ∀ x, (((inner ℝ w₀ x) - c₀ : ℝ) : EReal) ≤ ψ x) (x₀ : X) :
    lscHull ψ x₀ ≤ conjugate (conjugate ψ) x₀ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨r₁, hr₁, hr₁'⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  obtain ⟨r₂, hr₂, hr₂'⟩ := EReal.lt_iff_exists_real_btwn.mp hr₁'
  have hr12 : r₁ < r₂ := EReal.coe_lt_coe_iff.mp hr₂
  suffices H : ∃ (w : X) (c : ℝ), (∀ x, (((inner ℝ w x) - c : ℝ) : EReal) ≤ ψ x) ∧
      r₁ < inner ℝ w x₀ - c by
    obtain ⟨w, c, hw, hc⟩ := H
    have h1 := FCA_E221_biconj_ge_affine ψ w c hw x₀
    have h2 : ((r₁ : ℝ) : EReal) < conjugate (conjugate ψ) x₀ :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hc) h1
    exact absurd hr₁ (not_lt.mpr h2.le)
  have hev : ∀ᶠ x in 𝓝 x₀, ((r₂ : ℝ) : EReal) < ψ x := Filter.eventually_lt_of_lt_liminf hr₂'
  have hnot : (x₀, r₁) ∉ closure S := by
    rw [mem_closure_iff_frequently, Filter.not_frequently, nhds_prod_eq]
    have h2 : ∀ᶠ t in 𝓝 r₁, t < r₂ := eventually_lt_nhds hr12
    filter_upwards [hev.prod_mk h2] with p hp
    intro hpS
    have h3 := hS2 p hpS
    have h4 : ((p.2 : ℝ) : EReal) < r₂ := EReal.coe_lt_coe_iff.mpr hp.2
    exact absurd (lt_of_le_of_lt h3 (h4.trans hp.1)) (lt_irrefl _)
  obtain ⟨f, u, hf, hfu⟩ := geometric_hahn_banach_closed_point hS.closure isClosed_closure hnot
  set fX : StrongDual ℝ X := f.comp (ContinuousLinearMap.inl ℝ X ℝ) with hfX
  set w : X := (InnerProductSpace.toDual ℝ X).symm fX with hw
  set α : ℝ := f (0, 1) with hα
  have hf_eq : ∀ x (t : ℝ), f (x, t) = inner ℝ w x + t * α := by
    intro x t
    have : ((x, t) : X × ℝ) = ((x, 0) : X × ℝ) + t • ((0, 1) : X × ℝ) := by simp
    rw [this, f.map_add, f.map_smul, smul_eq_mul, hw, InnerProductSpace.toDual_symm_apply]
    simp [fX, hα]
  have hkey : ∀ x (t : ℝ), ψ x < t → inner ℝ w x + t * α < u := by
    intro x t hxt
    rw [← hf_eq]
    exact hf _ (subset_closure (hS1 x t hxt))
  have hkey0 : u < inner ℝ w x₀ + r₁ * α := by rw [← hf_eq]; exact hfu
  rcases lt_trichotomy α 0 with hneg | hzero | hpos
  · -- α < 0
    refine ⟨(-α)⁻¹ • w, u / (-α), ?_, ?_⟩
    · intro x
      by_contra hlt
      push_neg at hlt
      have h1 := hkey x _ hlt
      rw [real_inner_smul_left] at h1
      have hα' : α ≠ 0 := hneg.ne
      have hLα : ((-α)⁻¹ * inner ℝ w x - u / (-α)) * α = u - inner ℝ w x := by
        field_simp
        ring
      rw [hLα] at h1
      linarith
    · rw [real_inner_smul_left]
      have e : (-α)⁻¹ * inner ℝ w x₀ - u / (-α) = (inner ℝ w x₀ - u) / (-α) := by ring
      rw [e, lt_div_iff₀ (by linarith)]
      linarith
  · -- α = 0
    have hdom : ∀ x, ψ x < ⊤ → inner ℝ w x < u := by
      intro x hx
      obtain ⟨t, ht, -⟩ := EReal.lt_iff_exists_real_btwn.mp hx
      have := hkey x t ht
      rw [hzero, mul_zero, add_zero] at this
      exact this
    have hd : 0 < inner ℝ w x₀ - u := by
      rw [hzero, mul_zero, add_zero] at hkey0; linarith
    set m := inner ℝ w₀ x₀ - c₀ with hm
    set d := inner ℝ w x₀ - u with hd_def
    set lam := |r₁ - m| / d + 1 with hlam_def
    have hlam : 0 ≤ lam := by positivity
    refine ⟨w₀ + lam • w, c₀ + lam * u, ?_, ?_⟩
    · intro x
      rcases eq_or_lt_of_le (le_top : ψ x ≤ ⊤) with htop | hlt
      · rw [htop]; exact le_top
      · have h1 := hdom x hlt
        refine le_trans ?_ (hmin x)
        rw [EReal.coe_le_coe_iff, inner_add_left, real_inner_smul_left]
        nlinarith
    · rw [inner_add_left, real_inner_smul_left]
      have e1 : lam * d = |r₁ - m| + d := by
        rw [hlam_def]
        field_simp
      have e2 : r₁ - m ≤ |r₁ - m| := le_abs_self _
      have e3 : inner ℝ w₀ x₀ + lam * inner ℝ w x₀ - (c₀ + lam * u) = m + lam * d := by
        rw [hm, hd_def]; ring
      rw [e3, e1]
      linarith
  · -- α > 0
    refine ⟨0, -(r₁ + 1), ?_, ?_⟩
    · intro x
      simp only [inner_zero_left, zero_sub, neg_neg]
      by_contra hlt
      push_neg at hlt
      set t := max (r₁ + 1) ((u - inner ℝ w x) / α + 1) with ht_def
      have ht : ψ x < t := lt_of_lt_of_le hlt (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
      have h1 := hkey x t ht
      have h2 : (u - inner ℝ w x) / α + 1 ≤ t := le_max_right _ _
      have h3 : ((u - inner ℝ w x) / α + 1) * α ≤ t * α := mul_le_mul_of_nonneg_right h2 hpos.le
      have h4 : ((u - inner ℝ w x) / α + 1) * α = u - inner ℝ w x + α := by
        field_simp
      linarith
    · simp

lemma FCA_E221_aux1 (a b : ℝ) (G C : EReal) (h : ((a + b : ℝ) : EReal) - G ≤ C) :
    (a : EReal) - G ≤ C - b := by
  induction G using EReal.rec with
  | bot =>
    rw [EReal.coe_sub_bot, top_le_iff] at h
    rw [h, EReal.coe_sub_bot, EReal.top_sub_coe]
  | top => rw [EReal.sub_top]; exact bot_le
  | coe G =>
    induction C using EReal.rec with
    | bot =>
      rw [← EReal.coe_sub, le_bot_iff] at h
      exact absurd h (EReal.coe_ne_bot _)
    | top => rw [EReal.top_sub_coe]; exact le_top
    | coe C =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith

lemma FCA_E221_aux2 (a b : ℝ) (C : EReal) :
    ((a + b : ℝ) : EReal) - C ≤ (a : EReal) - (C - b) := by
  induction C using EReal.rec with
  | bot => rw [EReal.coe_sub_bot, EReal.bot_sub, EReal.coe_sub_bot]
  | top => rw [EReal.sub_top]; exact bot_le
  | coe C =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith

lemma FCA_E221_aux3 (b t : ℝ) (C : EReal) (h : C - (b : EReal) < t) :
    C < ((t + b : ℝ) : EReal) := by
  induction C using EReal.rec with
  | bot => exact EReal.bot_lt_coe _
  | top => rw [EReal.top_sub_coe] at h; exact absurd h (not_lt.mpr le_top)
  | coe C =>
    rw [← EReal.coe_sub, EReal.coe_lt_coe_iff] at h
    rw [EReal.coe_lt_coe_iff]
    linarith

theorem FCA_chap_E_2_2_1
  (g : F → EReal)
  (y₀ : F)
  (A₀ : E →ₗ[ℝ] F)
  (hg_closed_convex : InClosedConvRn g)
  (hg_nondegenerate : IsNondegenerate g)
  (h_nonempty_domain : Set.Nonempty ((Set.image (fun v => A₀ v + y₀) Set.univ) ∩
    effDom g)) :
  let gA := fun x => g (A₀ x + y₀)
  let h := fun s => sInf {v | ∃ p, (v = (conjugate g p) - (inner ℝ y₀ p)) ∧ (A₀.adjoint p = s)}
  (InClosedConvRn gA) ∧
  (∀ s, (conjugate gA s) = lscHull h s) := by
  intro gA h
  obtain ⟨⟨hg_bot, -, hg_conv⟩, hg_lsc⟩ := hg_closed_convex
  obtain ⟨-, s₀, b₀, hs₀⟩ := hg_nondegenerate
  have hgA_bot : ∀ x, ⊥ < gA x := fun x => hg_bot _
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, gA x₀ < ⊤ := by
    obtain ⟨y, ⟨x, -, rfl⟩, hy⟩ := h_nonempty_domain
    exact ⟨x, hy⟩
  have hgA_conv : ConvexEReal gA := by
    intro p hp q hq a b ha hb hab
    have key := hg_conv (x := (A₀ p.1 + y₀, p.2)) hp (y := (A₀ q.1 + y₀, q.2)) hq ha hb hab
    have e : A₀ (a • p.1 + b • q.1) + y₀ = a • (A₀ p.1 + y₀) + b • (A₀ q.1 + y₀) := by
      rw [map_add, map_smul, map_smul, smul_add, smul_add]
      have : y₀ = a • y₀ + b • y₀ := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [this]
      abel
    show g (A₀ (a • p + b • q).1 + y₀) ≤ ((a • p + b • q).2 : EReal)
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd]
    rw [e]
    exact key
  have hgA_lsc : LowerSemicontinuous gA := by
    have hc : Continuous (fun x => A₀ x + y₀) :=
      A₀.continuous_of_finiteDimensional.add continuous_const
    exact hg_lsc.comp hc
  have hgA : InClosedConvRn gA := ⟨⟨hgA_bot, ⟨x₀, hx₀⟩, hgA_conv⟩, hgA_lsc⟩
  refine ⟨hgA, ?_⟩
  -- (gA)^* ≤ h
  have hconj_le_h : ∀ s, conjugate gA s ≤ h s := by
    intro s
    apply le_sInf
    rintro v ⟨p, rfl, hp⟩
    rw [FCA_E221_conjugate_le_iff]
    intro x
    have h1 := FCA_E221_le_conjugate g p (A₀ x + y₀)
    have e1 : inner ℝ s x = inner ℝ p (A₀ x) := by rw [← hp, LinearMap.adjoint_inner_left]
    rw [inner_add_right] at h1
    show ((inner ℝ s x : ℝ) : EReal) - g (A₀ x + y₀) ≤
      conjugate g p - ((inner ℝ y₀ p : ℝ) : EReal)
    rw [e1, real_inner_comm p y₀]
    exact FCA_E221_aux1 _ _ _ _ h1
  intro s
  apply le_antisymm
  · -- (gA)^* s ≤ lscHull h s
    calc conjugate gA s ≤ Filter.liminf (conjugate gA) (𝓝 s) :=
          (FCA_E221_conjugate_lsc gA).le_liminf s
      _ ≤ Filter.liminf h (𝓝 s) :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hconj_le_h)
  · -- lscHull h s ≤ (gA)^* s
    have hFMg : ∀ y, g y ≤ conjugate (conjugate g) y := by
      intro y
      calc g y ≤ lscHull g y := hg_lsc.le_liminf y
        _ ≤ conjugate (conjugate g) y :=
          FCA_E221_lscHull_le_biconj g (epigraph g) hg_conv (fun x t ht => ht.le)
            (fun p hp => hp) s₀ b₀ (fun x => by have := hs₀ x; rwa [EReal.coe_sub]) y
    have hhconj : ∀ x, gA x ≤ conjugate h x := by
      intro x
      refine le_trans (hFMg _) ?_
      rw [FCA_E221_conjugate_le_iff]
      intro p
      have h1 := FCA_E221_le_conjugate h x (A₀.adjoint p)
      have h2 : h (A₀.adjoint p) ≤ conjugate g p - ((inner ℝ y₀ p : ℝ) : EReal) :=
        sInf_le ⟨p, rfl, rfl⟩
      refine le_trans ?_ h1
      refine le_trans ?_ (EReal.sub_le_sub le_rfl h2)
      rw [LinearMap.adjoint_inner_right, inner_add_left]
      exact FCA_E221_aux2 _ _ _
    have hx₀' : ⊥ < gA x₀ := hgA_bot x₀
    set G₀ := (gA x₀).toReal with hG₀_def
    have hG₀ : gA x₀ = G₀ := (EReal.coe_toReal hx₀.ne hx₀'.ne').symm
    have hmin_h : ∀ s', ((inner ℝ x₀ s' - G₀ : ℝ) : EReal) ≤ h s' := by
      intro s'
      refine le_trans ?_ (hconj_le_h s')
      refine le_trans ?_ (FCA_E221_le_conjugate gA s' x₀)
      rw [hG₀, real_inner_comm, EReal.coe_sub]
    have hconv_h : Convex ℝ {p : E × ℝ | h p.1 < p.2} := by
      intro q₁ hq₁ q₂ hq₂ a b ha hb hab
      simp only [Set.mem_setOf_eq] at hq₁ hq₂ ⊢
      obtain ⟨_, ⟨p₁, rfl, hp₁⟩, hv₁⟩ := sInf_lt_iff.mp hq₁
      obtain ⟨_, ⟨p₂, rfl, hp₂⟩, hv₂⟩ := sInf_lt_iff.mp hq₂
      obtain ⟨d₁, hd₁, hd₁'⟩ := EReal.lt_iff_exists_real_btwn.mp (FCA_E221_aux3 _ _ _ hv₁)
      obtain ⟨d₂, hd₂, hd₂'⟩ := EReal.lt_iff_exists_real_btwn.mp (FCA_E221_aux3 _ _ _ hv₂)
      rw [EReal.coe_lt_coe_iff] at hd₁' hd₂'
      have hm₁ := (FCA_E221_conjugate_le_real_iff g p₁ d₁).mp hd₁.le
      have hm₂ := (FCA_E221_conjugate_le_real_iff g p₂ d₂).mp hd₂.le
      have hm : conjugate g (a • p₁ + b • p₂) ≤ ((a * d₁ + b * d₂ : ℝ) : EReal) := by
        rw [FCA_E221_conjugate_le_real_iff]
        intro y
        have h1 := hm₁ y
        have h2 := hm₂ y
        generalize g y = G at h1 h2 ⊢
        induction G using EReal.rec with
        | bot => exact absurd (le_bot_iff.mp h1) (EReal.coe_ne_bot _)
        | top => exact le_top
        | coe G =>
          rw [EReal.coe_le_coe_iff] at h1 h2 ⊢
          rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
          have hb' : b = 1 - a := by linarith
          subst hb'
          nlinarith [mul_nonneg ha (sub_nonneg.mpr h1), mul_nonneg hb (sub_nonneg.mpr h2)]
      have hadj : A₀.adjoint (a • p₁ + b • p₂) = (a • q₁ + b • q₂).1 := by
        simp [map_add, map_smul, hp₁, hp₂]
      refine lt_of_le_of_lt (sInf_le ⟨a • p₁ + b • p₂, rfl, hadj⟩) ?_
      refine lt_of_le_of_lt (EReal.sub_le_sub hm le_rfl) ?_
      rw [← EReal.coe_sub, EReal.coe_lt_coe_iff]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, inner_add_right,
        real_inner_smul_right]
      rcases ha.eq_or_lt with ha0 | ha0
      · subst ha0
        have : b = 1 := by linarith
        subst this
        linarith
      · nlinarith [mul_pos ha0 (sub_pos.mpr hd₁'), mul_nonneg hb (sub_nonneg.mpr hd₂'.le)]
    calc lscHull h s ≤ conjugate (conjugate h) s :=
          FCA_E221_lscHull_le_biconj h {p | h p.1 < p.2} hconv_h (fun x t ht => ht)
            (fun p hp => le_of_lt hp) x₀ G₀ hmin_h s
      _ ≤ conjugate gA s := by
        rw [FCA_E221_conjugate_le_iff]
        intro x
        exact le_trans (EReal.sub_le_sub le_rfl (hhconj x)) (FCA_E221_le_conjugate gA s x)

end FCA_chap_E_2_2_1
