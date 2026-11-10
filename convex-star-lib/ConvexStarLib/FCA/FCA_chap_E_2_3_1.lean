import ConvexStarLib.Defs

/-!
# `FCA_chap_E_2_3_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_2_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_2_3_1`, so the main result is `FCA_chap_E_2_3_1.FCA_chap_E_2_3_1`.
-/

namespace FCA_chap_E_2_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### EReal helpers -/

lemma aux_le_of_forall {z : EReal} {a : ℝ} (H : ∀ r : ℝ, z ≤ (r : EReal) → a ≤ r) :
    (a : EReal) ≤ z := by
  by_contra h
  push_neg at h
  obtain ⟨r, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp h
  have := H r h1.le
  exact absurd (EReal.coe_lt_coe_iff.mp h2) (not_lt.mpr this)

lemma aux_sub_le_iff (a c : ℝ) (z : EReal) :
    (a : EReal) - z ≤ (c : EReal) ↔ (((a - c : ℝ)) : EReal) ≤ z := by
  induction z using EReal.rec with
  | bot =>
    rw [EReal.coe_sub_bot]
    simp only [top_le_iff, le_bot_iff, EReal.coe_ne_top, EReal.coe_ne_bot]
  | top => simp [EReal.sub_top]
  | coe r =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma aux_sub_le_of_forall {a : ℝ} {z w : EReal}
    (H : ∀ c : ℝ, z ≤ (c : EReal) → (((a - c : ℝ)) : EReal) ≤ w) : (a : EReal) - z ≤ w := by
  induction z using EReal.rec with
  | bot =>
    rw [EReal.coe_sub_bot]
    by_contra hw
    push_neg at hw
    obtain ⟨r, h1, -⟩ := EReal.lt_iff_exists_real_btwn.mp hw
    have := H (a - r - 1) bot_le
    have h3 : (((a - (a - r - 1) : ℝ)) : EReal) ≤ (r : EReal) := this.trans h1.le
    rw [EReal.coe_le_coe_iff] at h3
    linarith
  | top => rw [EReal.sub_top]; exact bot_le
  | coe r => rw [← EReal.coe_sub]; exact H r le_rfl

lemma aux_add_lt_decomp {A B : EReal} {r : ℝ} (hA : ⊥ < A) (hB : ⊥ < B)
    (h : A + B < (r : EReal)) : ∃ a b : ℝ, A = a ∧ B = b ∧ a + b < r := by
  induction A using EReal.rec with
  | bot => exact absurd hA (lt_irrefl _)
  | top =>
    rw [EReal.top_add_of_ne_bot hB.ne'] at h
    exact absurd h (not_lt.mpr le_top)
  | coe a =>
    induction B using EReal.rec with
    | bot => exact absurd hB (lt_irrefl _)
    | top =>
      rw [EReal.coe_add_top] at h
      exact absurd h (not_lt.mpr le_top)
    | coe b =>
      refine ⟨a, b, rfl, rfl, ?_⟩
      rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h
      exact h

lemma aux_lt_add_decomp {A B : EReal} {r : ℝ} (hA : ⊥ < A) (hB : ⊥ < B)
    (h : (r : EReal) < A + B) : ∃ a b : ℝ, (a : EReal) < A ∧ (b : EReal) < B ∧ r < a + b := by
  induction A using EReal.rec with
  | bot => exact absurd hA (lt_irrefl _)
  | top =>
    induction B using EReal.rec with
    | bot => exact absurd hB (lt_irrefl _)
    | top => exact ⟨r, 1, EReal.coe_lt_top _, EReal.coe_lt_top _, by linarith⟩
    | coe b =>
      refine ⟨r - b + 2, b - 1, EReal.coe_lt_top _, ?_, by linarith⟩
      rw [EReal.coe_lt_coe_iff]; linarith
  | coe a =>
    induction B using EReal.rec with
    | bot => exact absurd hB (lt_irrefl _)
    | top =>
      refine ⟨a - 1, r - a + 2, ?_, EReal.coe_lt_top _, by linarith⟩
      rw [EReal.coe_lt_coe_iff]; linarith
    | coe b =>
      rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h
      refine ⟨a - (a + b - r) / 3, b - (a + b - r) / 3, ?_, ?_, by linarith⟩
      · rw [EReal.coe_lt_coe_iff]; linarith
      · rw [EReal.coe_lt_coe_iff]; linarith

/-! ### conjugate helpers -/

lemma conj_le_iff (g : E → EReal) (y : E) (c : ℝ) :
    conjugate g y ≤ (c : EReal) ↔ ∀ x, (((inner ℝ y x - c : ℝ)) : EReal) ≤ g x := by
  unfold conjugate
  rw [sSup_le_iff]
  constructor
  · intro h x
    exact (aux_sub_le_iff _ _ _).mp (h _ ⟨x, Set.mem_univ _, rfl⟩)
  · rintro h _ ⟨x, -, rfl⟩
    exact (aux_sub_le_iff _ _ _).mpr (h x)

lemma le_conj (g : E → EReal) (y x : E) :
    ((inner ℝ y x : ℝ) : EReal) - g x ≤ conjugate g y :=
  le_sSup ⟨x, Set.mem_univ _, rfl⟩

lemma le_conj_of_le (g : E → EReal) (y x : E) (c : ℝ) (hc : g x ≤ (c : EReal)) :
    (((inner ℝ y x - c : ℝ)) : EReal) ≤ conjugate g y := by
  refine le_trans ?_ (le_conj g y x)
  rw [EReal.coe_sub]
  exact EReal.sub_le_sub le_rfl hc

lemma conj_bot_lt (g : E → EReal) (x₀ : E) (hx₀ : g x₀ < ⊤) (y : E) :
    ⊥ < conjugate g y := by
  refine lt_of_lt_of_le ?_ (le_conj g y x₀)
  induction h : g x₀ using EReal.rec with
  | bot => rw [EReal.coe_sub_bot]; exact bot_lt_top
  | top => rw [h] at hx₀; exact absurd hx₀ (lt_irrefl _)
  | coe r => rw [← EReal.coe_sub]; exact EReal.bot_lt_coe _

lemma affine_comb (g : E → EReal) (y₁ y₂ : E) (c₁ c₂ : ℝ)
    (h₁ : ∀ x, (((inner ℝ y₁ x - c₁ : ℝ)) : EReal) ≤ g x)
    (h₂ : ∀ x, (((inner ℝ y₂ x - c₂ : ℝ)) : EReal) ≤ g x)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∀ x, (((inner ℝ (a • y₁ + b • y₂) x - (a * c₁ + b * c₂) : ℝ)) : EReal) ≤ g x := by
  intro x
  apply aux_le_of_forall
  intro r hr
  have e1 := EReal.coe_le_coe_iff.mp ((h₁ x).trans hr)
  have e2 := EReal.coe_le_coe_iff.mp ((h₂ x).trans hr)
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have k1 := mul_le_mul_of_nonneg_left e1 ha
  have k2 := mul_le_mul_of_nonneg_left e2 hb
  have k3 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  rw [mul_sub] at k1 k2
  linarith

/-! ### separation -/

lemma not_mem_closure_epi (F : E → EReal) (s : E) (α α' : ℝ) (hαα' : α < α')
    (h : ∀ᶠ t in 𝓝 s, ((α' : ℝ) : EReal) < F t) : (s, α) ∉ closure (epigraph F) := by
  rw [mem_closure_iff_nhds]
  push_neg
  refine ⟨{p : E × ℝ | ((α' : ℝ) : EReal) < F p.1 ∧ p.2 < α'}, ?_, ?_⟩
  · have h1 : ∀ᶠ p : E × ℝ in 𝓝 (s, α), ((α' : ℝ) : EReal) < F p.1 :=
      (continuous_fst.tendsto (s, α)).eventually h
    have h2 : ∀ᶠ p : E × ℝ in 𝓝 (s, α), p.2 < α' :=
      (continuous_snd.tendsto (s, α)).eventually (gt_mem_nhds hαα')
    exact h1.and h2
  · ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, epigraph, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨h1, h2⟩, h3⟩
    have : F p.1 < ((α' : ℝ) : EReal) := lt_of_le_of_lt h3 (EReal.coe_lt_coe_iff.mpr h2)
    exact lt_asymm h1 this

lemma exists_real_ge (z : EReal) (hz : z < ⊤) : ∃ r : ℝ, z ≤ (r : EReal) := by
  induction z using EReal.rec with
  | bot => exact ⟨0, bot_le⟩
  | top => exact absurd hz (lt_irrefl _)
  | coe r => exact ⟨r, le_rfl⟩

lemma separation (F : E → EReal) (hF : Convex ℝ (epigraph F)) (s : E) (α : ℝ)
    (hs : (s, α) ∉ closure (epigraph F)) :
    (∃ x : E, ∃ β : ℝ, (∀ t, (((inner ℝ x t - β : ℝ)) : EReal) ≤ F t) ∧
        α < inner ℝ x s - β) ∨
    (∃ y : E, ∃ u : ℝ, (∀ t, F t < ⊤ → inner ℝ y t < u) ∧ u < inner ℝ y s) := by
  obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point hF.closure isClosed_closure hs
  set τ : ℝ := f ((0 : E), (1 : ℝ)) with hτ
  set ℓ : StrongDual ℝ E := f.comp (ContinuousLinearMap.inl ℝ E ℝ) with hℓ
  have hf_apply : ∀ (t : E) (r : ℝ), f (t, r) = ℓ t + r * τ := by
    intro t r
    have : ((t, r) : E × ℝ) = (t, (0 : ℝ)) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul]
    simp [ℓ, τ, smul_eq_mul]
  set y : E := (InnerProductSpace.toDual ℝ E).symm ℓ with hy_def
  have hy : ∀ t, inner ℝ y t = ℓ t := fun t => InnerProductSpace.toDual_symm_apply
  have hepi : ∀ (t : E) (r : ℝ), F t ≤ (r : EReal) → ℓ t + r * τ < u := by
    intro t r h
    rw [← hf_apply]
    exact hf _ (subset_closure h)
  have hu' : u < ℓ s + α * τ := by rw [← hf_apply]; exact hu
  rcases lt_trichotomy τ 0 with hneg | hzero | hpos
  · -- non-vertical
    left
    have hτne : τ ≠ 0 := hneg.ne
    refine ⟨(-τ)⁻¹ • y, u / (-τ), ?_, ?_⟩
    · intro t
      apply aux_le_of_forall
      intro r hr
      have h1 := hepi t r hr
      rw [real_inner_smul_left, hy]
      have hτ' : 0 < -τ := neg_pos.mpr hneg
      rw [← sub_nonneg]
      have : r - ((-τ)⁻¹ * ℓ t - u / (-τ)) = (u - (ℓ t + r * τ)) / (-τ) + 0 := by
        field_simp
        ring
      rw [this]
      have : 0 < (u - (ℓ t + r * τ)) / (-τ) := div_pos (by linarith) hτ'
      linarith
    · rw [real_inner_smul_left, hy]
      have hτ' : 0 < -τ := neg_pos.mpr hneg
      have : (-τ)⁻¹ * ℓ s - u / (-τ) - α = ((ℓ s + α * τ) - u) / (-τ) := by
        field_simp
        ring
      have h2 : 0 < ((ℓ s + α * τ) - u) / (-τ) := div_pos (by linarith) hτ'
      linarith
  · -- vertical
    right
    refine ⟨y, u, ?_, ?_⟩
    · intro t ht
      obtain ⟨r, hr⟩ := exists_real_ge (F t) ht
      have := hepi t r hr
      rw [hzero, mul_zero, add_zero] at this
      rw [hy]; exact this
    · rw [hzero, mul_zero, add_zero] at hu'
      rw [hy]; exact hu'
  · -- empty domain
    right
    refine ⟨0, -1, ?_, ?_⟩
    · intro t ht
      exfalso
      obtain ⟨r, hr⟩ := exists_real_ge (F t) ht
      set r' : ℝ := max r ((u - ℓ t) / τ) with hr'
      have hr'1 : F t ≤ (r' : EReal) := hr.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
      have h1 := hepi t r' hr'1
      have h2 : (u - ℓ t) / τ ≤ r' := le_max_right _ _
      have h3 : u - ℓ t ≤ r' * τ := by
        rw [div_le_iff₀ hpos] at h2; exact h2
      linarith
    · simp

lemma separation' (F : E → EReal) (hF : Convex ℝ (epigraph F)) (s : E) (α : ℝ)
    (hs : (s, α) ∉ closure (epigraph F))
    (x₀ : E) (β₀ : ℝ) (h₀ : ∀ t, (((inner ℝ x₀ t - β₀ : ℝ)) : EReal) ≤ F t) :
    ∃ x : E, ∃ β : ℝ, (∀ t, (((inner ℝ x t - β : ℝ)) : EReal) ≤ F t) ∧
        α < inner ℝ x s - β := by
  rcases separation F hF s α hs with h | ⟨y, u, hy, hu⟩
  · exact h
  · set k : ℝ := (|α - (inner ℝ x₀ s - β₀)| + 1) / (inner ℝ y s - u) with hk
    have hpos : 0 < inner ℝ y s - u := by linarith
    have hk0 : 0 ≤ k := div_nonneg (by positivity) hpos.le
    have hk1 : k * (inner ℝ y s - u) = |α - (inner ℝ x₀ s - β₀)| + 1 := by
      rw [hk]; field_simp
    refine ⟨x₀ + k • y, β₀ + k * u, ?_, ?_⟩
    · intro t
      by_cases ht : F t < ⊤
      · have h1 := hy t ht
        refine le_trans ?_ (h₀ t)
        rw [EReal.coe_le_coe_iff, inner_add_left, real_inner_smul_left]
        nlinarith
      · rw [not_lt, top_le_iff] at ht
        rw [ht]; exact le_top
    · rw [inner_add_left, real_inner_smul_left]
      have := le_abs_self (α - (inner ℝ x₀ s - β₀))
      nlinarith

/-! ### Fenchel–Moreau for closed convex proper functions -/

lemma fm (g : E → EReal) (hg : InClosedConvRn g) (x : E) (a : ℝ) (ha : (a : EReal) < g x) :
    ∃ y : E, ∃ b : ℝ, (∀ t, (((inner ℝ y t - b : ℝ)) : EReal) ≤ g t) ∧ a < inner ℝ y x - b := by
  obtain ⟨⟨hbot, ⟨x₀, hx₀⟩, hconv⟩, hlsc⟩ := hg
  have hnot : ∀ z : E, ∀ c : ℝ, (c : EReal) < g z → (z, c) ∉ closure (epigraph g) := by
    intro z c hc
    obtain ⟨c', hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    exact not_mem_closure_epi g z c c' (EReal.coe_lt_coe_iff.mp hc1) (hlsc z _ hc2)
  have hmin : ∃ y₀ : E, ∃ b₀ : ℝ, ∀ t, (((inner ℝ y₀ t - b₀ : ℝ)) : EReal) ≤ g t := by
    have hlt : ((((g x₀).toReal - 1 : ℝ)) : EReal) < g x₀ := by
      conv_rhs => rw [← EReal.coe_toReal hx₀.ne (hbot x₀).ne']
      rw [EReal.coe_lt_coe_iff]; linarith
    rcases separation g hconv x₀ _ (hnot x₀ _ hlt) with ⟨y₀, b₀, h, -⟩ | ⟨y, u, hy, hu⟩
    · exact ⟨y₀, b₀, h⟩
    · exact absurd (hy x₀ hx₀) (not_lt.mpr hu.le)
  obtain ⟨y₀, b₀, h₀⟩ := hmin
  exact separation' g hconv x a (hnot x a ha) y₀ b₀ h₀

/-! ### infimal convolution -/

lemma infConv_le (f₁ f₂ : E → EReal) (x y : E) : infimalConv f₁ f₂ x ≤ f₁ y + f₂ (x - y) :=
  sInf_le ⟨y, rfl⟩

lemma infConv_lt {f₁ f₂ : E → EReal} {x : E} {c : EReal} (h : infimalConv f₁ f₂ x < c) :
    ∃ y, f₁ y + f₂ (x - y) < c := by
  unfold infimalConv at h
  rw [sInf_lt_iff] at h
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := h
  exact ⟨y, hy⟩

lemma aux_add_le_decomp {A B : EReal} {r : ℝ} (hA : ⊥ < A) (hB : ⊥ < B)
    (h : A + B ≤ (r : EReal)) : ∃ a b : ℝ, A = a ∧ B = b ∧ a + b ≤ r := by
  induction A using EReal.rec with
  | bot => exact absurd hA (lt_irrefl _)
  | top =>
    rw [EReal.top_add_of_ne_bot hB.ne', top_le_iff] at h
    exact absurd h (EReal.coe_ne_top r)
  | coe a =>
    induction B using EReal.rec with
    | bot => exact absurd hB (lt_irrefl _)
    | top =>
      rw [EReal.coe_add_top, top_le_iff] at h
      exact absurd h (EReal.coe_ne_top r)
    | coe b =>
      refine ⟨a, b, rfl, rfl, ?_⟩
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
      exact h

lemma infConv_convex (g₁ g₂ : E → EReal) (x₁ x₂ : E) (hx₁ : g₁ x₁ < ⊤) (hx₂ : g₂ x₂ < ⊤) :
    Convex ℝ (epigraph (infimalConv (conjugate g₁) (conjugate g₂))) := by
  intro p hp q hq a b ha hb hab
  simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rw [← EReal.le_of_forall_lt_iff_le]
  intro c hc
  rw [EReal.coe_lt_coe_iff] at hc
  have hp' : infimalConv (conjugate g₁) (conjugate g₂) p.1 <
      ((p.2 + (c - (a * p.2 + b * q.2)) : ℝ) : EReal) :=
    lt_of_le_of_lt hp (EReal.coe_lt_coe_iff.mpr (by linarith))
  have hq' : infimalConv (conjugate g₁) (conjugate g₂) q.1 <
      ((q.2 + (c - (a * p.2 + b * q.2)) : ℝ) : EReal) :=
    lt_of_le_of_lt hq (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨y₁, hy₁⟩ := infConv_lt hp'
  obtain ⟨y₂, hy₂⟩ := infConv_lt hq'
  obtain ⟨c₁₁, c₁₂, e₁₁, e₁₂, hc₁⟩ :=
    aux_add_lt_decomp (conj_bot_lt g₁ x₁ hx₁ y₁) (conj_bot_lt g₂ x₂ hx₂ _) hy₁
  obtain ⟨c₂₁, c₂₂, e₂₁, e₂₂, hc₂⟩ :=
    aux_add_lt_decomp (conj_bot_lt g₁ x₁ hx₁ y₂) (conj_bot_lt g₂ x₂ hx₂ _) hy₂
  have k₁ : conjugate g₁ (a • y₁ + b • y₂) ≤ ((a * c₁₁ + b * c₂₁ : ℝ) : EReal) := by
    rw [conj_le_iff]
    exact affine_comb g₁ y₁ y₂ c₁₁ c₂₁ ((conj_le_iff _ _ _).mp e₁₁.le)
      ((conj_le_iff _ _ _).mp e₂₁.le) a b ha hb hab
  have k₂ : conjugate g₂ (a • (p.1 - y₁) + b • (q.1 - y₂)) ≤
      ((a * c₁₂ + b * c₂₂ : ℝ) : EReal) := by
    rw [conj_le_iff]
    exact affine_comb g₂ _ _ c₁₂ c₂₂ ((conj_le_iff _ _ _).mp e₁₂.le)
      ((conj_le_iff _ _ _).mp e₂₂.le) a b ha hb hab
  have hsplit : a • p.1 + b • q.1 - (a • y₁ + b • y₂) = a • (p.1 - y₁) + b • (q.1 - y₂) := by
    simp only [smul_sub]; abel
  calc infimalConv (conjugate g₁) (conjugate g₂) (a • p.1 + b • q.1)
      ≤ conjugate g₁ (a • y₁ + b • y₂) +
          conjugate g₂ (a • p.1 + b • q.1 - (a • y₁ + b • y₂)) := infConv_le _ _ _ _
    _ ≤ ((a * c₁₁ + b * c₂₁ : ℝ) : EReal) + ((a * c₁₂ + b * c₂₂ : ℝ) : EReal) := by
        rw [hsplit]; exact add_le_add k₁ k₂
    _ ≤ (c : EReal) := by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]
        have m1 := mul_le_mul_of_nonneg_left hc₁.le ha
        have m2 := mul_le_mul_of_nonneg_left hc₂.le hb
        have m3 : a * (c - (a * p.2 + b * q.2)) + b * (c - (a * p.2 + b * q.2)) =
            c - (a * p.2 + b * q.2) := by rw [← add_mul, hab, one_mul]
        rw [mul_add, mul_add] at m1 m2
        linarith

lemma infConv_minorant (g₁ g₂ : E → EReal) (x : E) (c : ℝ) (hc : g₁ x + g₂ x ≤ (c : EReal))
    (h1 : ⊥ < g₁ x) (h2 : ⊥ < g₂ x) :
    ∀ t, (((inner ℝ x t - c : ℝ)) : EReal) ≤ infimalConv (conjugate g₁) (conjugate g₂) t := by
  intro t
  obtain ⟨c₁, c₂, e₁, e₂, hc₁₂⟩ := aux_add_le_decomp h1 h2 hc
  unfold infimalConv
  apply le_sInf
  rintro _ ⟨y, rfl⟩
  calc (((inner ℝ x t - c : ℝ)) : EReal)
      ≤ (((inner ℝ y x - c₁ : ℝ)) : EReal) + (((inner ℝ (t - y) x - c₂ : ℝ)) : EReal) := by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_left, real_inner_comm x t]
        linarith
    _ ≤ conjugate g₁ y + conjugate g₂ (t - y) :=
        add_le_add (le_conj_of_le _ _ _ _ e₁.le) (le_conj_of_le _ _ _ _ e₂.le)

lemma conj_le_of (g : E → EReal) (y : E) (w : EReal)
    (H : ∀ x, ((inner ℝ y x : ℝ) : EReal) - g x ≤ w) : conjugate g y ≤ w := by
  unfold conjugate
  apply sSup_le
  rintro _ ⟨x, -, rfl⟩
  exact H x

lemma dir1 (g₁ g₂ : E → EReal) (h1 : ∀ x, ⊥ < g₁ x) (h2 : ∀ x, ⊥ < g₂ x) (s : E) :
    conjugate (g₁ + g₂) s ≤ lscHull (infimalConv (conjugate g₁) (conjugate g₂)) s := by
  unfold lscHull
  apply conj_le_of
  intro x
  apply aux_sub_le_of_forall
  intro c hc
  have hmin := infConv_minorant g₁ g₂ x c hc (h1 x) (h2 x)
  have hcont : Continuous (fun t => (((inner ℝ x t - c : ℝ)) : EReal)) := by
    apply continuous_coe_real_ereal.comp
    exact (continuous_const.inner continuous_id).sub continuous_const
  have htend := hcont.tendsto s
  calc (((inner ℝ s x - c : ℝ)) : EReal) = (((inner ℝ x s - c : ℝ)) : EReal) := by
        rw [real_inner_comm]
    _ = Filter.liminf (fun t => (((inner ℝ x t - c : ℝ)) : EReal)) (𝓝 s) :=
        htend.liminf_eq.symm
    _ ≤ Filter.liminf (infimalConv (conjugate g₁) (conjugate g₂)) (𝓝 s) :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hmin)

theorem FCA_chap_E_2_3_1
  (g₁ g₂ : E → EReal)
  (hg_closed_convex : InClosedConvRn g₁ ∧ InClosedConvRn g₂)
  (h_dom_nonempty : Set.Nonempty (effDom g₁ ∩
    effDom g₂))
  (g₁_ne_bot : ∀ x, ⊥ < g₁ x)
  (g₂_ne_bot : ∀ x, ⊥ < g₂ x) :
  ∀ s, (conjugate (g₁ + g₂) s) =
  (lscHull (infimalConv (conjugate g₁) (conjugate g₂)) s) := by
  obtain ⟨hg₁, hg₂⟩ := hg_closed_convex
  obtain ⟨x₀, hx₀₁, hx₀₂⟩ := h_dom_nonempty
  have hx₀₁' : g₁ x₀ < ⊤ := hx₀₁
  have hx₀₂' : g₂ x₀ < ⊤ := hx₀₂
  intro s
  apply le_antisymm (dir1 g₁ g₂ g₁_ne_bot g₂_ne_bot s)
  by_contra hcon
  push_neg at hcon
  obtain ⟨α, hα1, hα2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  obtain ⟨α', hα'1, hα'2⟩ := EReal.lt_iff_exists_real_btwn.mp hα2
  unfold lscHull at hα'2
  have hev : ∀ᶠ t in 𝓝 s, ((α' : ℝ) : EReal) < infimalConv (conjugate g₁) (conjugate g₂) t :=
    Filter.eventually_lt_of_lt_liminf hα'2
  have hnot := not_mem_closure_epi _ s α α' (EReal.coe_lt_coe_iff.mp hα'1) hev
  have hconv := infConv_convex g₁ g₂ x₀ x₀ hx₀₁' hx₀₂'
  obtain ⟨c₁, e₁⟩ : ∃ c₁ : ℝ, g₁ x₀ = c₁ :=
    ⟨(g₁ x₀).toReal, (EReal.coe_toReal hx₀₁'.ne (g₁_ne_bot x₀).ne').symm⟩
  obtain ⟨c₂, e₂⟩ : ∃ c₂ : ℝ, g₂ x₀ = c₂ :=
    ⟨(g₂ x₀).toReal, (EReal.coe_toReal hx₀₂'.ne (g₂_ne_bot x₀).ne').symm⟩
  have h₀ := infConv_minorant g₁ g₂ x₀ (c₁ + c₂) (by rw [e₁, e₂, EReal.coe_add])
    (g₁_ne_bot x₀) (g₂_ne_bot x₀)
  obtain ⟨x, β, hxβ, hαβ⟩ := separation' _ hconv s α hnot x₀ (c₁ + c₂) h₀
  have key : g₁ x + g₂ x ≤ (β : EReal) := by
    by_contra hk
    push_neg at hk
    obtain ⟨a₁, a₂, ha₁, ha₂, ha⟩ := aux_lt_add_decomp (g₁_ne_bot x) (g₂_ne_bot x) hk
    obtain ⟨y₁, b₁, hy₁, hab₁⟩ := fm g₁ hg₁ x a₁ ha₁
    obtain ⟨y₂, b₂, hy₂, hab₂⟩ := fm g₂ hg₂ x a₂ ha₂
    have k₁ : conjugate g₁ y₁ ≤ (b₁ : EReal) := (conj_le_iff _ _ _).mpr hy₁
    have k₂ : conjugate g₂ y₂ ≤ (b₂ : EReal) := (conj_le_iff _ _ _).mpr hy₂
    have k₃ : infimalConv (conjugate g₁) (conjugate g₂) (y₁ + y₂) ≤
        conjugate g₁ y₁ + conjugate g₂ y₂ := by
      have := infConv_le (conjugate g₁) (conjugate g₂) (y₁ + y₂) y₁
      rwa [add_sub_cancel_left] at this
    have k₄ := (hxβ (y₁ + y₂)).trans (k₃.trans (add_le_add k₁ k₂))
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, inner_add_right] at k₄
    rw [real_inner_comm] at hab₁ hab₂
    linarith
  have h5 : (((inner ℝ s x - β : ℝ)) : EReal) ≤ conjugate (g₁ + g₂) s :=
    le_conj_of_le (g₁ + g₂) s x β key
  rw [real_inner_comm] at h5
  have h6 : (α : EReal) < conjugate (g₁ + g₂) s :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hαβ) h5
  exact absurd hα1 (not_lt.mpr h6.le)

end FCA_chap_E_2_3_1
