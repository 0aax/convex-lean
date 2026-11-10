import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_3_2_i`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_3_2_i` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_3_2_i`, so the main result is `FCA_chap_C_3_3_2_i.FCA_chap_C_3_3_2_i`.
-/

namespace FCA_chap_C_3_3_2_i

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_3_3_2_i
  (S₁ S₂ : Set E)
  (t₁ t₂ : ℝ)
  (hS_nonempty : Set.Nonempty S₁ ∧ Set.Nonempty S₂)
  (hS_closed : IsClosed S₁ ∧ IsClosed S₂)
  (hS_convex : Convex ℝ S₁ ∧ Convex ℝ S₂)
  (ht : t₁ > 0 ∧ t₂ > 0) :
  let σ₁ := supportFunction S₁
  let σ₂ := supportFunction S₂
  let S₁' := {x | ∃ s ∈ S₁, x = t₁ • s}
  let S₂' := {x | ∃ s ∈ S₂, x = t₂ • s}
  let S := closure {x | ∃ s₁ ∈ S₁', ∃ s₂ ∈ S₂', x = s₁ + s₂}
  ∀ x, (t₁ * (σ₁ x) + t₂ * (σ₂ x)) = (supportFunction S x) := by
  intro σ₁ σ₂ S₁' S₂' S x
  -- the support function is unchanged by taking the closure
  have hcl : ∀ A : Set E, supportFunction (closure A) x = supportFunction A x := by
    intro A
    unfold supportFunction
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨v, hv, rfl⟩
      have hclosed : IsClosed {v : E | ((inner ℝ v x : ℝ) : EReal) ≤
          sSup ((fun v : E => ((inner ℝ v x : ℝ) : EReal)) '' A)} :=
        isClosed_le (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const))
          continuous_const
      have hsub : A ⊆ {v : E | ((inner ℝ v x : ℝ) : EReal) ≤
          sSup ((fun v : E => ((inner ℝ v x : ℝ) : EReal)) '' A)} := by
        intro v hv
        rw [Set.mem_setOf_eq]
        exact le_sSup (Set.mem_image_of_mem _ hv)
      exact closure_minimal hsub hclosed hv
    · exact sSup_le_sSup (Set.image_mono subset_closure)
  -- the support function of a Minkowski sum is the sum of the support functions
  have hadd : ∀ A B : Set E, supportFunction {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b} x =
      supportFunction A x + supportFunction B x := by
    intro A B
    unfold supportFunction
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨v, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      dsimp only
      rw [inner_add_left, EReal.coe_add]
      exact add_le_add (le_sSup (Set.mem_image_of_mem _ ha)) (le_sSup (Set.mem_image_of_mem _ hb))
    · apply EReal.add_le_of_forall_lt
      intro a' ha' b' hb'
      obtain ⟨_, ⟨a, ha, rfl⟩, ha''⟩ := lt_sSup_iff.mp ha'
      obtain ⟨_, ⟨b, hb, rfl⟩, hb''⟩ := lt_sSup_iff.mp hb'
      have hab : a + b ∈ {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b} := ⟨a, ha, b, hb, rfl⟩
      refine le_trans ?_ (le_sSup (Set.mem_image_of_mem _ hab))
      dsimp only at ha'' hb'' ⊢
      rw [inner_add_left, EReal.coe_add]
      exact add_le_add ha''.le hb''.le
  -- positive scalars pull out of the support function
  have hsmul : ∀ (A : Set E) (t : ℝ), 0 < t →
      supportFunction {x | ∃ s ∈ A, x = t • s} x = (t : EReal) * supportFunction A x := by
    intro A t ht
    unfold supportFunction
    have ht' : (0 : EReal) < t := by exact_mod_cast ht
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨v, ⟨s, hs, rfl⟩, rfl⟩
      dsimp only
      rw [real_inner_smul_left, EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left (le_sSup (Set.mem_image_of_mem _ hs)) ht'.le
    · rw [mul_comm, ← EReal.le_div_iff_mul_le ht' (EReal.coe_ne_top t)]
      apply sSup_le
      rintro _ ⟨s, hs, rfl⟩
      have hts : t • s ∈ {x | ∃ s ∈ A, x = t • s} := ⟨s, hs, rfl⟩
      dsimp only
      rw [EReal.le_div_iff_mul_le ht' (EReal.coe_ne_top t), ← EReal.coe_mul, mul_comm,
        ← real_inner_smul_left]
      exact le_sSup (Set.mem_image_of_mem (fun v : E => ((inner ℝ v x : ℝ) : EReal)) hts)
  show (t₁ : EReal) * supportFunction S₁ x + (t₂ : EReal) * supportFunction S₂ x =
    supportFunction (closure {x | ∃ s₁ ∈ S₁', ∃ s₂ ∈ S₂', x = s₁ + s₂}) x
  rw [hcl, hadd, hsmul S₁ t₁ ht.1, hsmul S₂ t₂ ht.2]

end FCA_chap_C_3_3_2_i
