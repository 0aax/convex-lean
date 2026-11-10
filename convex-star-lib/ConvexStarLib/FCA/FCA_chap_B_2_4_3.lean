import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_4_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_4_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_4_3`, so the main result is `FCA_chap_B_2_4_3.FCA_chap_B_2_4_3`.
-/

namespace FCA_chap_B_2_4_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
theorem FCA_chap_B_2_4_3
  {p n : ℕ}
  (phi : EuclideanSpace ℝ (Fin p) → EReal)
  (c : (Fin n) → (EuclideanSpace ℝ (Fin p) → EReal))
  (h_phi_convex : InConvRn phi)
  (hc_convex : ∀ j, InConvRn (c j))
  (h_nonempty_dom : Set.Nonempty (effDom phi ∩ (⋂ j, effDom (c j))))
  (h_noninf_val : ∀ x, (valueFun phi c x) > ⊥) :
  InConvRn (valueFun phi c) := by
  refine ⟨fun x => h_noninf_val x, ?_, ?_⟩
  · -- the value function is finite somewhere
    obtain ⟨u0, hu0phi, hu0c⟩ := h_nonempty_dom
    simp only [Set.mem_iInter, effDom, Set.mem_setOf_eq] at hu0c hu0phi
    refine ⟨WithLp.toLp 2 (fun j => (c j u0).toReal), ?_⟩
    calc valueFun phi c (WithLp.toLp 2 (fun j => (c j u0).toReal)) ≤ phi u0 := by
          apply sInf_le
          refine ⟨u0, ?_, rfl⟩
          intro j
          rw [PiLp.toLp_apply]
          exact EReal.le_coe_toReal (hu0c j).ne
      _ < ⊤ := hu0phi
  · -- convexity of the epigraph
    intro P hP Q hQ a b ha hb hab
    obtain ⟨x1, t1⟩ := P
    obtain ⟨x2, t2⟩ := Q
    simp only [epigraph, Set.mem_setOf_eq] at hP hQ ⊢
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    rw [EReal.coe_lt_coe_iff] at hz
    set ε := z - (a * t1 + b * t2) with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    -- approximate minimizers
    have hlt1 : valueFun phi c x1 < ((t1 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hP (EReal.coe_lt_coe_iff.mpr (by linarith))
    have hlt2 : valueFun phi c x2 < ((t2 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hQ (EReal.coe_lt_coe_iff.mpr (by linarith))
    obtain ⟨y1, ⟨u1, hu1, rfl⟩, hy1⟩ := sInf_lt_iff.mp hlt1
    obtain ⟨y2, ⟨u2, hu2, rfl⟩, hy2⟩ := sInf_lt_iff.mp hlt2
    have hfeas : ∀ j, c j (a • u1 + b • u2) ≤ ((a • x1 + b • x2) j : EReal) := by
      intro j
      have h1 : (u1, x1 j) ∈ epigraph (c j) := hu1 j
      have h2 : (u2, x2 j) ∈ epigraph (c j) := hu2 j
      have h := (hc_convex j).2.2 h1 h2 ha hb hab
      simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h
      simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using h
    have hphi : phi (a • u1 + b • u2) ≤ ((a * (t1 + ε) + b * (t2 + ε) : ℝ) : EReal) := by
      have h1 : (u1, t1 + ε) ∈ epigraph phi := hy1.le
      have h2 : (u2, t2 + ε) ∈ epigraph phi := hy2.le
      have h := h_phi_convex.2.2 h1 h2 ha hb hab
      simpa only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using h
    have heq : a * (t1 + ε) + b * (t2 + ε) = z := by
      rw [hε]; linear_combination (z - (a * t1 + b * t2)) * hab
    calc valueFun phi c (a • x1 + b • x2) ≤ phi (a • u1 + b • u2) :=
          sInf_le ⟨a • u1 + b • u2, hfeas, rfl⟩
      _ ≤ ((a * (t1 + ε) + b * (t2 + ε) : ℝ) : EReal) := hphi
      _ = (z : EReal) := by rw [heq]

end FCA_chap_B_2_4_3
