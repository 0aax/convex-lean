import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_4_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_4_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_4_5`, so the main result is `FCA_chap_B_2_4_5.FCA_chap_B_2_4_5`.
-/

namespace FCA_chap_B_2_4_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_2_4_5
  {n m : ℕ}
  (g : EuclideanSpace ℝ (Fin (n + m)) → EReal)
  (hg_convex : InConvRn g)
  (hg_bounded : ∀ (x : EuclideanSpace ℝ (Fin n)), marginalFun g x > ⊥) :
  InConvRn (marginalFun g) := by
  obtain ⟨hbot, ⟨x0, hx0⟩, hconv⟩ := hg_convex
  set app : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin (n + m)) :=
    fun a b => (WithLp.equiv 2 _).symm (Fin.append (α := ℝ) a.ofLp b.ofLp) with happ
  have hmf : ∀ x, marginalFun g x = sInf (Set.range (fun y => g (app x y))) := fun x => rfl
  have hle : ∀ x y, marginalFun g x ≤ g (app x y) := fun x y => by
    rw [hmf]; exact sInf_le ⟨y, rfl⟩
  have hlin : ∀ (a b : ℝ) x1 x2 y1 y2,
      app (a • x1 + b • x2) (a • y1 + b • y2) = a • app x1 y1 + b • app x2 y2 := by
    intro a b x1 x2 y1 y2
    ext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [happ]
    · simp [happ]
  refine ⟨hg_bounded, ?_, ?_⟩
  · refine ⟨(WithLp.equiv 2 _).symm (fun i => x0 (Fin.castAdd m i)),
      lt_of_le_of_lt (hle _ ((WithLp.equiv 2 _).symm (fun j => x0 (Fin.natAdd n j)))) ?_⟩
    convert hx0
    ext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [happ]
    · simp [happ]
  · intro p hp q hq a b ha hb hab
    simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
    obtain ⟨x1, r1⟩ := p
    obtain ⟨x2, r2⟩ := q
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hp hq ⊢
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : a * r1 + b * r2 < z := by exact_mod_cast hz
    set ε := z - (a * r1 + b * r2) with hε
    have hεpos : 0 < ε := by linarith
    have h1 : marginalFun g x1 < ((r1 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hp (by exact_mod_cast (by linarith : r1 < r1 + ε))
    have h2 : marginalFun g x2 < ((r2 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hq (by exact_mod_cast (by linarith : r2 < r2 + ε))
    rw [hmf, sInf_lt_iff] at h1 h2
    obtain ⟨_, ⟨y1, rfl⟩, hy1⟩ := h1
    obtain ⟨_, ⟨y2, rfl⟩, hy2⟩ := h2
    have hm1 : (app x1 y1, r1 + ε) ∈ epigraph g := le_of_lt hy1
    have hm2 : (app x2 y2, r2 + ε) ∈ epigraph g := le_of_lt hy2
    have hc := hconv hm1 hm2 ha hb hab
    simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hc
    calc marginalFun g (a • x1 + b • x2)
        ≤ g (app (a • x1 + b • x2) (a • y1 + b • y2)) := hle _ _
      _ = g (a • app x1 y1 + b • app x2 y2) := by rw [hlin]
      _ ≤ ((a * (r1 + ε) + b * (r2 + ε) : ℝ) : EReal) := hc
      _ = (z : EReal) := by
        congr 1
        have : a * (r1 + ε) + b * (r2 + ε) = a * r1 + b * r2 + (a + b) * ε := by ring
        rw [this, hab, hε]; ring

end FCA_chap_B_2_4_5
