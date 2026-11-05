import Mathlib

def strongPow {α : Type*} (G : SimpleGraph α) (k : ℕ) :
    SimpleGraph (Fin k → α) where
  Adj x y := x ≠ y ∧ ∀ i, G.Adj (x i) (y i) ∨ x i = y i
  symm x y := by
    rintro ⟨hne, h⟩
    exact ⟨hne.symm, fun i => (h i).imp (fun h => h.symm) Eq.symm⟩
  loopless := by
    constructor
    intro a h
    grind

noncomputable def shannonCapacity {α : Type*} (G : SimpleGraph α) : ℝ :=
  sSup {r : ℝ | ∃ k : ℕ, 1 ≤ k ∧ r = ((strongPow G k).indepNum : ℝ) ^ ((1 : ℝ) / k)}

def shannon_capacity_c7 : Prop :=
  shannonCapacity (SimpleGraph.cycleGraph 7)
      = 7 * Real.cos (Real.pi / 7) / (1 + Real.cos (Real.pi / 7))

theorem shannon_capacity_c7_POS : shannon_capacity_c7 := by
  sorry

theorem shannon_capacity_c7_NEG : ¬ shannon_capacity_c7 := by
  sorry
