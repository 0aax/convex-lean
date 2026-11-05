import Mathlib

def Matrix.CompletelyPositive {n : Type*} [Fintype n]
  (A : Matrix n n ℝ) : Prop :=
  ∃ (r : ℕ) (B : Matrix n (Fin r) ℝ),
    (∀ i j, 0 ≤ B i j) ∧
    (A = B * B.transpose)

def order_six_djl : Prop :=
  ∀ (A : Matrix (Fin 6) (Fin 6) ℝ),
    (A.CompletelyPositive) →
      ∃ (C : Matrix (Fin 6) (Fin 9) ℝ),
        (∀ i j, 0 ≤ C i j) ∧
        (A = C * C.transpose)

theorem order_six_djl_POS : order_six_djl := by
  sorry

theorem order_six_djl_NEG : ¬ order_six_djl := by
  sorry
