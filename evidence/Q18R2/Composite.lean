import Solutions.Sol_DiagRamsey_diagonal_le_three_point_five_pow
    open DiagRamsey in
    example: ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (ramseyNumber k k : ℝ) ≤ (7 / 2 : ℝ) ^ k := by
      apply DiagRamsey.diagonal_le_three_point_five_pow <;> assumption
    #print axioms DiagRamsey.diagonal_le_three_point_five_pow
    