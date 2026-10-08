import Solutions.Sol_DiagRamsey_diagonal_le_three_point_five_pow
import SharpBound

open DiagRamsey in
example : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (ramseyNumber k k : ℝ) ≤ (7 / 2 : ℝ) ^ k :=
  DiagRamsey.diagonal_le_three_point_five_pow

/-- info: 'DiagRamsey.diagonal_le_three_point_five_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DiagRamsey.diagonal_le_three_point_five_pow

/-- info: 'DiagRamsey.diagonal_le_3p4986238_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DiagRamsey.diagonal_le_3p4986238_pow

/-- info: 'DiagRamsey.diagonal_le_exp_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DiagRamsey.diagonal_le_exp_z
