import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_DiagRamsey_Basic

namespace DiagRamsey

theorem diagonal_le_three_point_five_pow :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (ramseyNumber k k : ℝ) ≤ (7 / 2 : ℝ) ^ k := by sorry

end DiagRamsey
