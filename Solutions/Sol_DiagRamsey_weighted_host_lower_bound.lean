import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DiagRamsey

theorem weighted_host_lower_bound (N a b : ℕ) (w : ℝ) (hw : 0 ≤ w) (ha : N ≤ 3 * a) (hb : N ≤ 3 * b) :
    ((N : ℝ) / 3) ^ (w + 1) ≤ (a : ℝ) ^ w * (b : ℝ) := by
  have h0 : (0 : ℝ) ≤ (N : ℝ) / 3 := by positivity
  have haR : (N : ℝ) / 3 ≤ (a : ℝ) := by
    have : (N : ℝ) ≤ 3 * (a : ℝ) := by exact_mod_cast ha
    linarith
  have hbR : (N : ℝ) / 3 ≤ (b : ℝ) := by
    have : (N : ℝ) ≤ 3 * (b : ℝ) := by exact_mod_cast hb
    linarith
  rw [Real.rpow_add' h0 (by linarith), Real.rpow_one]
  exact mul_le_mul (Real.rpow_le_rpow h0 haR hw) hbR h0 (Real.rpow_nonneg (Nat.cast_nonneg a) w)

end DiagRamsey

theorem solution_weighted_host_lower_bound (N a b : ℕ) (w : ℝ) (hw : 0 ≤ w) (ha : N ≤ 3 * a) (hb : N ≤ 3 * b) :
    ((N : ℝ) / 3) ^ (w + 1) ≤ (a : ℝ) ^ w * (b : ℝ) :=
  DiagRamsey.weighted_host_lower_bound N a b w hw ha hb
