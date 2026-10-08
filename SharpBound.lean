import Solutions.P06.P0r12.Final

/-! Sharp form of Q18R2: `R(k,k) ≤ e^{zk}` eventually, z = 626184844701/500000000000 (e^z ≈ 3.4986238), and the
corollaries `R(k,k) ≤ 3.4987^k` and `R(k,k) ≤ 3.4986238^k`. Compiled against the port build `lean-luwang/.lake/portfullp0_P0r12/build`. -/

set_option maxRecDepth 100000

namespace DiagRamsey

open DiagRamsey.SharpCert

theorem diagonal_le_exp_z :
    ∀ᶠ k : ℕ in Filter.atTop, (ramseyNumber k k : ℝ) ≤ Real.exp ((626184844701 / 500000000000 : ℝ) * k) := by
  have hq : ((V5.FQ.mk (.ofNat (nat_lit 626184844701)) (nat_lit 499999999999)).toQ : ℚ)
      = 626184844701 / 500000000000 := by decide +kernel
  have h := V5.P06_P0r12.bank_diagonal V5.P06_P0r12.certs lu_wang_lines_P0r12
  rw [hq] at h
  push_cast at h
  exact h

theorem diagonal_le_3p4987_pow :
    ∃ K : ℕ, ∀ k ≥ K, (ramseyNumber k k : ℝ) ≤ (34987 / 10000 : ℝ) ^ k := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 diagonal_le_exp_z
  refine ⟨K, fun k hk => (hK k hk).trans ?_⟩
  have hb : expLeB (626184844701 / 500000000000 : ℚ) (34987 / 10000) = true := by decide +kernel
  have he : Real.exp (626184844701 / 500000000000 : ℝ) ≤ 34987 / 10000 := by
    have := exp_le_of_expLeB hb
    push_cast at this
    linarith
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he k

/-- The tightest 7-digit base for this certificate: e^z = 3.49862379380751… ≤ 3.4986238. -/
theorem diagonal_le_3p4986238_pow :
    ∃ K : ℕ, ∀ k ≥ K, (ramseyNumber k k : ℝ) ≤ (34986238 / 10000000 : ℝ) ^ k := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 diagonal_le_exp_z
  refine ⟨K, fun k hk => (hK k hk).trans ?_⟩
  have hb : expLeB (626184844701 / 500000000000 : ℚ) (34986238 / 10000000) = true := by decide +kernel
  have he : Real.exp (626184844701 / 500000000000 : ℝ) ≤ 34986238 / 10000000 := by
    have := exp_le_of_expLeB hb
    push_cast at this
    linarith
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he k

end DiagRamsey

#print axioms DiagRamsey.diagonal_le_exp_z
#print axioms DiagRamsey.diagonal_le_3p4987_pow
#print axioms DiagRamsey.diagonal_le_3p4986238_pow
