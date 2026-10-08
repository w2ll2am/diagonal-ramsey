import Lemmas.DiagRamsey_JB_Transfer
import Lemmas.DiagRamsey_SB_Bank
import Lemmas.DiagRamsey_diagonal_wrapper

/-!
# Joint banks: the diagonal corollary

`statements/DiagRamsey_joint_integer_target_bank.md`, Corollary (diagonal): two profiles `R, S` whose assertions
hold with one constant, with `1 ∈ I_R ∩ I_S` and `p_R + p_S ≤ 1`, give `R(k, k) ≤ e^{z k}` for all large `k`
whenever `z > max (L_R 1) (L_S 1)`. This is the `complementary_raw` / `complementary_ratio_monotone` piece at `r = 1`
applied to the RAW donors themselves, which needs no density hypothesis on the host.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

lemma redEdgeDensity_add_compl {N : ℕ} (G : SimpleGraph (Fin N)) (hN : 2 ≤ N) :
    redEdgeDensity G + redEdgeDensity Gᶜ = 1 := by
  have h := redPairs_add_compl G Finset.univ
  rw [redPairs_univ_eq, redPairs_univ_eq, Finset.card_univ, Fintype.card_fin] at h
  unfold redEdgeDensity
  rw [Nat.cast_choose_two, ← add_div, div_eq_one_iff_eq]
  · linarith
  · have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 1) := by nlinarith
    linarith

theorem joint_diagonal {C : ℝ} (hC : 1 ≤ C) (R S : BankProfile) (hR : R.Assert C) (hS : S.Assert C)
    (hRv : R.Valid) (hSv : S.Valid) (hR1 : R.lo ≤ 1) (hR2 : 1 ≤ R.hi) (hS1 : S.lo ≤ 1) (hS2 : 1 ≤ S.hi)
    (hp : R.p + S.p ≤ 1) (z : ℝ) (hz : max (R.L 1) (S.L 1) < z) :
    ∀ᶠ k : ℕ in Filter.atTop, (ramseyNumber k k : ℝ) ≤ Real.exp (z * k) := by
  set L := max (R.L 1) (S.L 1) with hL
  have hL0 : 0 < L := lt_of_lt_of_le (hRv.2.2.2.2 1 hR1 hR2) (le_max_left _ _)
  have hC0 : 0 < C := by linarith
  obtain ⟨K, hK⟩ := exists_nat_ge (Real.log 2 / L + 1)
  refine eventually_ramsey_le_of_arrows L z C hz hL0.le hC0 K (fun k hk N hN G => ?_)
  have hkpos : (1 : ℝ) ≤ k := by
    have : (1 : ℝ) ≤ K := by
      have := div_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hL0.le
      have : (1 : ℝ) ≤ K := by linarith
      exact this
    exact this.trans (by exact_mod_cast hk)
  have hk0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have hkk : ((k : ℕ) : ℝ) / k = 1 := div_self (by positivity)
  -- N ≥ 2
  have hN2 : 2 ≤ N := by
    have h1 : Real.log 2 ≤ L * k := by
      have : Real.log 2 / L ≤ k := by linarith [show (K : ℝ) ≤ k by exact_mod_cast hk]
      rwa [div_le_iff₀ hL0, mul_comm] at this
    have h2 : (2 : ℝ) ≤ Real.exp (L * k) := by
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (L * k) := Real.exp_le_exp.mpr h1
    have h3 : Real.exp (L * k) ≤ C * Real.exp (L * k) := le_mul_of_one_le_left (Real.exp_pos _).le hC
    exact_mod_cast (show (2 : ℝ) ≤ N by linarith)
  have hsz : ∀ (P : BankProfile), P.L 1 ≤ L → C * Real.exp (k * P.L (((k : ℕ) : ℝ) / k)) ≤ (N : ℝ) := by
    intro P hP
    rw [hkk]
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0.le) hN
    rw [mul_comm (L : ℝ)]
    exact mul_le_mul_of_nonneg_left hP (by positivity)
  by_cases hd : R.p ≤ redEdgeDensity G
  · exact hR k k hk0 hk0 (by rw [hkk]; exact hR1) (by rw [hkk]; exact hR2) N G hd (hsz R (le_max_left _ _))
  · push_neg at hd
    have hdc : S.p ≤ redEdgeDensity Gᶜ := by
      have := redEdgeDensity_add_compl G hN2
      linarith
    rcases hS k k hk0 hk0 (by rw [hkk]; exact hS1) (by rw [hkk]; exact hS2) N Gᶜ hdc
      (hsz S (le_max_right _ _)) with ⟨T, hT⟩ | ⟨T, hT⟩
    · exact Or.inr ⟨T, hT⟩
    · rw [compl_compl] at hT; exact Or.inl ⟨T, hT⟩

end DiagRamsey
