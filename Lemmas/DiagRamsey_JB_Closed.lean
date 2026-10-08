import Lemmas.DiagRamsey_JB_Raw

/-!
# Joint banks: CLOSED pieces on the same host (Lemma 3 of the NL proof)

Given every RAW assertion on the whole host `V` for every graph on `V` (both colour namings), each CLOSED piece
gives its profile's assertion on `V` at every integer pair `(k, b)` with `b/k ∈ J ∩ I_Q`, once
`k ≥ ⌈1/(c' - c)⌉` for the ratio-monotone kinds.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

section
variable {nR : ℕ} {V : Type} [Fintype V] [DecidableEq V]

lemma hasBlue_le {G : SimpleGraph V} {W : Finset V} {b b' : ℕ} (h : HasBlueClique G W b') (hb : b ≤ b') :
    HasBlueClique G W b := by
  obtain ⟨S, hS, hc⟩ := h
  obtain ⟨T, hT, hTc⟩ := ClosureEnv.isNClique_sub hc hb
  exact ⟨T, hT.trans hS, hTc⟩

lemma hasRed_le {G : SimpleGraph V} {W : Finset V} {b b' : ℕ} (h : HasRedClique G W b') (hb : b ≤ b') :
    HasRedClique G W b := by
  obtain ⟨S, hS, hc⟩ := h
  obtain ⟨T, hT, hTc⟩ := ClosureEnv.isNClique_sub hc hb
  exact ⟨T, hT.trans hS, hTc⟩

/-- The ratio-monotone threshold. -/
noncomputable def kRM : ClosedPiece nR → ℕ
  | .rawDensity _ => 0
  | .complRaw _ _ => 0
  | .ratioMono _ c c' => ⌈1 / (c' - c)⌉₊
  | .complRatioMono _ _ c c' => ⌈1 / (c' - c)⌉₊

/-- The rounded-up target `b' = ⌈c k⌉`: `b'/k ∈ [c, c']` and `b ≤ b'`. -/
lemma ceil_target {c c' hi : ℝ} {k b : ℕ} (hk0 : 0 < k) (hcc : c < c') (hk : ⌈1 / (c' - c)⌉₊ ≤ k)
    (hhic : hi ≤ c) (hb : (b : ℝ) / k ≤ hi) (hc0 : 0 < c) :
    0 < ⌈c * k⌉₊ ∧ c ≤ (⌈c * k⌉₊ : ℝ) / k ∧ (⌈c * k⌉₊ : ℝ) / k ≤ c' ∧ b ≤ ⌈c * k⌉₊ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have h1 : c * k ≤ (⌈c * k⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈c * k⌉₊ : ℝ) < c * k + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk' : 1 / (c' - c) ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hk'' : 1 ≤ (c' - c) * k := by
    rw [div_le_iff₀ (by linarith)] at hk'; linarith
  refine ⟨Nat.ceil_pos.mpr (by positivity), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hkpos]; exact h1
  · rw [div_le_iff₀ hkpos]; nlinarith
  · have : (b : ℝ) ≤ c * k := by
      rw [div_le_iff₀ hkpos] at hb; nlinarith
    exact_mod_cast this.trans h1

/-- Density split for a complementary pair: red density `≥ p` or blue density `≥ q` when `p + q ≤ 1`. -/
lemma density_split (G : SimpleGraph V) (W : Finset V) {p q : ℝ} (hpq : p + q ≤ 1)
    (hW : 0 ≤ (W.card : ℝ) * ((W.card : ℝ) - 1))
    (h : ¬ p * ((W.card : ℝ) * ((W.card : ℝ) - 1)) ≤ (redPairs G W : ℝ)) :
    q * ((W.card : ℝ) * ((W.card : ℝ) - 1)) ≤ (redPairs Gᶜ W : ℝ) := by
  push_neg at h
  have := redPairs_add_compl G W
  nlinarith

lemma natsq_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith

lemma closed_piece_ok (raw : Fin nR → BankProfile) (hraw : ∀ i, (raw i).Valid) (Q : BankProfile)
    (lo hi : ℝ) (pc : ClosedPiece nR) (hpc : pc.Valid raw Q lo hi) (C : ℝ) (hC : 1 ≤ C)
    (hRAW : ∀ (G' : SimpleGraph V) (i : Fin nR), AssertOn (raw i) C G' Finset.univ)
    (G : SimpleGraph V) (k b : ℕ) (hk : kRM pc ≤ k) (hk0 : 0 < k) (hb0 : 0 < b)
    (h1 : lo ≤ (b : ℝ) / k) (h2 : (b : ℝ) / k ≤ hi)
    (hd : Q.p * (((Finset.univ : Finset V).card : ℝ) * (((Finset.univ : Finset V).card : ℝ) - 1)) ≤
      (redPairs G Finset.univ : ℝ))
    (hs : C * Real.exp (k * Q.L ((b : ℝ) / k)) ≤ ((Finset.univ : Finset V).card : ℝ)) :
    HasRedClique G Finset.univ k ∨ HasBlueClique G Finset.univ b := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
  have hC0 : 0 ≤ C := by linarith
  have hnn := natsq_nonneg (Finset.univ : Finset V).card
  have hsize : ∀ x : ℝ, x ≤ k * Q.L ((b : ℝ) / k) → C * Real.exp x ≤ ((Finset.univ : Finset V).card : ℝ) :=
    fun x hx => le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) hC0) hs
  have hkb : (k : ℝ) / b = 1 / ((b : ℝ) / k) := by field_simp
  rcases pc with R | ⟨R, S⟩ | ⟨R, c, c'⟩ | ⟨R, S, c, c'⟩
  · -- raw_density
    obtain ⟨hp, hlo, hhi, hL⟩ := hpc
    exact hRAW G R k b hk0 hb0 (hlo.trans h1) (h2.trans hhi)
      (le_trans (mul_le_mul_of_nonneg_right hp hnn) hd)
      (hsize _ (mul_le_mul_of_nonneg_left (hL _ h1 h2) hkpos.le))
  · -- complementary_raw
    obtain ⟨hpsum, hlo, hhi, hLS⟩ := hpc
    obtain ⟨hSlo, hShi, hmax⟩ := hLS _ h1 h2
    by_cases hred : (raw R).p * (((Finset.univ : Finset V).card : ℝ) *
        (((Finset.univ : Finset V).card : ℝ) - 1)) ≤ (redPairs G Finset.univ : ℝ)
    · exact hRAW G R k b hk0 hb0 (hlo.trans h1) (h2.trans hhi) hred
        (hsize _ (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hmax) hkpos.le))
    · have hblue := density_split G Finset.univ hpsum hnn hred
      have hres := hRAW Gᶜ S b k hb0 hk0 (by rw [hkb]; exact hSlo) (by rw [hkb]; exact hShi) hblue
        (hsize _ (by
          rw [hkb]
          have e : (b : ℝ) * (raw S).L (1 / ((b : ℝ) / k)) =
              k * ((b : ℝ) / k * (raw S).L (1 / ((b : ℝ) / k))) := by field_simp
          rw [e]
          exact mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hmax) hkpos.le))
      rcases hres with ⟨T, hT, h⟩ | ⟨T, hT, h⟩
      · exact Or.inr ⟨T, hT, h⟩
      · rw [compl_compl] at h; exact Or.inl ⟨T, hT, h⟩
  · -- ratio_monotone
    obtain ⟨hp, hhic, hcc, hlo, hhi, hL⟩ := hpc
    have hc0 : 0 < c := lt_of_lt_of_le (div_pos hbpos hkpos) (h2.trans hhic)
    obtain ⟨hb'0, hb'1, hb'2, hbb'⟩ := ceil_target hk0 hcc hk hhic h2 hc0
    have hres := hRAW G R k ⌈c * k⌉₊ hk0 hb'0 (hlo.trans hb'1) (hb'2.trans hhi)
      (le_trans (mul_le_mul_of_nonneg_right hp hnn) hd)
      (hsize _ (mul_le_mul_of_nonneg_left (hL _ h1 h2 _ hb'1 hb'2) hkpos.le))
    rcases hres with h | h
    · exact Or.inl h
    · exact Or.inr (hasBlue_le h hbb')
  · -- complementary_ratio_monotone
    obtain ⟨hpsum, hhic, hcc, hlo, hhi, hW, hL⟩ := hpc
    have hc0 : 0 < c := lt_of_lt_of_le (div_pos hbpos hkpos) (h2.trans hhic)
    obtain ⟨hb'0, hb'1, hb'2, hbb'⟩ := ceil_target hk0 hcc hk hhic h2 hc0
    set b' := ⌈c * k⌉₊ with hb'def
    have hb'pos : (0 : ℝ) < b' := by exact_mod_cast hb'0
    have hmax := hL _ h1 h2 _ hb'1 hb'2
    by_cases hred : (raw R).p * (((Finset.univ : Finset V).card : ℝ) *
        (((Finset.univ : Finset V).card : ℝ) - 1)) ≤ (redPairs G Finset.univ : ℝ)
    · rcases hRAW G R k b' hk0 hb'0 (hlo.trans hb'1) (hb'2.trans hhi) hred
        (hsize _ (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hmax) hkpos.le)) with h | h
      · exact Or.inl h
      · exact Or.inr (hasBlue_le h hbb')
    · have hblue := density_split G Finset.univ hpsum hnn hred
      obtain ⟨hSlo, hShi⟩ := hW _ hb'1 hb'2
      have hkb' : (k : ℝ) / b' = 1 / ((b' : ℝ) / k) := by field_simp
      have hres := hRAW Gᶜ S b' k hb'0 hk0 (by rw [hkb']; exact hSlo) (by rw [hkb']; exact hShi) hblue
        (hsize _ (by
          rw [hkb']
          have e : (b' : ℝ) * (raw S).L (1 / ((b' : ℝ) / k)) =
              k * ((b' : ℝ) / k * (raw S).L (1 / ((b' : ℝ) / k))) := by field_simp
          rw [e]
          exact mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hmax) hkpos.le))
      rcases hres with ⟨T, hT, h⟩ | ⟨T, hT, h⟩
      · exact Or.inr (hasBlue_le ⟨T, hT, h⟩ hbb')
      · rw [compl_compl] at h; exact Or.inl ⟨T, hT, h⟩

end

end DiagRamsey
