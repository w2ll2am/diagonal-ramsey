import Lemmas.DiagRamsey_balanced_cut
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace DiagRamsey

open Finset


open MajorityCut in
theorem majority_colour_balanced_cut (N : ℕ) (hN : 2 ≤ N) (c : Fin N → Fin N → Bool)
    (hc : ∀ u v, c u v = c v u) :
    ∃ b : Bool,
      N * (N - 1) ≤
          2 * (Finset.univ.filter (fun e : Fin N × Fin N => e.1 ≠ e.2 ∧ c e.1 e.2 = b)).card ∧
      ∃ X : Finset (Fin N), N ≤ 3 * X.card ∧ N ≤ 3 * Xᶜ.card ∧
        X.card * Xᶜ.card ≤ 2 * ((X ×ˢ Xᶜ).filter (fun e : Fin N × Fin N => c e.1 e.2 = b)).card := by
  set D : Finset (Fin N × Fin N) := univ.filter (fun e => e.1 ≠ e.2) with hD
  have hDcard : D.card = N * (N - 1) := by
    have : D = (univ : Finset (Fin N)).offDiag := by
      ext e; simp [hD, mem_offDiag]
    rw [this, offDiag_card, card_univ, Fintype.card_fin, Nat.mul_sub_one]
  -- majority colour
  have hsplit : ∀ b : Bool, (univ.filter (fun e : Fin N × Fin N => e.1 ≠ e.2 ∧ c e.1 e.2 = b)) =
      D.filter (fun e => c e.1 e.2 = b) := by
    intro b; ext e; simp [hD]
  have hsum : (D.filter (fun e => c e.1 e.2 = true)).card +
      (D.filter (fun e => c e.1 e.2 = false)).card = D.card := by
    have := card_filter_add_card_filter_not (s := D) (fun e : Fin N × Fin N => c e.1 e.2 = true)
    simpa using this
  obtain ⟨b, hb⟩ : ∃ b : Bool, D.card ≤ 2 * (D.filter (fun e => c e.1 e.2 = b)).card := by
    by_cases h : D.card ≤ 2 * (D.filter (fun e => c e.1 e.2 = true)).card
    · exact ⟨true, h⟩
    · exact ⟨false, by omega⟩
  refine ⟨b, by rw [hsplit, ← hDcard]; exact hb, ?_⟩
  -- averaging over permutations
  set m := N / 2 with hm
  have hmN : m ≤ N := Nat.div_le_self N 2
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set e0 : Fin N × Fin N := (⟨0, by omega⟩, ⟨1, by omega⟩) with he0
  set R := D.filter (fun e => c e.1 e.2 = b) with hR
  have hRD : ∀ e ∈ R, e.1 ≠ e.2 := by
    intro e he; simp only [hR, hD, mem_filter, mem_univ, true_and] at he; exact he.1
  have hDD : ∀ e ∈ D, e.1 ≠ e.2 := by
    intro e he; simp only [hD, mem_filter, mem_univ, true_and] at he; exact he
  have sumR := sum_card_sep m R hRD e0 h01
  have sumD := sum_card_sep m D hDD e0 h01
  have hD' : ∀ σ : Equiv.Perm (Fin N), (D.filter (Separates m σ)).card = m * (N - m) := by
    intro σ; rw [hD]; exact card_sep_offDiag m hmN σ
  simp_rw [hD'] at sumD
  have hle : ∑ _σ : Equiv.Perm (Fin N), m * (N - m) ≤
      ∑ σ : Equiv.Perm (Fin N), 2 * (R.filter (Separates m σ)).card := by
    rw [sumD, ← Finset.mul_sum, sumR]
    calc D.card * K m e0 ≤ (2 * R.card) * K m e0 := Nat.mul_le_mul_right _ hb
      _ = 2 * (R.card * K m e0) := Nat.mul_assoc _ _ _
  obtain ⟨σ, -, hσ⟩ := exists_le_of_sum_le (s := (univ : Finset (Equiv.Perm (Fin N))))
    univ_nonempty hle
  set X : Finset (Fin N) := univ.filter (fun i => (σ i).val < m) with hX
  have hXc : X.card = m := by
    have : X.card = (univ.filter (fun j : Fin N => j.val < m)).card := by
      apply card_equiv σ
      intro i; simp [hX]
    rw [this]
    have h := Fin.card_filter_val_lt (n := N) (m := m)
    simpa [min_eq_right hmN] using h
  have hXcc : Xᶜ.card = N - m := by rw [card_compl, Fintype.card_fin, hXc]
  have hcross : (X ×ˢ Xᶜ).filter (fun e : Fin N × Fin N => c e.1 e.2 = b) = R.filter (Separates m σ) := by
    ext e
    simp only [hR, hD, hX, mem_filter, mem_product, mem_compl, mem_univ, true_and, Separates]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, h3⟩, h1, h2⟩
      intro hh; rw [hh] at h1; exact h2 h1
    · rintro ⟨⟨_, h3⟩, h1, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  refine ⟨X, ?_, ?_, ?_⟩
  · rw [hXc]; omega
  · rw [hXcc]; omega
  · rw [hXc, hXcc, hcross]; exact hσ

end DiagRamsey

theorem solution_majority_colour_balanced_cut (N : ℕ) (hN : 2 ≤ N) (c : Fin N → Fin N → Bool)
    (hc : ∀ u v, c u v = c v u) :
    ∃ b : Bool,
      N * (N - 1) ≤
          2 * (Finset.univ.filter (fun e : Fin N × Fin N => e.1 ≠ e.2 ∧ c e.1 e.2 = b)).card ∧
      ∃ X : Finset (Fin N), N ≤ 3 * X.card ∧ N ≤ 3 * Xᶜ.card ∧
        X.card * Xᶜ.card ≤ 2 * ((X ×ˢ Xᶜ).filter (fun e : Fin N × Fin N => c e.1 e.2 = b)).card :=
  DiagRamsey.majority_colour_balanced_cut N hN c hc
