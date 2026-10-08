import Mathlib
import Lemmas.DiagRamsey_SE_Calc

namespace DiagRamsey.SE

open Finset

/-- Enumeration of a finset sorted by a real key, with its initial segments. -/
theorem sorted_enum {V : Type*} (X : Finset V) (hX : X.Nonempty) (q : V → ℝ) :
    ∃ idx : ℕ → V, (∀ k < X.card, idx k ∈ X) ∧
      (∀ F : V → ℝ, ∑ i ∈ X, F i = ∑ k ∈ range X.card, F (idx k)) ∧
      (∀ k, k + 1 < X.card → q (idx k) ≤ q (idx (k + 1))) ∧
      (∀ k ≤ X.card, ∃ A ⊆ X, A.card = k ∧
        ∀ F : V → ℝ, ∑ i ∈ A, F i = ∑ l ∈ range k, F (idx l)) := by
  classical
  set N := X.card with hN
  have hNpos : 0 < N := hX.card_pos
  let e0 : Fin N ≃ X := X.equivFin.symm
  let f : Fin N → ℝ := fun j => q (e0 j)
  let σ := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  let g : Fin N → V := fun j => (e0 (σ j) : V)
  have ginj : Function.Injective g := by
    intro a b h
    have := Subtype.ext h
    exact σ.injective (e0.injective this)
  set idx : ℕ → V := fun k => if h : k < N then g ⟨k, h⟩ else g ⟨0, hNpos⟩ with hidx
  have hidxj : ∀ j : Fin N, idx j = g j := by
    intro j; simp only [hidx, dif_pos j.isLt, Fin.eta]
  refine ⟨idx, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have := hidxj ⟨k, hk⟩
    simp only at this
    rw [this]; exact (e0 (σ ⟨k, hk⟩)).2
  · intro F
    have h1 : ∑ i ∈ X, F i = ∑ j : Fin N, F (g j) := by
      rw [← Finset.sum_coe_sort X F, ← Equiv.sum_comp e0, ← Equiv.sum_comp σ]
    rw [h1, ← Fin.sum_univ_eq_sum_range (fun k => F (idx k))]
    exact Finset.sum_congr rfl fun j _ => by rw [hidxj]
  · intro k hk
    have h1 := hidxj ⟨k, by omega⟩
    have h2 := hidxj ⟨k + 1, hk⟩
    simp only at h1 h2
    rw [h1, h2]
    exact hmono (show (⟨k, by omega⟩ : Fin N) ≤ ⟨k + 1, hk⟩ from Fin.mk_le_mk.2 (Nat.le_succ k))
  · intro k hk
    set A := (univ.filter (fun j : Fin N => j.val < k)).map ⟨g, ginj⟩ with hA
    have hsumA : ∀ F : V → ℝ, ∑ i ∈ A, F i = ∑ l ∈ range k, F (idx l) := by
      intro F
      rw [hA, Finset.sum_map, Finset.sum_filter]
      have h2 : ∑ j : Fin N, (if (j:ℕ) < k then F (g j) else 0) =
          ∑ l ∈ range N, (if l < k then F (idx l) else 0) := by
        rw [← Fin.sum_univ_eq_sum_range (fun l => if l < k then F (idx l) else 0)]
        exact Finset.sum_congr rfl fun j _ => by rw [hidxj]
      simp only [Function.Embedding.coeFn_mk]
      rw [h2, ← Finset.sum_filter]
      congr 1
      ext l; simp only [mem_filter, mem_range]; omega
    refine ⟨A, ?_, ?_, hsumA⟩
    · intro v hv
      rw [hA, Finset.mem_map] at hv
      obtain ⟨j, _, rfl⟩ := hv
      exact (e0 (σ j)).2
    · have := hsumA (fun _ => 1)
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range] at this
      exact_mod_cast this

/-- Quantile drift: sorted rows, discrete Abel summation against the row-support bound. -/
theorem drift {V : Type*} (X : Finset V) (hX : X.Nonempty) (q Vf : V → ℝ) (r γ : ℝ)
    (hr : 0 < r) (hγ0 : 0 < γ)
    (hsum : ∑ i ∈ X, Vf i = X.card)
    (hS : ∀ A ⊆ X, A.Nonempty → ∑ i ∈ A, Vf i ≤ X.card * ((A.card : ℝ) / X.card) ^ γ) :
    ∃ idx : ℕ → V, (∀ k < X.card, idx k ∈ X) ∧
      (∀ F : V → ℝ, ∑ i ∈ X, F i = ∑ k ∈ range X.card, F (idx k)) ∧
      (X.card : ℝ) * ∑ k ∈ range X.card, q (idx k) *
          (PhiK r γ (((k:ℝ) + 1) / X.card) - PhiK r γ ((k:ℝ) / X.card)) ≤
        r * ∑ k ∈ range X.card, q (idx k) * (Vf (idx k) - 1) := by
  obtain ⟨idx, hmem, hsumF, hmono, hpre⟩ := sorted_enum X hX q
  refine ⟨idx, hmem, hsumF, ?_⟩
  set N := X.card with hNdef
  have hNpos : 0 < N := hX.card_pos
  have hN' : (0:ℝ) < N := by exact_mod_cast hNpos
  set D : ℕ → ℝ := fun k => ∑ l ∈ range k, Vf (idx l) - N * ((k:ℝ) / N) ^ γ with hD
  have hD0 : D 0 = 0 := by simp [hD, Real.zero_rpow hγ0.ne']
  have hDle : ∀ k ≤ N - 1 + 1, D k ≤ 0 := by
    intro k hk
    rw [Nat.sub_add_cancel hNpos] at hk
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, hD0]
    · obtain ⟨A, hAX, hAc, hAF⟩ := hpre k hk
      have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
      have := hS A hAX hAne
      rw [hAF, hAc] at this
      simp only [hD]
      linarith
  have hDN : D N = 0 := by
    simp only [hD]
    rw [← hsumF Vf, hsum, div_self hN'.ne', Real.one_rpow, mul_one, sub_self]
  have hab := abel_drift (fun k => q (idx k)) D (N - 1)
    (fun k hk => hmono k (by omega)) hDle hD0
  rw [Nat.sub_add_cancel hNpos, hDN, mul_zero] at hab
  have hdiff : ∀ k ∈ range N, q (idx k) * (D (k + 1) - D k) =
      q (idx k) * Vf (idx k) - N * (q (idx k) * ((((k:ℝ) + 1) / N) ^ γ - ((k:ℝ) / N) ^ γ)) := by
    intro k _
    simp only [hD, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    ring
  rw [Finset.sum_congr rfl hdiff, Finset.sum_sub_distrib, ← Finset.mul_sum] at hab
  set A := ∑ k ∈ range N, q (idx k) * ((((k:ℝ) + 1) / N) ^ γ - ((k:ℝ) / N) ^ γ)
  set B := ∑ k ∈ range N, q (idx k)
  set Cq := ∑ k ∈ range N, q (idx k) * Vf (idx k)
  have e1 : ∀ k ∈ range N, q (idx k) *
      (PhiK r γ (((k:ℝ) + 1) / N) - PhiK r γ ((k:ℝ) / N)) =
      r * (q (idx k) * ((((k:ℝ) + 1) / N) ^ γ - ((k:ℝ) / N) ^ γ)) - r / N * q (idx k) := by
    intro k _
    unfold PhiK
    field_simp
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e2 : ∑ k ∈ range N, q (idx k) * (Vf (idx k) - 1) = Cq - B := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e2]
  have e3 : (N:ℝ) * (r / N * B) = r * B := by field_simp
  have := mul_le_mul_of_nonneg_left (show (N:ℝ) * A ≤ Cq by linarith) hr.le
  nlinarith

end DiagRamsey.SE
