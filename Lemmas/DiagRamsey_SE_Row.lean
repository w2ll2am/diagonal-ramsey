import Mathlib
import Lemmas.DiagRamsey_SE_PRL

open Filter Topology

namespace DiagRamsey.SE

/-- Jensen for the clipped power on a sub-cell `T` of a weight vector. -/
lemma cell_jensen {ι : Type*} (T : Finset ι) (ν x : ι → ℝ) (hν : ∀ y ∈ T, 0 ≤ ν y)
    (hm : 0 < ∑ y ∈ T, ν y) {s : ℝ} (hs : 1 ≤ s) :
    (∑ y ∈ T, ν y) * (max ((∑ y ∈ T, ν y * x y) / ∑ y ∈ T, ν y) 0) ^ s ≤
      ∑ y ∈ T, ν y * (max (x y) 0) ^ s := by
  set m := ∑ y ∈ T, ν y with hmdef
  have hw : ∀ y ∈ T, 0 ≤ ν y / m := fun y hy => div_nonneg (hν y hy) hm.le
  have hw1 : ∑ y ∈ T, ν y / m = 1 := by rw [← Finset.sum_div, div_self hm.ne']
  have hpm := Real.rpow_arith_mean_le_arith_mean_rpow T (fun y => ν y / m)
    (fun y => max (x y) 0) hw hw1 (fun y _ => le_max_right _ _) hs
  have h1 : max ((∑ y ∈ T, ν y * x y) / m) 0 ≤ ∑ y ∈ T, ν y / m * max (x y) 0 := by
    apply max_le
    · rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro y hy
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (hν y hy)) hm.le
    · exact Finset.sum_nonneg fun y hy => mul_nonneg (hw y hy) (le_max_right _ _)
  have h2 := Real.rpow_le_rpow (le_max_right _ _) h1 (by linarith : (0:ℝ) ≤ s)
  have h3 : ∑ y ∈ T, ν y / m * max (x y) 0 ^ s = (∑ y ∈ T, ν y * max (x y) 0 ^ s) / m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h4 : (max ((∑ y ∈ T, ν y * x y) / m) 0) ^ s ≤ (∑ y ∈ T, ν y * max (x y) 0 ^ s) / m :=
    h2.trans (hpm.trans h3.le)
  calc m * (max ((∑ y ∈ T, ν y * x y) / m) 0) ^ s ≤
        m * ((∑ y ∈ T, ν y * max (x y) 0 ^ s) / m) := mul_le_mul_of_nonneg_left h4 hm.le
    _ = _ := by field_simp

/-- Tangent-line inequality for `x ↦ x^s`, `s ≥ 1`. -/
lemma rpow_tangent {x0 x s : ℝ} (hx0 : 0 < x0) (hx : 0 ≤ x) (hs : 1 ≤ s) :
    x0 ^ s + s * x0 ^ (s - 1) * (x - x0) ≤ x ^ s := by
  have hb := one_add_mul_self_le_rpow_one_add (show (-1:ℝ) ≤ x / x0 - 1 by
    have : 0 ≤ x / x0 := div_nonneg hx hx0.le
    linarith) hs
  rw [show (1:ℝ) + (x / x0 - 1) = x / x0 by ring, Real.div_rpow hx hx0.le] at hb
  have hpos : 0 < x0 ^ s := Real.rpow_pos_of_pos hx0 s
  rw [le_div_iff₀ hpos] at hb
  have : x0 ^ s + s * x0 ^ (s - 1) * (x - x0) = (1 + s * (x / x0 - 1)) * x0 ^ s := by
    rw [Real.rpow_sub_one hx0.ne']
    field_simp
  linarith

/-- The two-cell envelope: for an in-cell value `A ≥ A0 > U^{1/s}`, the objective is maximised at
`A = A0` on the constraint boundary. -/
theorem two_cell {m s U A0 A C : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hs : 1 ≤ s)
    (hA0 : 0 < A0) (hA0U : U < A0 ^ s) (hA : A0 ≤ A)
    (hcon : m * A ^ s + (1 - m) * (max C 0) ^ s < U) :
    0 < U - m * A0 ^ s ∧
    m * A + (1 - m) * C ≤ m * A0 + (1 - m) * ((U - m * A0 ^ s) / (1 - m)) ^ (1 / s) := by
  have hs0 : 0 < s := by linarith
  have h1m : 0 < 1 - m := by linarith
  have hAs : A0 ^ s ≤ A ^ s := Real.rpow_le_rpow hA0.le hA hs0.le
  have hCs : 0 ≤ (max C 0) ^ s := Real.rpow_nonneg (le_max_right _ _) _
  have hCs' : 0 ≤ (1 - m) * (max C 0) ^ s := mul_nonneg h1m.le hCs
  have hW1 : 0 < U - m * A ^ s := by linarith
  have hW0 : 0 < U - m * A0 ^ s := by nlinarith
  refine ⟨hW0, ?_⟩
  set W := (U - m * A0 ^ s) / (1 - m) with hW
  set W1 := (U - m * A ^ s) / (1 - m) with hW1d
  have hWp : 0 < W := div_pos hW0 h1m
  have hW1p : 0 < W1 := div_pos hW1 h1m
  set c0 := W ^ (1 / s) with hc0
  set c1 := W1 ^ (1 / s) with hc1
  have hc0p : 0 < c0 := Real.rpow_pos_of_pos hWp _
  have hc0s : c0 ^ s = W := by
    rw [hc0, ← Real.rpow_mul hWp.le, one_div_mul_cancel hs0.ne', Real.rpow_one]
  have hc1s : c1 ^ s = W1 := by
    rw [hc1, ← Real.rpow_mul hW1p.le, one_div_mul_cancel hs0.ne', Real.rpow_one]
  have hc1n : 0 ≤ c1 := Real.rpow_nonneg hW1p.le _
  have hCc1 : C ≤ c1 := by
    have h : (max C 0) ^ s ≤ W1 := by
      rw [hW1d, le_div_iff₀ h1m]; linarith
    have h2 : max C 0 ≤ c1 := by
      rw [← Real.rpow_le_rpow_iff (le_max_right _ _) hc1n hs0, hc1s]; exact h
    exact (le_max_left _ _).trans h2
  have hc0A : c0 ≤ A0 := by
    have : W < A0 ^ s := by
      rw [hW, div_lt_iff₀ h1m]; nlinarith
    rw [← Real.rpow_le_rpow_iff hc0p.le hA0.le hs0, hc0s]; exact this.le
  have t1 := rpow_tangent hA0 (hA0.le.trans hA) hs
  have t2 := rpow_tangent hc0p hc1n hs
  have eq1 : m * A ^ s + (1 - m) * c1 ^ s = U := by
    rw [hc1s, hW1d]; field_simp; ring
  have eq0 : m * A0 ^ s + (1 - m) * c0 ^ s = U := by
    rw [hc0s, hW]; field_simp; ring
  have hpow : c0 ^ (s - 1) ≤ A0 ^ (s - 1) := Real.rpow_le_rpow hc0p.le hc0A (by linarith)
  have hcp : 0 < c0 ^ (s - 1) := Real.rpow_pos_of_pos hc0p _
  have key : m * s * c0 ^ (s - 1) * (A - A0) ≤ (1 - m) * s * c0 ^ (s - 1) * (c0 - c1) := by
    have h3 : m * s * c0 ^ (s - 1) * (A - A0) ≤ m * s * A0 ^ (s - 1) * (A - A0) := by
      have : 0 ≤ m * s * (A - A0) := by have := sub_nonneg.2 hA; positivity
      have := mul_le_mul_of_nonneg_left hpow this
      linarith
    have k1 := mul_le_mul_of_nonneg_left t1 hm0.le
    have k2 := mul_le_mul_of_nonneg_left t2 h1m.le
    nlinarith
  have key2 : m * (A - A0) ≤ (1 - m) * (c0 - c1) := by
    have hsc : 0 < s * c0 ^ (s - 1) := mul_pos hs0 hcp
    have : (m * (A - A0)) * (s * c0 ^ (s - 1)) ≤ ((1 - m) * (c0 - c1)) * (s * c0 ^ (s - 1)) := by
      calc (m * (A - A0)) * (s * c0 ^ (s - 1)) = m * s * c0 ^ (s - 1) * (A - A0) := by ring
        _ ≤ (1 - m) * s * c0 ^ (s - 1) * (c0 - c1) := key
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hsc
  have := mul_le_mul_of_nonneg_left hCc1 h1m.le
  linarith

/-- The red failure inequality, Jensen-reduced to the red cell, in the `ellF` normalisation. -/
lemma red_conv {w β x q m π r X : ℝ} (hβ0 : 0 < β) (hr : 0 < r) (hq1 : q < 1) (hm0 : 0 < m)
    (hπ0 : 0 < π) (hx0 : 0 < x)
    (h : m * (max X 0) ^ (β * r) < (1 - q) ^ (β * r - w * β) * x ^ β * π ^ (1 - β)) :
    X < (1 - q) * Real.exp (ellF w β x q m π / r) := by
  have hq : 0 < 1 - q := by linarith
  have hs : 0 < β * r := mul_pos hβ0 hr
  have hβne := hβ0.ne'
  have hrne := hr.ne'
  set Y := (1 - q) * Real.exp (ellF w β x q m π / r) with hY
  have hYp : 0 < Y := mul_pos hq (Real.exp_pos _)
  have hA : 0 < (1 - q) ^ (β * r - w * β) := Real.rpow_pos_of_pos hq _
  have hB : 0 < x ^ β := Real.rpow_pos_of_pos hx0 _
  have hC : 0 < π ^ (1 - β) := Real.rpow_pos_of_pos hπ0 _
  have hL : Real.log (m * Y ^ (β * r)) =
      Real.log ((1 - q) ^ (β * r - w * β) * x ^ β * π ^ (1 - β)) := by
    rw [Real.log_mul hm0.ne' (Real.rpow_pos_of_pos hYp _).ne', Real.log_rpow hYp, hY,
      Real.log_mul hq.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (mul_pos hA hB).ne' hC.ne', Real.log_mul hA.ne' hB.ne',
      Real.log_rpow hq, Real.log_rpow hx0, Real.log_rpow hπ0]
    unfold ellF
    field_simp
    ring
  have hYs : m * Y ^ (β * r) = (1 - q) ^ (β * r - w * β) * x ^ β * π ^ (1 - β) := by
    have := congrArg Real.exp hL
    rwa [Real.exp_log (mul_pos hm0 (Real.rpow_pos_of_pos hYp _)),
      Real.exp_log (mul_pos (mul_pos hA hB) hC)] at this
  by_contra hc
  have hc' : Y ≤ max X 0 := (le_of_not_gt hc).trans (le_max_left _ _)
  have := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hYp.le hc' hs.le) hm0.le
  linarith

/-- The scalar consequences of (B), (R) and Jensen give `RowBound`. -/
theorem rowbound_of_cells {μ w β x q m π r E zin zout : ℝ} (hβ0 : 0 < β) (hr : 0 < r)
    (hs1 : 1 ≤ β * r) (hq0 : 0 < q) (hq1 : q < 1) (hm0 : 0 < m) (hm1 : m ≤ 1) (hπ0 : 0 < π)
    (hx0 : 0 < x)
    (hE : E = m * zin + (1 - m) * zout)
    (hJ : (max (1 + E) 0) ^ (β * r) < certU μ w β q)
    (hred : m * (max ((1 - q) - q * zin) 0) ^ (β * r) <
      (1 - q) ^ (β * r - w * β) * x ^ β * π ^ (1 - β))
    (hblue : m * (max (1 + zin) 0) ^ (β * r) + (1 - m) * (max (1 + zout) 0) ^ (β * r) <
      certU μ w β q) :
    RowBound μ w β x q m π r E := by
  have hs0 : 0 < β * r := by linarith
  have hrne := hr.ne'
  have hβne := hβ0.ne'
  have hTF : TF μ w q r ^ (β * r) = certU μ w β q := by
    unfold TF certU; rw [← Real.exp_mul]; congr 1; field_simp
  have hTFp : 0 < TF μ w q r := Real.exp_pos _
  have hzin : LF w β x q m π r < zin := by
    have h := red_conv hβ0 hr hq1 hm0 hπ0 hx0 hred
    unfold LF
    rw [div_lt_iff₀ hq0]; nlinarith
  have hPw : ∀ _ : 0 < 1 + LF w β x q m π r,
      PwF w β x q m π r = (1 + LF w β x q m π r) ^ (β * r) := by
    intro h; unfold PwF; rw [Real.rpow_def_of_pos h]; congr 1; ring
  have hJ' : max (1 + E) 0 < TF μ w q r := by
    rw [← Real.rpow_lt_rpow_iff (le_max_right _ _) hTFp.le hs0, hTF]; exact hJ
  have hE1 := le_max_left (1 + E) 0
  refine ⟨by linarith, ?_, ?_⟩
  · intro h
    rw [hPw h]
    have h1 : (1 + LF w β x q m π r) ^ (β * r) ≤ (max (1 + zin) 0) ^ (β * r) :=
      Real.rpow_le_rpow h.le ((by linarith : 1 + LF w β x q m π r ≤ 1 + zin).trans
        (le_max_left _ _)) hs0.le
    have h2 : 0 ≤ (1 - m) * (max (1 + zout) 0) ^ (β * r) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (le_max_right _ _) _)
    have := mul_le_mul_of_nonneg_left h1 hm0.le
    linarith
  · intro hT
    have hA0 : 0 < 1 + LF w β x q m π r := hTFp.trans hT
    have hm1' : m < 1 := by
      rcases hm1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hE' : E = zin := by rw [hE, h]; ring
        linarith
    refine ⟨hm1', ?_⟩
    have hU : certU μ w β q < (1 + LF w β x q m π r) ^ (β * r) := by
      rw [← hTF]; exact Real.rpow_lt_rpow hTFp.le hT hs0
    rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 + zin)] at hblue
    obtain ⟨hW0, hmain⟩ := two_cell hm0 hm1' hs1 hA0 hU
      (by linarith : 1 + LF w β x q m π r ≤ 1 + zin) hblue
    have hWF : WF μ w β x q m π r =
        (certU μ w β q - m * (1 + LF w β x q m π r) ^ (β * r)) / (1 - m) := by
      unfold WF; rw [hPw hA0]
    have hWp : 0 < WF μ w β x q m π r := by rw [hWF]; exact div_pos hW0 (by linarith)
    have hexp : Real.exp (Real.log (WF μ w β x q m π r) / (β * r)) =
        WF μ w β x q m π r ^ (1 / (β * r)) := by
      rw [Real.rpow_def_of_pos hWp]; congr 1; ring
    rw [hexp, hWF, hE]
    linarith

end DiagRamsey.SE
