import Mathlib
import Definitions.Def_DiagRamsey_WeightedHost
import Lemmas.DiagRamsey_SE_Row

open Classical

namespace DiagRamsey.SE

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def hR (G : SimpleGraph V) (i y : V) : ℝ := if G.Adj i y then 1 else 0

noncomputable def uC (G : SimpleGraph V) (X : Finset V) (c : ℝ) (y : V) : ℝ := colDensity G X y - c

noncomputable def nuW (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) (y : V) : ℝ :=
  uC G X c y ^ s / colMomentSum G X Y c s

noncomputable def ZR (G B : SimpleGraph V) (X : Finset V) (c : ℝ) (i y : V) : ℝ :=
  (colDensity G (graphNbhd B X i) y - colDensity G X y) / uC G X c y

/-- Row support `V_i = E_ν[(h_iy - c)/u_y]`. -/
noncomputable def Vr (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) (i : V) : ℝ :=
  ∑ y ∈ Y, uC G X c y ^ (s - 1) * (hR G i y - c) / colMomentSum G X Y c s

/-- Row mean `E_i = E_ν Z_i`. -/
noncomputable def Er (G B : SimpleGraph V) (X Y : Finset V) (c s : ℝ) (i : V) : ℝ :=
  ∑ y ∈ Y, nuW G X Y c s y * ZR G B X c i y

/-- Red incidence `m_i = ν(red cell of i)`. -/
noncomputable def mr (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) (i : V) : ℝ :=
  ∑ y ∈ Y.filter (fun y => G.Adj i y), nuW G X Y c s y

section basic

variable (G B : SimpleGraph V) (X Y : Finset V) (c s : ℝ)

lemma uC_pos (hpos : ∀ y ∈ Y, c < colDensity G X y) {y : V} (hy : y ∈ Y) : 0 < uC G X c y := by
  unfold uC; linarith [hpos y hy]

lemma S_eq (hpos : ∀ y ∈ Y, c < colDensity G X y) :
    colMomentSum G X Y c s = ∑ y ∈ Y, uC G X c y ^ s := by
  unfold colMomentSum uC
  exact Finset.sum_congr rfl fun y hy => by rw [max_eq_left (by linarith [hpos y hy])]

lemma S_pos (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) :
    0 < colMomentSum G X Y c s := by
  rw [S_eq G X Y c s hpos]
  exact Finset.sum_pos (fun y hy => Real.rpow_pos_of_pos (uC_pos G X Y c hpos hy) _) hY

lemma nu_nonneg (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) {y : V} (hy : y ∈ Y) :
    0 ≤ nuW G X Y c s y :=
  div_nonneg (Real.rpow_nonneg (uC_pos G X Y c hpos hy).le _) (S_pos G X Y c s hY hpos).le

lemma nu_pos (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) {y : V} (hy : y ∈ Y) :
    0 < nuW G X Y c s y :=
  div_pos (Real.rpow_pos_of_pos (uC_pos G X Y c hpos hy) _) (S_pos G X Y c s hY hpos)

lemma nu_sum (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) :
    ∑ y ∈ Y, nuW G X Y c s y = 1 := by
  unfold nuW
  rw [← Finset.sum_div, ← S_eq G X Y c s hpos, div_self (S_pos G X Y c s hY hpos).ne']

lemma sum_hR (A : Finset V) (y : V) :
    ∑ i ∈ A, hR G i y = ((A.filter (fun v => G.Adj v y)).card : ℝ) := by
  unfold hR; rw [Finset.sum_boole]

lemma rowsum (A : Finset V) (hA : A.Nonempty) (y : V) :
    ∑ i ∈ A, (hR G i y - c) = A.card * (colDensity G A y - c) := by
  rw [Finset.sum_sub_distrib, sum_hR, Finset.sum_const, nsmul_eq_mul]
  unfold colDensity
  have : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  field_simp

lemma sumV_sub (A : Finset V) (hA : A.Nonempty) :
    ∑ i ∈ A, Vr G X Y c s i = A.card * ∑ y ∈ Y,
      uC G X c y ^ (s - 1) * (colDensity G A y - c) / colMomentSum G X Y c s := by
  unfold Vr
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_div, ← Finset.mul_sum, rowsum G c A hA y]
  ring

lemma nu_mul (hpos : ∀ y ∈ Y, c < colDensity G X y) {y : V} (hy : y ∈ Y) (t : ℝ) :
    nuW G X Y c s y * (t / uC G X c y) =
      uC G X c y ^ (s - 1) * t / colMomentSum G X Y c s := by
  have hu := uC_pos G X Y c hpos hy
  unfold nuW
  rw [Real.rpow_sub_one hu.ne']
  field_simp

lemma nu_clip {u S t s : ℝ} (hu : 0 < u) :
    u ^ s / S * (max (t / u) 0) ^ s = (max t 0) ^ s / S := by
  have h : max (t / u) 0 = max t 0 / u := by rw [← max_div_div_right hu.le, zero_div]
  have hus := (Real.rpow_pos_of_pos hu s).ne'
  rw [h, Real.div_rpow (le_max_right _ _) hu.le]
  field_simp

theorem sumV (hX : X.Nonempty) (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) :
    ∑ i ∈ X, Vr G X Y c s i = X.card := by
  rw [sumV_sub G X Y c s X hX]
  have : ∑ y ∈ Y, uC G X c y ^ (s - 1) * (colDensity G X y - c) / colMomentSum G X Y c s =
      ∑ y ∈ Y, nuW G X Y c s y := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have hu := uC_pos G X Y c hpos hy
    rw [← nu_mul G X Y c s hpos hy, show colDensity G X y - c = uC G X c y from rfl,
      div_self hu.ne', mul_one]
  rw [this, nu_sum G X Y c s hY hpos, mul_one]

lemma jensen_col (A : Finset V) (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y)
    (hs : 1 ≤ s) :
    ∑ y ∈ Y, uC G X c y ^ (s - 1) * (colDensity G A y - c) / colMomentSum G X Y c s ≤
      (colMomentSum G A Y c s / colMomentSum G X Y c s) ^ (1 / s) := by
  have hS := S_pos G X Y c s hY hpos
  have hJ := cell_jensen Y (nuW G X Y c s) (fun y => (colDensity G A y - c) / uC G X c y)
    (fun y hy => nu_nonneg G X Y c s hY hpos hy) (by rw [nu_sum G X Y c s hY hpos]; norm_num) hs
  rw [nu_sum G X Y c s hY hpos, div_one, one_mul] at hJ
  have e1 : ∑ y ∈ Y, nuW G X Y c s y * ((colDensity G A y - c) / uC G X c y) =
      ∑ y ∈ Y, uC G X c y ^ (s - 1) * (colDensity G A y - c) / colMomentSum G X Y c s :=
    Finset.sum_congr rfl fun y hy => nu_mul G X Y c s hpos hy _
  have e2 : ∑ y ∈ Y, nuW G X Y c s y * (max ((colDensity G A y - c) / uC G X c y) 0) ^ s =
      colMomentSum G A Y c s / colMomentSum G X Y c s := by
    unfold colMomentSum
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun y hy => nu_clip (uC_pos G X Y c hpos hy)
  rw [e1, e2] at hJ
  set Z := ∑ y ∈ Y, uC G X c y ^ (s - 1) * (colDensity G A y - c) / colMomentSum G X Y c s
  have hs0 : 0 < s := by linarith
  have h2 : max Z 0 = (max Z 0 ^ s) ^ (1 / s) := by
    rw [← Real.rpow_mul (le_max_right _ _), mul_one_div_cancel hs0.ne', Real.rpow_one]
  calc Z ≤ max Z 0 := le_max_left _ _
    _ = (max Z 0 ^ s) ^ (1 / s) := h2
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (le_max_right _ _) _) hJ (by positivity)

lemma cms_nonneg (A : Finset V) : 0 ≤ colMomentSum G A Y c s :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (le_max_right _ _) _

lemma rowmax_ratio (A : Finset V) (w r : ℝ) (hX : X.Nonempty) (hA : A.Nonempty) (hY : Y.Nonempty)
    (hpos : ∀ y ∈ Y, c < colDensity G X y) (hr : 0 < r)
    (hmax : potential G A Y c w r s ≤ potential G X Y c w r s) :
    (colMomentSum G A Y c s / colMomentSum G X Y c s) ^ (1 / s) ≤
      ((X.card : ℝ) / A.card) ^ (w / r) := by
  have hN : (0:ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hAc : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hM : (0:ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hS := S_pos G X Y c s hY hpos
  have hSA := cms_nonneg G Y c s A
  unfold potential momentNorm at hmax
  rw [show (∑ y ∈ Y, (max (colDensity G A y - c) 0) ^ s) = colMomentSum G A Y c s from rfl,
    show (∑ y ∈ Y, (max (colDensity G X y - c) 0) ^ s) = colMomentSum G X Y c s from rfl] at hmax
  set ρA := (colMomentSum G A Y c s / colMomentSum G X Y c s) ^ (1 / s) with hρA
  set H := (colMomentSum G X Y c s / Y.card) ^ (1 / s) with hH
  have hHA : (colMomentSum G A Y c s / Y.card) ^ (1 / s) = ρA * H := by
    rw [hρA, hH, ← Real.mul_rpow (div_nonneg hSA hS.le) (div_nonneg hS.le hM.le)]
    congr 1; field_simp
  have hHp : 0 < H := Real.rpow_pos_of_pos (div_pos hS hM) _
  have hρ0 : 0 ≤ ρA := Real.rpow_nonneg (div_nonneg hSA hS.le) _
  rw [hHA, Real.mul_rpow hρ0 hHp.le] at hmax
  have hHr : 0 < H ^ r := Real.rpow_pos_of_pos hHp _
  have h1 : (A.card : ℝ) ^ w * ρA ^ r ≤ (X.card : ℝ) ^ w := by
    have hpos' : 0 < (Y.card : ℝ) * H ^ r := mul_pos hM hHr
    have : ((A.card : ℝ) ^ w * ρA ^ r) * ((Y.card : ℝ) * H ^ r) ≤
        (X.card : ℝ) ^ w * ((Y.card : ℝ) * H ^ r) := by
      calc ((A.card : ℝ) ^ w * ρA ^ r) * ((Y.card : ℝ) * H ^ r) =
            (A.card : ℝ) ^ w * (Y.card : ℝ) * (ρA ^ r * H ^ r) := by ring
        _ ≤ (X.card : ℝ) ^ w * (Y.card : ℝ) * H ^ r := hmax
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hpos'
  have hAw : 0 < (A.card : ℝ) ^ w := Real.rpow_pos_of_pos hAc _
  have h2 : ρA ^ r ≤ (((X.card : ℝ) / A.card) ^ (w / r)) ^ r := by
    rw [← Real.rpow_mul (div_nonneg hN.le hAc.le), div_mul_cancel₀ w hr.ne',
      Real.div_rpow hN.le hAc.le, le_div_iff₀ hAw]
    linarith
  exact (Real.rpow_le_rpow_iff hρ0 (Real.rpow_nonneg (div_nonneg hN.le hAc.le) _) hr).1 h2

theorem Sbin (w r : ℝ) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hpos : ∀ y ∈ Y, c < colDensity G X y) (hr : 0 < r) (hs : 1 ≤ s)
    (hrow : ∀ X' : Finset V, X' ⊆ X → X'.Nonempty →
      potential G X' Y c w r s ≤ potential G X Y c w r s)
    (A : Finset V) (hAX : A ⊆ X) (hA : A.Nonempty) :
    ∑ i ∈ A, Vr G X Y c s i ≤ X.card * ((A.card : ℝ) / X.card) ^ (1 - w / r) := by
  rw [sumV_sub G X Y c s A hA]
  have h1 := jensen_col G X Y c s A hY hpos hs
  have h2 := rowmax_ratio G X Y c s A w r hX hA hY hpos hr (hrow A hAX hA)
  have hN : (0:ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hAc : (0:ℝ) < A.card := by exact_mod_cast hA.card_pos
  calc (A.card : ℝ) * _ ≤ A.card * ((X.card : ℝ) / A.card) ^ (w / r) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hAc.le
    _ = X.card * ((A.card : ℝ) / X.card) ^ (1 - w / r) := by
      rw [Real.rpow_sub (div_pos hAc hN), Real.rpow_one, Real.div_rpow hN.le hAc.le,
        Real.div_rpow hAc.le hN.le]
      have := (Real.rpow_pos_of_pos hN (w / r)).ne'
      have := (Real.rpow_pos_of_pos hAc (w / r)).ne'
      field_simp

theorem Vlow (w r : ℝ) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hpos : ∀ y ∈ Y, c < colDensity G X y) (hr : 0 < r) (hs : 1 ≤ s) (hw : 0 ≤ w) (hwr : w ≤ r)
    (hrow : ∀ X' : Finset V, X' ⊆ X → X'.Nonempty →
      potential G X' Y c w r s ≤ potential G X Y c w r s)
    (i : V) (hi : i ∈ X) : 1 - w / r ≤ Vr G X Y c s i := by
  have hsum := sumV G X Y c s hX hY hpos
  have hwr0 : 0 ≤ w / r := div_nonneg hw hr.le
  have hwr1 : w / r ≤ 1 := (div_le_one hr).2 hwr
  by_cases he : (X.erase i).Nonempty
  · have h := Sbin G X Y c s w r hX hY hpos hr hs hrow (X.erase i) (Finset.erase_subset _ _) he
    rw [Finset.sum_erase_eq_sub hi, hsum, Finset.card_erase_of_mem hi] at h
    have hN1 : 1 ≤ X.card := hX.card_pos
    rw [Nat.cast_sub hN1, Nat.cast_one] at h
    have hN : (0:ℝ) < X.card := by exact_mod_cast hX.card_pos
    have hN1' : (1:ℝ) ≤ X.card := by exact_mod_cast hN1
    have hb := rpow_one_add_le_one_add_mul_self (s := -1 / (X.card : ℝ)) (p := 1 - w / r)
      (by rw [neg_div, neg_le_neg_iff, div_le_one hN]; exact hN1') (by linarith) (by linarith)
    have e : ((X.card : ℝ) - 1) / X.card = 1 + -1 / X.card := by field_simp; ring
    rw [e] at h
    have h3 := mul_le_mul_of_nonneg_left hb hN.le
    have e2 : (X.card : ℝ) * (1 + (1 - w / r) * (-1 / X.card)) = X.card - (1 - w / r) := by
      field_simp; ring
    linarith
  · have hX1 : X = {i} := by
      rw [Finset.not_nonempty_iff_eq_empty, Finset.erase_eq_empty_iff] at he
      rcases he with h | h
      · exact absurd h hX.ne_empty
      · exact h
    have h1 : ∑ j ∈ X, Vr G X Y c s j = Vr G X Y c s i :=
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
        rw [hX1] at hj; exact absurd (Finset.mem_singleton.1 hj) hji)
    have hc : (X.card : ℝ) = 1 := by rw [hX1, Finset.card_singleton, Nat.cast_one]
    rw [h1, hc] at hsum
    linarith

end basic

section stat

variable (G B : SimpleGraph V) (X Y : Finset V) (c s : ℝ)

lemma qb_eq (i y : V) : graphFrac B X i * colDensity G (graphNbhd B X i) y =
    (((graphNbhd B X i).filter (fun v => G.Adj v y)).card : ℝ) / X.card := by
  unfold graphFrac colDensity
  by_cases h : ((graphNbhd B X i).card : ℝ) = 0
  · have h0 : graphNbhd B X i = ∅ := Finset.card_eq_zero.1 (by exact_mod_cast h)
    simp [h0]
  · field_simp

lemma stat_col (y : V) : ∑ i ∈ X, graphFrac B X i * colDensity G (graphNbhd B X i) y =
    ∑ i ∈ X, graphFrac B X i * hR G i y := by
  simp only [qb_eq]
  unfold graphFrac
  rw [← Finset.sum_div]
  have : ∑ i ∈ X, ((graphNbhd B X i).card : ℝ) / X.card * hR G i y =
      (∑ i ∈ X, ((graphNbhd B X i).card : ℝ) * hR G i y) / X.card := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  congr 1
  unfold graphNbhd hR
  simp only [Finset.filter_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [B.adj_comm b a]
  split_ifs <;> simp_all

theorem stationarity (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) :
    ∑ i ∈ X, graphFrac B X i * Er G B X Y c s i =
      ∑ i ∈ X, graphFrac B X i * (Vr G X Y c s i - 1) := by
  have hV1 : ∀ i, Vr G X Y c s i - 1 = ∑ y ∈ Y,
      uC G X c y ^ (s - 1) * (hR G i y - colDensity G X y) / colMomentSum G X Y c s := by
    intro i
    rw [show Vr G X Y c s i - 1 = Vr G X Y c s i - ∑ y ∈ Y, nuW G X Y c s y by
      rw [nu_sum G X Y c s hY hpos], Vr, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hu := uC_pos G X Y c hpos hy
    unfold nuW
    rw [show uC G X c y ^ s = uC G X c y ^ (s - 1) * uC G X c y by
      rw [Real.rpow_sub_one hu.ne']; field_simp]
    unfold uC
    ring
  have hE : ∀ i, Er G B X Y c s i = ∑ y ∈ Y, uC G X c y ^ (s - 1) *
      (colDensity G (graphNbhd B X i) y - colDensity G X y) / colMomentSum G X Y c s := by
    intro i
    exact Finset.sum_congr rfl fun y hy => nu_mul G X Y c s hpos hy _
  simp only [hV1, hE, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e : ∀ F : V → ℝ, ∑ i ∈ X, graphFrac B X i *
      (uC G X c y ^ (s - 1) * (F i - colDensity G X y) / colMomentSum G X Y c s) =
      uC G X c y ^ (s - 1) / colMomentSum G X Y c s *
        (∑ i ∈ X, graphFrac B X i * F i - ∑ i ∈ X, graphFrac B X i * colDensity G X y) := by
    intro F
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e (fun i => colDensity G (graphNbhd B X i) y), e (fun i => hR G i y), stat_col]

end stat

end DiagRamsey.SE
