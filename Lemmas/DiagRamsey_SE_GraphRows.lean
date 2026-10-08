import Mathlib
import Lemmas.DiagRamsey_SE_Graph

open Classical

namespace DiagRamsey.SE

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma ub_scalar {μ w q r E : ℝ} (hq0 : 0 < q) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hw : 0 < w)
    (hr : 2 * w ≤ r) (hE : E ≤ TF μ w q r - 1) : r * (q * E) ≤ w := by
  have hr0 : 0 < r := by linarith
  have h1 : r * (q * E) ≤ q * (r * (TF μ w q r - 1)) := by
    have := mul_le_mul_of_nonneg_left hE (mul_nonneg hq0.le hr0.le); linarith
  set ℓ := Real.log (μ / q) with hℓ
  have hTF : TF μ w q r = Real.exp (w * ℓ / r) := by unfold TF certB; rfl
  rw [hTF] at h1
  rcases le_or_gt ℓ 0 with hl | hl
  · have h2 : w * ℓ / r ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hw.le hl) hr0.le
    have h3 : Real.exp (w * ℓ / r) ≤ 1 := Real.exp_le_one_iff.2 h2
    have : q * (r * (Real.exp (w * ℓ / r) - 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hq0.le (mul_nonpos_of_nonneg_of_nonpos hr0.le (by linarith))
    linarith
  · set y := w * ℓ / r with hy
    have hy0 : 0 < y := by positivity
    have hyl : y ≤ ℓ / 2 := by rw [hy, div_le_iff₀ hr0]; nlinarith
    have hey : Real.exp y - 1 ≤ y * Real.exp y := by
      have h := Real.add_one_le_exp (-y)
      have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
      have := mul_le_mul_of_nonneg_right h (Real.exp_pos y).le
      nlinarith
    have hry : r * y = w * ℓ := by rw [hy]; field_simp
    have he2 : Real.exp y ≤ Real.exp (ℓ / 2) := Real.exp_le_exp.2 hyl
    have hqe : q * Real.exp ℓ = μ := by rw [hℓ, Real.exp_log (div_pos hμ0 hq0)]; field_simp
    have hl2 : ℓ ≤ Real.exp (ℓ / 2) := by
      have := Real.quadratic_le_exp_of_nonneg (x := ℓ / 2) (by linarith)
      nlinarith [sq_nonneg (ℓ - 2)]
    have hee : Real.exp (ℓ / 2) * Real.exp (ℓ / 2) = Real.exp ℓ := by
      rw [← Real.exp_add]; ring_nf
    have s1 : q * (r * (Real.exp y - 1)) ≤ q * (w * ℓ * Real.exp y) := by
      apply mul_le_mul_of_nonneg_left _ hq0.le
      have := mul_le_mul_of_nonneg_left hey hr0.le
      rw [← hry]; linarith
    have s2 : q * (w * ℓ * Real.exp y) ≤ w * (q * ℓ * Real.exp (ℓ / 2)) := by
      have := mul_le_mul_of_nonneg_left he2 (by positivity : 0 ≤ q * w * ℓ); linarith
    have s3 : q * ℓ * Real.exp (ℓ / 2) ≤ μ := by
      have := mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ q * Real.exp (ℓ / 2))
      have h5 : q * Real.exp (ℓ / 2) * Real.exp (ℓ / 2) = q * Real.exp ℓ := by
        rw [mul_assoc, hee]
      linarith
    have s4 := mul_le_mul_of_nonneg_left s3 hw.le
    have s5 : w * μ ≤ w := by nlinarith
    linarith

section rows

variable (G B : SimpleGraph V) (X Y : Finset V) (c s : ℝ)

lemma one_add_ZR (hpos : ∀ y ∈ Y, c < colDensity G X y) (i : V) {y : V} (hy : y ∈ Y) :
    1 + ZR G B X c i y = (colDensity G (graphNbhd B X i) y - c) / uC G X c y := by
  have hu := uC_pos G X Y c hpos hy
  unfold ZR
  rw [eq_div_iff hu.ne', add_mul, div_mul_cancel₀ _ hu.ne']
  unfold uC; ring

lemma red_ZR (hpos : ∀ y ∈ Y, c < colDensity G X y) (i : V) {y : V} (hy : y ∈ Y) (q : ℝ) :
    (1 - q) - q * ZR G B X c i y = ((1 - q) * (colDensity G X y - c) -
      q * (colDensity G (graphNbhd B X i) y - colDensity G X y)) / uC G X c y := by
  have hu := uC_pos G X Y c hpos hy
  unfold ZR
  rw [eq_div_iff hu.ne', sub_mul, mul_assoc, div_mul_cancel₀ _ hu.ne']
  unfold uC; ring

lemma blue_sum (hpos : ∀ y ∈ Y, c < colDensity G X y) (i : V) :
    ∑ y ∈ Y, nuW G X Y c s y * (max (1 + ZR G B X c i y) 0) ^ s =
      colMomentSum G (graphNbhd B X i) Y c s / colMomentSum G X Y c s := by
  rw [show colMomentSum G (graphNbhd B X i) Y c s =
    ∑ y ∈ Y, (max (colDensity G (graphNbhd B X i) y - c) 0) ^ s from rfl, Finset.sum_div]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [one_add_ZR G B X Y c hpos i hy, nuW]
  exact nu_clip (uC_pos G X Y c hpos hy)

lemma red_sum (hpos : ∀ y ∈ Y, c < colDensity G X y) (i : V) (q : ℝ) :
    ∑ y ∈ Y.filter (fun y => G.Adj i y), nuW G X Y c s y * (max ((1 - q) - q * ZR G B X c i y) 0) ^ s =
      (∑ y ∈ Y.filter (fun y => G.Adj i y), (max ((1 - q) * (colDensity G X y - c) -
        q * (colDensity G (graphNbhd B X i) y - colDensity G X y)) 0) ^ s) /
        colMomentSum G X Y c s := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy' := (Finset.mem_filter.1 hy).1
  rw [red_ZR G B X Y c hpos i hy' q, nuW]
  exact nu_clip (uC_pos G X Y c hpos hy')

lemma nu_split (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (i : V) :
    mr G X Y c s i + ∑ y ∈ Y.filter (fun y => ¬ G.Adj i y), nuW G X Y c s y = 1 := by
  unfold mr; rw [Finset.sum_filter_add_sum_filter_not, nu_sum G X Y c s hY hpos]

lemma mr_nonneg (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (i : V) :
    0 ≤ mr G X Y c s i :=
  Finset.sum_nonneg fun y hy => nu_nonneg G X Y c s hY hpos (Finset.mem_filter.1 hy).1

lemma mr_le_one (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (i : V) :
    mr G X Y c s i ≤ 1 := by
  have := nu_split G X Y c s hY hpos i
  have : 0 ≤ ∑ y ∈ Y.filter (fun y => ¬ G.Adj i y), nuW G X Y c s y :=
    Finset.sum_nonneg fun y hy => nu_nonneg G X Y c s hY hpos (Finset.mem_filter.1 hy).1
  linarith

lemma blue_lt {μ w β : ℝ} (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (hμ0 : 0 < μ)
    (i : V) (hq0 : 0 < graphFrac B X i)
    (hblue : SharpBlueFailure G B X Y c μ w β s i) :
    ∑ y ∈ Y, nuW G X Y c s y * (max (1 + ZR G B X c i y) 0) ^ s < certU μ w β (graphFrac B X i) := by
  have hS := S_pos G X Y c s hY hpos
  rw [blue_sum G B X Y c s hpos i, div_lt_iff₀ hS]
  have e : (μ / graphFrac B X i) ^ (w * β) = certU μ w β (graphFrac B X i) := by
    unfold certU certB; rw [Real.rpow_def_of_pos (div_pos hμ0 hq0)]; congr 1; ring
  rw [← e]; exact hblue

lemma row_J {μ w β : ℝ} (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (hμ0 : 0 < μ)
    (hs : 1 ≤ s) (i : V) (hq0 : 0 < graphFrac B X i)
    (hblue : SharpBlueFailure G B X Y c μ w β s i) :
    (max (1 + Er G B X Y c s i) 0) ^ s < certU μ w β (graphFrac B X i) := by
  have hJ := cell_jensen Y (nuW G X Y c s) (fun y => 1 + ZR G B X c i y)
    (fun y hy => nu_nonneg G X Y c s hY hpos hy) (by rw [nu_sum G X Y c s hY hpos]; norm_num) hs
  rw [nu_sum G X Y c s hY hpos, div_one, one_mul] at hJ
  have e : ∑ y ∈ Y, nuW G X Y c s y * (1 + ZR G B X c i y) = 1 + Er G B X Y c s i := by
    unfold Er
    rw [show (∑ y ∈ Y, nuW G X Y c s y * (1 + ZR G B X c i y)) = ∑ y ∈ Y, nuW G X Y c s y +
        ∑ y ∈ Y, nuW G X Y c s y * ZR G B X c i y by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun y _ => by ring,
      nu_sum G X Y c s hY hpos]
  rw [e] at hJ
  exact lt_of_le_of_lt hJ (blue_lt G B X Y c s hY hpos hμ0 i hq0 hblue)

lemma row_E_le {μ w β r : ℝ} (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y)
    (hμ0 : 0 < μ) (hβ0 : 0 < β) (hr : 0 < r) (hs : 1 ≤ β * r) (i : V) (hq0 : 0 < graphFrac B X i)
    (hblue : SharpBlueFailure G B X Y c μ w β (β * r) i) :
    Er G B X Y c (β * r) i ≤ TF μ w (graphFrac B X i) r - 1 := by
  have hJ := row_J G B X Y c (β * r) hY hpos hμ0 hs i hq0 hblue
  have hs0 : 0 < β * r := by linarith
  have hTF : TF μ w (graphFrac B X i) r ^ (β * r) = certU μ w β (graphFrac B X i) := by
    unfold TF certU; rw [← Real.exp_mul]; congr 1; field_simp
  have hTFp : 0 < TF μ w (graphFrac B X i) r := Real.exp_pos _
  have h : max (1 + Er G B X Y c (β * r) i) 0 < TF μ w (graphFrac B X i) r := by
    rw [← Real.rpow_lt_rpow_iff (le_max_right _ _) hTFp.le hs0, hTF]; exact hJ
  linarith [le_max_left (1 + Er G B X Y c (β * r) i) 0]

lemma row_q0 {w β r x : ℝ} (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (i : V)
    (hq : graphFrac B X i = 0) (hred : SharpRedFailure G B X Y c w β (β * r) x i) :
    mr G X Y c (β * r) i < x ^ β * (rowDensity G i Y) ^ (1 - β) := by
  have hS := S_pos G X Y c (β * r) hY hpos
  unfold SharpRedFailure at hred
  rw [hq] at hred
  simp only [sub_zero, one_mul, zero_mul, Real.one_rpow] at hred
  have e : mr G X Y c (β * r) i = (∑ y ∈ Y.filter (fun y => G.Adj i y),
      (max (colDensity G X y - c) 0) ^ (β * r)) / colMomentSum G X Y c (β * r) := by
    unfold mr nuW
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' := (Finset.mem_filter.1 hy).1
    rw [max_eq_left (by linarith [hpos y hy'])]
    rfl
  rw [e, div_lt_iff₀ hS]
  exact hred

theorem row_RB {μ w β x r : ℝ} (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y)
    (hβ0 : 0 < β) (hr : 0 < r) (hs1 : 1 ≤ β * r) (hμ0 : 0 < μ) (hx0 : 0 < x)
    (i : V) (hq0 : 0 < graphFrac B X i) (hq1 : graphFrac B X i < 1)
    (hm0 : 0 < mr G X Y c (β * r) i) (hπ0 : 0 < rowDensity G i Y)
    (hblue : SharpBlueFailure G B X Y c μ w β (β * r) i)
    (hred : SharpRedFailure G B X Y c w β (β * r) x i) :
    RowBound μ w β x (graphFrac B X i) (mr G X Y c (β * r) i) (rowDensity G i Y) r
      (Er G B X Y c (β * r) i) := by
  have hS := S_pos G X Y c (β * r) hY hpos
  have hsplit := nu_split G X Y c (β * r) hY hpos i
  have hm1 := mr_le_one G X Y c (β * r) hY hpos i
  have hνR : ∀ y ∈ Y.filter (fun y => G.Adj i y), 0 ≤ nuW G X Y c (β * r) y :=
    fun y hy => nu_nonneg G X Y c (β * r) hY hpos (Finset.mem_filter.1 hy).1
  have hνB : ∀ y ∈ Y.filter (fun y => ¬ G.Adj i y), 0 ≤ nuW G X Y c (β * r) y :=
    fun y hy => nu_nonneg G X Y c (β * r) hY hpos (Finset.mem_filter.1 hy).1
  obtain ⟨m, hm⟩ : ∃ m, m = mr G X Y c (β * r) i := ⟨_, rfl⟩
  obtain ⟨AR, hAR⟩ : ∃ A, A = ∑ y ∈ Y.filter (fun y => G.Adj i y),
      nuW G X Y c (β * r) y * ZR G B X c i y := ⟨_, rfl⟩
  obtain ⟨AB, hAB⟩ : ∃ A, A = ∑ y ∈ Y.filter (fun y => ¬ G.Adj i y),
      nuW G X Y c (β * r) y * ZR G B X c i y := ⟨_, rfl⟩
  have hTR : ∑ y ∈ Y.filter (fun y => G.Adj i y), nuW G X Y c (β * r) y = m := by rw [hm]; rfl
  have hTB : ∑ y ∈ Y.filter (fun y => ¬ G.Adj i y), nuW G X Y c (β * r) y = 1 - m := by
    rw [hm]; linarith
  rw [← hm] at hm0 hm1 ⊢
  have hEs : Er G B X Y c (β * r) i = AR + AB := by
    unfold Er; rw [hAR, hAB, Finset.sum_filter_add_sum_filter_not]
  have hABm : (1 - m) * (AB / (1 - m)) = AB := by
    by_cases h : 1 - m = 0
    · have hTBe : Y.filter (fun y => ¬ G.Adj i y) = ∅ := by
        by_contra hne
        have := Finset.sum_pos
          (fun y hy => nu_pos G X Y c (β * r) hY hpos (Finset.mem_filter.1 hy).1)
          (Finset.nonempty_iff_ne_empty.2 hne)
        linarith
      rw [hAB, hTBe, Finset.sum_empty]; simp
    · field_simp
  have hmAR : m * (AR / m) = AR := by field_simp
  apply rowbound_of_cells (zin := AR / m) (zout := AB / (1 - m)) hβ0 hr hs1 hq0 hq1 hm0 hm1 hπ0 hx0
  · rw [hEs, hmAR, hABm]
  · exact row_J G B X Y c (β * r) hY hpos hμ0 hs1 i hq0 hblue
  · have hJ := cell_jensen _ (nuW G X Y c (β * r))
      (fun y => (1 - graphFrac B X i) - graphFrac B X i * ZR G B X c i y) hνR
      (by rw [hTR]; exact hm0) hs1
    rw [hTR, red_sum G B X Y c (β * r) hpos i] at hJ
    have e1 : (∑ y ∈ Y.filter (fun y => G.Adj i y), nuW G X Y c (β * r) y *
        ((1 - graphFrac B X i) - graphFrac B X i * ZR G B X c i y)) / m =
        (1 - graphFrac B X i) - graphFrac B X i * (AR / m) := by
      rw [show (∑ y ∈ Y.filter (fun y => G.Adj i y), nuW G X Y c (β * r) y *
          ((1 - graphFrac B X i) - graphFrac B X i * ZR G B X c i y)) =
          (1 - graphFrac B X i) * m - graphFrac B X i * AR by
        rw [← hTR, hAR, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring]
      field_simp
    rw [e1] at hJ
    unfold SharpRedFailure at hred
    have h2 := (div_lt_iff₀ hS).2 hred
    linarith
  · have hJR := cell_jensen _ (nuW G X Y c (β * r)) (fun y => 1 + ZR G B X c i y) hνR
      (by rw [hTR]; exact hm0) hs1
    rw [hTR] at hJR
    have e2 : (∑ y ∈ Y.filter (fun y => G.Adj i y), nuW G X Y c (β * r) y *
        (1 + ZR G B X c i y)) / m = 1 + AR / m := by
      rw [show (∑ y ∈ Y.filter (fun y => G.Adj i y), nuW G X Y c (β * r) y *
          (1 + ZR G B X c i y)) = m + AR by
        rw [← hTR, hAR, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring]
      field_simp
    rw [e2] at hJR
    have hJB : (1 - m) * (max (1 + AB / (1 - m)) 0) ^ (β * r) ≤
        ∑ y ∈ Y.filter (fun y => ¬ G.Adj i y), nuW G X Y c (β * r) y *
          (max (1 + ZR G B X c i y) 0) ^ (β * r) := by
      by_cases h : 1 - m = 0
      · rw [h, zero_mul]
        exact Finset.sum_nonneg fun y hy =>
          mul_nonneg (hνB y hy) (Real.rpow_nonneg (le_max_right _ _) _)
      · have hpos' : 0 < 1 - m := lt_of_le_of_ne (by linarith) (Ne.symm h)
        have hJ := cell_jensen _ (nuW G X Y c (β * r)) (fun y => 1 + ZR G B X c i y) hνB
          (by rw [hTB]; exact hpos') hs1
        rw [hTB] at hJ
        have e3 : (∑ y ∈ Y.filter (fun y => ¬ G.Adj i y), nuW G X Y c (β * r) y *
            (1 + ZR G B X c i y)) / (1 - m) = 1 + AB / (1 - m) := by
          rw [show (∑ y ∈ Y.filter (fun y => ¬ G.Adj i y), nuW G X Y c (β * r) y *
              (1 + ZR G B X c i y)) = (1 - m) + AB by
            rw [← hTB, hAB, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun y _ => by ring]
          field_simp
        rw [e3] at hJ; exact hJ
    have hbl := blue_lt G B X Y c (β * r) hY hpos hμ0 i hq0 hblue
    rw [← Finset.sum_filter_add_sum_filter_not Y (fun y => G.Adj i y)] at hbl
    linarith

end rows

end DiagRamsey.SE
