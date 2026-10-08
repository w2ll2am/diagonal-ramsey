import Mathlib
import Lemmas.DiagRamsey_SE_GraphRows
import Lemmas.DiagRamsey_closure_wgp

open Classical

namespace DiagRamsey.SE

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma markov_card {ι : Type*} (A : Finset ι) (D : ι → ℝ) (hD : ∀ i ∈ A, 0 ≤ D i) (t : ℝ)
    (ht : 0 < t) : ((A.filter (fun i => t < D i)).card : ℝ) ≤ (∑ i ∈ A, D i) / t := by
  rw [le_div_iff₀ ht]
  calc ((A.filter (fun i => t < D i)).card : ℝ) * t = ∑ i ∈ A.filter (fun i => t < D i), t := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ A.filter (fun i => t < D i), D i :=
        Finset.sum_le_sum fun i hi => (Finset.mem_filter.1 hi).2.le
    _ ≤ ∑ i ∈ A, D i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i hi _ => hD i hi)

lemma card_good {ι : Type*} [DecidableEq ι] (X Xg : Finset ι) (hXg : Xg ⊆ X) (P Q : ι → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (X.card : ℝ) - ((Xg.filter (fun i => P i ∧ Q i)).card : ℝ) ≤
      ((X.card : ℝ) - Xg.card) + ((X.filter (fun i => ¬ P i)).card : ℝ) +
        ((X.filter (fun i => ¬ Q i)).card : ℝ) := by
  have h2 : Xg ⊆ Xg.filter (fun i => P i ∧ Q i) ∪
      (X.filter (fun i => ¬ P i) ∪ X.filter (fun i => ¬ Q i)) := by
    intro i hi
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_filter]
    have := hXg hi
    tauto
  have h3 := Finset.card_le_card h2
  have h4 := Finset.card_union_le (Xg.filter (fun i => P i ∧ Q i))
    (X.filter (fun i => ¬ P i) ∪ X.filter (fun i => ¬ Q i))
  have h4' := Finset.card_union_le (X.filter (fun i => ¬ P i)) (X.filter (fun i => ¬ Q i))
  have h5 : Xg.card ≤ (Xg.filter (fun i => P i ∧ Q i)).card + (X.filter (fun i => ¬ P i)).card +
      (X.filter (fun i => ¬ Q i)).card := by omega
  have h6 : (Xg.card : ℝ) ≤ ((Xg.filter (fun i => P i ∧ Q i)).card : ℝ) +
      ((X.filter (fun i => ¬ P i)).card : ℝ) + ((X.filter (fun i => ¬ Q i)).card : ℝ) := by
    exact_mod_cast h5
  linarith

lemma frac_le_one (A : Finset V) (p : V → Prop) [DecidablePred p] :
    ((A.filter p).card : ℝ) / A.card ≤ 1 := by
  rcases Nat.eq_zero_or_pos A.card with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast Finset.card_filter_le A p

lemma frac_nonneg (A : Finset V) (p : V → Prop) [DecidablePred p] :
    0 ≤ ((A.filter p).card : ℝ) / A.card := by positivity

lemma theta_tend {β κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) :
    ∃ R > 0, ∀ r ≥ R, 1 - (1 - β) ^ (1 / (β * r)) ≤ κ := by
  set L := Real.log (1 - β)
  have hL : L < 0 := Real.log_neg (by linarith) (by linarith)
  refine ⟨max 1 (-L / (β * κ)), by positivity, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hr2 : -L / (β * κ) ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : 0 < r := by linarith
  have hβr : 0 < β * r := by positivity
  have h1 : 1 + L * (1 / (β * r)) ≤ (1 - β) ^ (1 / (β * r)) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    linarith [Real.add_one_le_exp (L * (1 / (β * r)))]
  have h2 : -L ≤ κ * (β * r) := by
    rw [div_le_iff₀ (by positivity)] at hr2; linarith
  have h3 : -(L * (1 / (β * r))) ≤ κ := by
    rw [mul_one_div, ← neg_div, div_le_iff₀ hβr]; exact h2
  linarith

lemma tail_tend {β ε κ : ℝ} (hβ1 : β < 1) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ R > 0, ∀ r ≥ R, (1 + ε) ^ (β * r - r) ≤ κ := by
  set ℓ := Real.log (1 + ε)
  have hℓ : 0 < ℓ := Real.log_pos (by linarith)
  have hb : 0 < 1 - β := by linarith
  refine ⟨1 / (κ * (1 - β) * ℓ) + 1, by positivity, fun r hr => ?_⟩
  have hr0 : 0 < r := by
    have : 0 < 1 / (κ * (1 - β) * ℓ) := by positivity
    linarith
  set x := (1 - β) * r * ℓ with hx
  have hx0 : 0 < x := by positivity
  have hxκ : 1 / κ ≤ x := by
    have h1 : 1 / (κ * (1 - β) * ℓ) ≤ r := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ hκ, hx]; nlinarith
  have e : (1 + ε) ^ (β * r - r) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos (by linarith), hx]; congr 1; ring
  rw [e]
  have h1 : x < Real.exp x := by linarith [Real.add_one_le_exp x]
  have h2 : Real.exp (-x) = 1 / Real.exp x := by rw [Real.exp_neg, one_div]
  rw [h2, div_le_iff₀ (Real.exp_pos x)]
  have : 1 ≤ κ * x := by rw [div_le_iff₀ hκ] at hxκ; linarith
  nlinarith

section conc

variable (G B : SimpleGraph V) (X Y : Finset V) (c s : ℝ)

lemma H_def : momentNorm G X Y c s = (colMomentSum G X Y c s / Y.card) ^ (1 / s) := rfl

lemma H_pos (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) :
    0 < momentNorm G X Y c s := by
  rw [H_def]
  exact Real.rpow_pos_of_pos (div_pos (S_pos G X Y c s hY hpos) (by exact_mod_cast hY.card_pos)) _

lemma H_pow (hs : 0 < s) : momentNorm G X Y c s ^ s = colMomentSum G X Y c s / Y.card := by
  rw [H_def, ← Real.rpow_mul (div_nonneg (cms_nonneg G Y c s X) (Nat.cast_nonneg _)),
    one_div_mul_cancel hs.ne', Real.rpow_one]

lemma H_le_one (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (hc : 0 ≤ c)
    (hs : 0 < s) : momentNorm G X Y c s ≤ 1 := by
  rw [H_def]
  apply Real.rpow_le_one (div_nonneg (cms_nonneg G Y c s X) (Nat.cast_nonneg _)) _ (by positivity)
  have hM : (0:ℝ) < Y.card := by exact_mod_cast hY.card_pos
  rw [div_le_one hM, S_eq G X Y c s hpos]
  calc ∑ y ∈ Y, uC G X c y ^ s ≤ ∑ y ∈ Y, (1:ℝ) := Finset.sum_le_sum fun y hy => by
        have hu := uC_pos G X Y c hpos hy
        have : uC G X c y ≤ 1 := by
          unfold uC
          have := frac_le_one (X) (fun v => G.Adj v y)
          unfold colDensity; linarith
        exact Real.rpow_le_one hu.le this hs.le
    _ = Y.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

lemma crop (w r : ℝ) (hX : X.Nonempty) (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y)
    (hs : 0 < s) (hsr : s < r)
    (hcol : ∀ Y' : Finset V, Y' ⊆ Y → Y'.Nonempty →
      potential G X Y' c w r s ≤ potential G X Y c w r s)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∑ y ∈ Y.filter (fun y => (1 + ε) * momentNorm G X Y c s < uC G X c y), nuW G X Y c s y ≤
      (1 + ε) ^ (s - r) := by
  have hHp := H_pos G X Y c s hY hpos
  have hHs := H_pow G X Y c s hs
  set H := momentNorm G X Y c s with hHdef
  set T := Y.filter (fun y => (1 + ε) * H < uC G X c y) with hT
  have hS := S_pos G X Y c s hY hpos
  have hM : (0:ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hN : (0:ℝ) < X.card := by exact_mod_cast hX.card_pos
  rcases T.eq_empty_or_nonempty with hTe | hTn
  · rw [hTe, Finset.sum_empty]; exact Real.rpow_nonneg (by linarith) _
  have hTY : T ⊆ Y := Finset.filter_subset _ _
  have hposT : ∀ y ∈ T, c < colDensity G X y := fun y hy => hpos y (hTY hy)
  have hTc : (0:ℝ) < T.card := by exact_mod_cast hTn.card_pos
  have hS' := S_pos G X T c s hTn hposT
  have hsum : ∑ y ∈ T, nuW G X Y c s y = colMomentSum G X T c s / colMomentSum G X Y c s := by
    unfold nuW; rw [← Finset.sum_div, S_eq G X T c s hposT]
  rw [hsum]
  have hpot := hcol T hTY hTn
  unfold potential at hpot
  rw [H_def G X T, H_def G X Y, ← Real.rpow_mul (div_nonneg hS'.le hTc.le),
    ← Real.rpow_mul (div_nonneg hS.le hM.le), one_div_mul_eq_div] at hpot
  have hNw : 0 < (X.card : ℝ) ^ w := Real.rpow_pos_of_pos hN _
  rw [mul_assoc, mul_assoc] at hpot
  have h1 := le_of_mul_le_mul_left hpot hNw
  set k := r / s with hk
  have hk1 : 1 < k := (one_lt_div hs).2 hsr
  obtain ⟨A, hA⟩ : ∃ A, A = colMomentSum G X T c s / T.card := ⟨_, rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ B, B = colMomentSum G X Y c s / Y.card := ⟨_, rfl⟩
  rw [← hA, ← hBm] at h1
  have hA0 : 0 < A := by rw [hA]; exact div_pos hS' hTc
  have hB0 : 0 < Bm := by rw [hBm]; exact div_pos hS hM
  have hAB : (1 + ε) ^ s * Bm ≤ A := by
    rw [hA, hBm, ← hHs, le_div_iff₀ hTc, S_eq G X T c s hposT]
    have : ∀ y ∈ T, (1 + ε) ^ s * H ^ s ≤ uC G X c y ^ s := by
      intro y hy
      have hy' := (Finset.mem_filter.1 hy).2
      rw [← Real.mul_rpow (by linarith) hHp.le]
      exact Real.rpow_le_rpow (by positivity) hy'.le hs.le
    have h := Finset.card_nsmul_le_sum T (fun y => uC G X c y ^ s) _ this
    rw [nsmul_eq_mul] at h
    linarith
  obtain ⟨lam, hlam⟩ : ∃ l, l = A / Bm := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; exact div_pos hA0 hB0
  have hlam1 : (1 + ε) ^ s ≤ lam := by rw [hlam, le_div_iff₀ hB0]; exact hAB
  have hAl : A = lam * Bm := by rw [hlam]; field_simp
  have h2 : (T.card : ℝ) * lam ^ k ≤ Y.card := by
    rw [hAl, Real.mul_rpow hlam0.le hB0.le] at h1
    have hBk : 0 < Bm ^ k := Real.rpow_pos_of_pos hB0 _
    have : ((T.card : ℝ) * lam ^ k) * Bm ^ k ≤ (Y.card : ℝ) * Bm ^ k := by linarith
    exact le_of_mul_le_mul_right this hBk
  have e1 : colMomentSum G X T c s / colMomentSum G X Y c s = T.card * lam / Y.card := by
    have e2 : colMomentSum G X T c s = T.card * A := by
      rw [mul_comm]; exact ((eq_div_iff hTc.ne').1 hA).symm
    have e3 : colMomentSum G X Y c s = Y.card * Bm := by
      rw [mul_comm]; exact ((eq_div_iff hM.ne').1 hBm).symm
    rw [e2, e3, hAl, ← mul_assoc, mul_div_mul_right _ _ hB0.ne']
  rw [e1]
  have hlk : 0 < lam ^ k := Real.rpow_pos_of_pos hlam0 _
  have h3 : (T.card : ℝ) * lam / Y.card ≤ lam ^ (1 - k) := by
    rw [Real.rpow_sub hlam0, Real.rpow_one, div_le_div_iff₀ hM hlk]
    nlinarith
  have h4 : lam ^ (1 - k) ≤ ((1 + ε) ^ s) ^ (1 - k) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hlam1 (by linarith)
  have h5 : ((1 + ε) ^ s) ^ (1 - k) = (1 + ε) ^ (s - r) := by
    rw [← Real.rpow_mul (by linarith)]; congr 1; rw [hk]; field_simp
  linarith

lemma rho_bound (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (H θ ε : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hε : 0 ≤ ε) (hH : 0 < H)
    (hlow : ∀ y ∈ Y, θ * H ≤ uC G X c y) :
    ∑ y ∈ Y, nuW G X Y c s y * |1 - H / uC G X c y| ≤
      ε + (1 / θ - 1) + ∑ y ∈ Y.filter (fun y => (1 + ε) * H < uC G X c y), nuW G X Y c s y := by
  have hθ' : 0 ≤ 1 / θ - 1 := by rw [sub_nonneg, le_div_iff₀ hθ0]; linarith
  have e : ε + (1 / θ - 1) + ∑ y ∈ Y.filter (fun y => (1 + ε) * H < uC G X c y), nuW G X Y c s y =
      ∑ y ∈ Y, (nuW G X Y c s y * (ε + (1 / θ - 1)) +
        if (1 + ε) * H < uC G X c y then nuW G X Y c s y else 0) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, nu_sum G X Y c s hY hpos, one_mul,
      Finset.sum_filter]
  rw [e]
  refine Finset.sum_le_sum fun y hy => ?_
  have hν := nu_nonneg G X Y c s hY hpos hy
  have hu := uC_pos G X Y c hpos hy
  have hHu : H / uC G X c y ≤ 1 / θ := by
    rw [div_le_div_iff₀ hu hθ0]; nlinarith [hlow y hy]
  have hHu0 : 0 < H / uC G X c y := div_pos hH hu
  split_ifs with ht
  · have : |1 - H / uC G X c y| ≤ ε + (1 / θ - 1) + 1 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith
  · push_neg at ht
    have hlo : 1 - ε ≤ H / uC G X c y := by
      rw [le_div_iff₀ hu]
      rcases le_total ε 1 with h | h
      · nlinarith [mul_le_mul_of_nonneg_left ht (sub_nonneg.2 h), mul_nonneg (sq_nonneg ε) hH.le]
      · nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : 1 - ε ≤ 0) hu.le]
    have : |1 - H / uC G X c y| ≤ ε + (1 / θ - 1) := by
      rw [abs_le]; constructor <;> linarith
    nlinarith

lemma m_point (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y) (H : ℝ) (hH : 0 ≤ H)
    (i : V) :
    |mr G X Y c s i - (c + H)| ≤
      (1 + |c|) * ∑ y ∈ Y, nuW G X Y c s y * |1 - H / uC G X c y| +
        H * |Vr G X Y c s i - 1| := by
  set ρ := ∑ y ∈ Y, nuW G X Y c s y * |1 - H / uC G X c y|
  have hm : mr G X Y c s i = ∑ y ∈ Y, nuW G X Y c s y * hR G i y := by
    unfold mr hR
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
  have hHV : H * Vr G X Y c s i = ∑ y ∈ Y, nuW G X Y c s y * (hR G i y - c) * (H / uC G X c y) := by
    unfold Vr
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← nu_mul G X Y c s hpos hy]
    ring
  set A := ∑ y ∈ Y, nuW G X Y c s y * hR G i y * (1 - H / uC G X c y)
  set C := ∑ y ∈ Y, nuW G X Y c s y * (1 - H / uC G X c y)
  have e1 : ∑ y ∈ Y, (nuW G X Y c s y * hR G i y * (1 - H / uC G X c y) +
      nuW G X Y c s y * (hR G i y - c) * (H / uC G X c y) -
      c * (nuW G X Y c s y * (1 - H / uC G X c y))) =
      ∑ y ∈ Y, nuW G X Y c s y * hR G i y - c * ∑ y ∈ Y, nuW G X Y c s y := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    nu_sum G X Y c s hY hpos, ← hHV, ← hm] at e1
  have key : mr G X Y c s i - (c + H) = A + H * (Vr G X Y c s i - 1) - c * C := by linarith
  have hA : |A| ≤ ρ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
    have hν := nu_nonneg G X Y c s hY hpos hy
    have hh : |hR G i y| ≤ 1 := by unfold hR; split_ifs <;> simp
    rw [abs_mul, abs_mul, abs_of_nonneg hν]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hν hh) (abs_nonneg _)
  have hC : |C| ≤ ρ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
    rw [abs_mul, abs_of_nonneg (nu_nonneg G X Y c s hY hpos hy)]
  rw [key]
  calc |A + H * (Vr G X Y c s i - 1) - c * C| ≤ |A| + H * |Vr G X Y c s i - 1| + |c| * |C| := by
        have := abs_sub (A + H * (Vr G X Y c s i - 1)) (c * C)
        have h2 := abs_add_le A (H * (Vr G X Y c s i - 1))
        rw [abs_mul H, abs_of_nonneg hH] at h2
        rw [abs_mul] at this
        linarith
    _ ≤ ρ + H * |Vr G X Y c s i - 1| + |c| * ρ := by
        have := mul_le_mul_of_nonneg_left hC (abs_nonneg c); linarith
    _ = _ := by ring

lemma L1_V (w r : ℝ) (hX : X.Nonempty) (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y)
    (hr : 0 < r) (hs : 1 ≤ s) (hw : 0 ≤ w) (hwr : w ≤ r)
    (hrow : ∀ X' : Finset V, X' ⊆ X → X'.Nonempty →
      potential G X' Y c w r s ≤ potential G X Y c w r s) :
    ∑ i ∈ X, |Vr G X Y c s i - 1| ≤ 2 * (w / r) * X.card := by
  have hsum := sumV G X Y c s hX hY hpos
  have hwr0 : 0 ≤ w / r := div_nonneg hw hr.le
  have h : ∀ i ∈ X, |Vr G X Y c s i - 1| ≤ (Vr G X Y c s i - 1) + 2 * (w / r) := by
    intro i hi
    have := Vlow G X Y c s w r hX hY hpos hr hs hw hwr hrow i hi
    rcases le_total 0 (Vr G X Y c s i - 1) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  calc ∑ i ∈ X, |Vr G X Y c s i - 1| ≤ ∑ i ∈ X, ((Vr G X Y c s i - 1) + 2 * (w / r)) :=
        Finset.sum_le_sum h
    _ = 2 * (w / r) * X.card := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, Finset.sum_const,
          Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring

lemma L1_pi (w r θ : ℝ) (hw : 0 < w) (hwr : w < r) (hs : 1 ≤ s) (hX : X.Nonempty)
    (hY : Y.Nonempty) (hpos : ∀ y ∈ Y, c < colDensity G X y)
    (hlow : ∀ y ∈ Y, θ * momentNorm G X Y c s ≤ uC G X c y)
    (hrow : ∀ X' : Finset V, X' ⊆ X → X'.Nonempty →
      potential G X' Y c w r s ≤ potential G X Y c w r s) :
    ∑ i ∈ X, |rowDensity G i Y - (c + momentNorm G X Y c s)| ≤
      X.card * ((1 - θ) * momentNorm G X Y c s + 2 * (w / r) * momentNorm G X Y c s) := by
  have hH := H_pos G X Y c s hY hpos
  have hex := DiagRamsey.ClosureEnv.wgp_row_excess G X Y c w r s hw hwr hs hY hH hrow
  have havg := DiagRamsey.ClosureEnv.wgp_avg_eq G X Y hX hY
  set H := momentNorm G X Y c s
  have hM : (0:ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hN : (0:ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hg : (Y.card : ℝ) * (c + θ * H) ≤ ∑ y ∈ Y, colDensity G X y := by
    calc (Y.card : ℝ) * (c + θ * H) = ∑ y ∈ Y, (c + θ * H) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ Y, colDensity G X y := Finset.sum_le_sum fun y hy => by
          have := hlow y hy; unfold uC at this; linarith
  have hπ : (X.card : ℝ) * (c + θ * H) ≤ ∑ i ∈ X, rowDensity G i Y := by
    have e : ∑ i ∈ X, rowDensity G i Y = X.card * ((∑ y ∈ Y, colDensity G X y) / Y.card) := by
      rw [havg]; field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hN.le
    rw [le_div_iff₀ hM]; linarith
  have habs : ∀ e : ℝ, |e| ≤ 2 * max e 0 - e := fun e => by
    rcases le_total 0 e with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; linarith
    · rw [abs_of_nonpos h, max_eq_right h]; linarith
  have h1 : ∑ i ∈ X, |rowDensity G i Y - (c + H)| ≤
      ∑ i ∈ X, (2 * max (rowDensity G i Y - c - H) 0 - (rowDensity G i Y - c - H)) :=
    Finset.sum_le_sum fun i _ => by rw [sub_add_eq_sub_sub]; exact habs _
  have h2 : ∑ i ∈ X, (2 * max (rowDensity G i Y - c - H) 0 - (rowDensity G i Y - c - H)) =
      2 * ∑ i ∈ X, max (rowDensity G i Y - c - H) 0 - ∑ i ∈ X, rowDensity G i Y +
        X.card * c + X.card * H := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [h2] at h1
  nlinarith

end conc

end DiagRamsey.SE
