import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Definitions.Def_DiagRamsey_NestedMoment
import Definitions.Def_DiagRamsey_WeightedHost

/-! Verbatim copy of the proof in `Solutions/Sol_DiagRamsey_weighted_good_pages.lean` (verified, no sorryAx),
moved to the namespace `DiagRamsey.ClosureEnv` and renamed `cl_weighted_good_pages`, so that it can be imported
alongside the `Theorems` stub `DiagRamsey.weighted_good_pages`. -/

namespace DiagRamsey.ClosureEnv

/-- The potential written through the column sum. -/
lemma wgp_nestedPot_eq {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (X A : Finset V)
    (w r s c : ℝ) :
    nestedPot G w r s c X A = (X.card : ℝ) ^ w * (A.card : ℝ) *
      ((∑ y ∈ A, (max (redDens G X y - c) 0) ^ s) / A.card) ^ (r / s) := rfl

/-- Positivity of the parent potential: `|X|^w > 0`, `|Y| > 0`, positive clipped moment. -/
lemma wgp_pos_parts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (w r s c : ℝ) (hrs : 0 < r / s) (hpos : 0 < nestedPot G w r s c X Y) :
    0 < (X.card : ℝ) ^ w ∧ 0 < (Y.card : ℝ) ∧ 0 < clippedMoment G X Y c s := by
  unfold nestedPot at hpos
  have hm0 : 0 ≤ clippedMoment G X Y c s := by
    unfold clippedMoment
    exact div_nonneg (Finset.sum_nonneg (fun y _ => Real.rpow_nonneg (le_max_right _ _) s))
      (Nat.cast_nonneg _)
  have hXw : 0 ≤ (X.card : ℝ) ^ w := Real.rpow_nonneg (Nat.cast_nonneg _) w
  have hY0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · rcases hXw.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  · rcases hY0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hpos; simp at hpos
  · rcases hm0.lt_or_eq with h | h
    · exact h
    · rw [← h, Real.zero_rpow hrs.ne'] at hpos; simp at hpos

/-- The crop inequality: `S(A)/|A| ≤ (|Y|/|A|)^(s/r) * (S(Y)/|Y|)` for nonempty `A ⊆ Y`. -/
lemma wgp_crop_le {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V)
    (w r s c : ℝ) (hs : 0 < s) (hsr : s < r)
    (hpos : 0 < nestedPot G w r s c X Y)
    (hmax : ∀ A ⊆ Y, A.Nonempty → nestedPot G w r s c X A ≤ nestedPot G w r s c X Y)
    (A : Finset V) (hA : A ⊆ Y) (hAne : A.Nonempty) :
    clippedMoment G X A c s ≤ ((Y.card : ℝ) / A.card) ^ (s / r) * clippedMoment G X Y c s := by
  have hr : 0 < r := lt_trans hs hsr
  have hrs : 0 < r / s := div_pos hr hs
  obtain ⟨hXw, hY, hm⟩ := wgp_pos_parts G X Y w r s c hrs hpos
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hmA : 0 ≤ clippedMoment G X A c s := by
    unfold clippedMoment
    exact div_nonneg (Finset.sum_nonneg (fun y _ => Real.rpow_nonneg (le_max_right _ _) s))
      (Nat.cast_nonneg _)
  have h1 := hmax A hA hAne
  unfold nestedPot at h1
  -- cancel |X|^w and divide by |A|
  have h2 : (clippedMoment G X A c s) ^ (r / s) ≤
      ((Y.card : ℝ) / A.card) * (clippedMoment G X Y c s) ^ (r / s) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hAc]
    have := (mul_le_mul_iff_of_pos_left hXw).mp (by
      calc (X.card : ℝ) ^ w * ((A.card : ℝ) * (clippedMoment G X A c s) ^ (r / s))
          = (X.card : ℝ) ^ w * A.card * (clippedMoment G X A c s) ^ (r / s) := by ring
        _ ≤ (X.card : ℝ) ^ w * Y.card * (clippedMoment G X Y c s) ^ (r / s) := h1
        _ = (X.card : ℝ) ^ w * ((Y.card : ℝ) * (clippedMoment G X Y c s) ^ (r / s)) := by ring)
    linarith
  -- take the (s/r)-th power
  have h3 := Real.rpow_le_rpow (Real.rpow_nonneg hmA _) h2 (div_pos hs hr).le
  rw [← Real.rpow_mul hmA, Real.mul_rpow (div_nonneg hY.le hAc.le) (Real.rpow_nonneg hm.le _),
    ← Real.rpow_mul hm.le] at h3
  have he : r / s * (s / r) = 1 := by field_simp
  rwa [he, Real.rpow_one, Real.rpow_one] at h3

lemma wgp_col_singleton {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (w r s c : ℝ) (hs : 0 < s) (hsr : s < r)
    (hpos : 0 < nestedPot G w r s c X Y)
    (hmax : ∀ A ⊆ Y, A.Nonempty → nestedPot G w r s c X A ≤ nestedPot G w r s c X Y) :
    ∀ y ∈ Y, (1 - s / r) * clippedMoment G X Y c s ≤ (max (redDens G X y - c) 0) ^ s ∧
      c < redDens G X y := by
  classical
  intro y hy
  have hr : 0 < r := lt_trans hs hsr
  have hrs : 0 < r / s := div_pos hr hs
  obtain ⟨_, hY, hm⟩ := wgp_pos_parts G X Y w r s c hrs hpos
  have hsr1 : s / r < 1 := (div_lt_one hr).mpr hsr
  have hsr0 : 0 < s / r := div_pos hs hr
  set θ := 1 - s / r with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  set m := clippedMoment G X Y c s with hmdef
  set z := max (redDens G X y - c) 0 with hzdef
  set S := ∑ y ∈ Y, (max (redDens G X y - c) 0) ^ s with hSdef
  have hSm : S = Y.card * m := by
    rw [hmdef, clippedMoment]; field_simp
    first | rfl | exact hSdef
  have key : θ * m ≤ z ^ s := by
    by_cases hM : Y.card = 1
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hM
      have hya : y = a := by rw [ha] at hy; exact Finset.mem_singleton.mp hy
      have hmz : m = z ^ s := by
        rw [hmdef, clippedMoment, ha, Finset.sum_singleton, Finset.card_singleton, ← hya]; simp [hzdef]
      rw [← hmz]
      nlinarith
    · have hM2 : 2 ≤ Y.card := by
        have : 0 < Y.card := Finset.card_pos.mpr ⟨y, hy⟩
        omega
      set A := Y.erase y with hAdef
      have hAcard : A.card = Y.card - 1 := Finset.card_erase_of_mem hy
      have hAne : A.Nonempty := by rw [← Finset.card_pos, hAcard]; omega
      have hcrop := wgp_crop_le G X Y w r s c hs hsr hpos hmax A (Finset.erase_subset y Y) hAne
      have hAc : (A.card : ℝ) = Y.card - 1 := by
        rw [hAcard, Nat.cast_sub (by omega)]; simp
      have hMr : (2 : ℝ) ≤ Y.card := by exact_mod_cast hM2
      have hmA : clippedMoment G X A c s = (S - z ^ s) / (Y.card - 1) := by
        rw [clippedMoment, hAdef, Finset.sum_erase_eq_sub hy, ← hAdef, hAc]
      rw [hmA, hAc] at hcrop
      set p : ℝ := (Y.card - 1) / Y.card with hpdef
      have hp0 : 0 < p := by rw [hpdef]; apply div_pos <;> linarith
      have hp1 : p ≤ 1 := by rw [hpdef, div_le_one (by linarith)]; linarith
      have hinv : (Y.card : ℝ) / (Y.card - 1) = p⁻¹ := by rw [hpdef, inv_div]
      rw [hinv, Real.inv_rpow hp0.le] at hcrop
      -- S - z^s ≤ M p^θ m
      have h1 : S - z ^ s ≤ Y.card * (p ^ θ * m) := by
        have hden : (0 : ℝ) < Y.card - 1 := by linarith
        rw [div_le_iff₀ hden] at hcrop
        have hpθ : p ^ θ = p / p ^ (s / r) := by
          rw [hθ, Real.rpow_sub hp0, Real.rpow_one]
        rw [hpθ]
        have hps : 0 < p ^ (s / r) := Real.rpow_pos_of_pos hp0 _
        have hM0 : (0 : ℝ) < Y.card := by linarith
        calc S - z ^ s ≤ (p ^ (s / r))⁻¹ * m * (Y.card - 1) := hcrop
          _ = Y.card * (p / p ^ (s / r) * m) := by rw [hpdef]; field_simp
      -- Bernoulli: p^θ ≤ 1 - θ / M
      have hbern : p ^ θ ≤ 1 - θ / Y.card := by
        have hp' : p = 1 + (-(1 / (Y.card : ℝ))) := by rw [hpdef]; field_simp; ring
        have hge : -1 ≤ -(1 / (Y.card : ℝ)) := by
          rw [neg_le_neg_iff, div_le_one (by linarith)]; linarith
        have := rpow_one_add_le_one_add_mul_self hge hθ0.le (by rw [hθ]; linarith)
        rw [hp']
        calc (1 + -(1 / (Y.card : ℝ))) ^ θ ≤ 1 + θ * -(1 / (Y.card : ℝ)) := this
          _ = 1 - θ / Y.card := by ring
      have hM0 : (0 : ℝ) < Y.card := by linarith
      have h2 : Y.card * (p ^ θ * m) ≤ Y.card * ((1 - θ / Y.card) * m) := by
        apply mul_le_mul_of_nonneg_left _ hM0.le
        exact mul_le_mul_of_nonneg_right hbern hm.le
      have h3 : (Y.card : ℝ) * ((1 - θ / Y.card) * m) = S - θ * m := by
        rw [hSm]; field_simp
      linarith
  refine ⟨key, ?_⟩
  have hzs : 0 < z ^ s := lt_of_lt_of_le (mul_pos hθ0 hm) key
  have hz : 0 < z := by
    by_contra hcon
    have hz0 : z = 0 := le_antisymm (not_lt.mp hcon) (le_max_right _ _)
    rw [hz0, Real.zero_rpow hs.ne'] at hzs
    exact lt_irrefl 0 hzs
  rw [hzdef, lt_max_iff] at hz
  rcases hz with h | h
  · linarith
  · exact absurd h (lt_irrefl 0)

section WeightedGoodPages

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted potential agrees with `nestedPot` (classical decidability). -/
lemma wgp_pot_eq (G : SimpleGraph V) (X A : Finset V) (c w r s : ℝ) :
    potential G X A c w r s =
      @nestedPot V G (fun a b => Classical.propDecidable (G.Adj a b)) w r s c X A := by
  unfold potential nestedPot momentNorm clippedMoment
  have h0 : 0 ≤ (∑ y ∈ A, (max (colDensity G X y - c) 0) ^ s) / (A.card : ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun y _ => Real.rpow_nonneg (le_max_right _ _) s))
      (Nat.cast_nonneg _)
  rw [← Real.rpow_mul h0, one_div_mul_eq_div]
  rfl

open Classical in
/-- Double counting of red `A`-`Y` edges. -/
lemma wgp_double_count (G : SimpleGraph V) (A Y : Finset V) :
    ∑ y ∈ Y, ((A.filter (fun v => G.Adj v y)).card : ℝ) =
      ∑ v ∈ A, ((Y.filter (fun y => G.Adj v y)).card : ℝ) := by
  classical
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

lemma wgp_avg_eq (G : SimpleGraph V) (A Y : Finset V) (hA : A.Nonempty) (hY : Y.Nonempty) :
    (∑ y ∈ Y, colDensity G A y) / (Y.card : ℝ) = (∑ v ∈ A, rowDensity G v Y) / (A.card : ℝ) := by
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  unfold colDensity rowDensity
  rw [← Finset.sum_div, ← Finset.sum_div, wgp_double_count]
  field_simp

/-- Column lower bound (C): every column has `g_y - c ≥ (1 - s/r)^(1/s) H`. -/
lemma wgp_col_lower (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) (hs : 0 < s) (hsr : s < r)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hH : 0 < momentNorm G X Y c s)
    (hcol : ∀ Y' : Finset V, Y' ⊆ Y → Y'.Nonempty →
      potential G X Y' c w r s ≤ potential G X Y c w r s) :
    ∀ y ∈ Y, (1 - s / r) ^ (1 / s) * momentNorm G X Y c s ≤ colDensity G X y - c := by
  letI : DecidableRel G.Adj := fun a b => Classical.propDecidable (G.Adj a b)
  have hr : 0 < r := lt_trans hs hsr
  have hm0 : 0 ≤ clippedMoment G X Y c s := by
    unfold clippedMoment
    exact div_nonneg (Finset.sum_nonneg (fun y _ => Real.rpow_nonneg (le_max_right _ _) s))
      (Nat.cast_nonneg _)
  have hHm : momentNorm G X Y c s = clippedMoment G X Y c s ^ (1 / s) := rfl
  have hmpos : 0 < clippedMoment G X Y c s := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · rw [hHm, ← h, Real.zero_rpow (by positivity)] at hH; exact absurd hH (lt_irrefl 0)
  have hpos : 0 < nestedPot G w r s c X Y := by
    unfold nestedPot
    have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos hX0 _) hY0) (Real.rpow_pos_of_pos hmpos _)
  have hmax : ∀ A ⊆ Y, A.Nonempty → nestedPot G w r s c X A ≤ nestedPot G w r s c X Y := by
    intro A hA hAne
    have := hcol A hA hAne
    rwa [wgp_pot_eq, wgp_pot_eq] at this
  intro y hy
  obtain ⟨h1, h2⟩ := wgp_col_singleton G X Y w r s c hs hsr hpos hmax y hy
  have hred : redDens G X y = colDensity G X y := rfl
  rw [hred] at h1 h2
  have hu : 0 < colDensity G X y - c := by linarith
  rw [max_eq_left hu.le] at h1
  have hθ : 0 ≤ 1 - s / r := by rw [sub_nonneg, div_le_one hr]; exact hsr.le
  have h3 := Real.rpow_le_rpow (mul_nonneg hθ hm0) h1 (by positivity : (0:ℝ) ≤ 1 / s)
  rw [Real.mul_rpow hθ hm0, ← Real.rpow_mul hu.le, mul_one_div_cancel hs.ne', Real.rpow_one] at h3
  rw [hHm]; exact h3

/-- Row part: `∑_{v ∈ X} (π_v - c - H)_+ ≤ (w/r) |X| H` (weighted row tail at `t = 1` plus Young). -/
lemma wgp_row_excess (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) (hw : 0 < w) (hwr : w < r)
    (hs1 : 1 ≤ s) (hY : Y.Nonempty) (hH : 0 < momentNorm G X Y c s)
    (hrow : ∀ X' : Finset V, X' ⊆ X → X'.Nonempty →
      potential G X' Y c w r s ≤ potential G X Y c w r s) :
    ∑ v ∈ X, max (rowDensity G v Y - c - momentNorm G X Y c s) 0 ≤
      w / r * X.card * momentNorm G X Y c s := by
  classical
  have hr : 0 < r := lt_trans hw hwr
  have hs : 0 < s := by linarith
  set H := momentNorm G X Y c s with hHdef
  set P := X.filter (fun v => c + H < rowDensity G v Y) with hPdef
  have hsum : ∑ v ∈ X, max (rowDensity G v Y - c - H) 0 = ∑ v ∈ P, (rowDensity G v Y - c - H) := by
    rw [hPdef, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs with h
    · exact max_eq_left (by linarith)
    · exact max_eq_right (by linarith)
  rw [hsum]
  rcases P.eq_empty_or_nonempty with hP | hP
  · rw [hP, Finset.sum_empty]; positivity
  have hPX : P ⊆ X := Finset.filter_subset _ _
  set m : ℝ := (P.card : ℝ) with hmdef
  set N : ℝ := (X.card : ℝ) with hNdef
  have hm : 0 < m := by rw [hmdef]; exact_mod_cast hP.card_pos
  have hmN : m ≤ N := by rw [hmdef, hNdef]; exact_mod_cast Finset.card_le_card hPX
  have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  set T := (∑ v ∈ P, rowDensity G v Y) / m - c with hTdef
  have hsumT : ∑ v ∈ P, (rowDensity G v Y - c - H) = m * T - m * H := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, hTdef]
    field_simp
    ring
  have hTH : H < T := by
    have : ∑ v ∈ P, (c + H) < ∑ v ∈ P, rowDensity G v Y :=
      Finset.sum_lt_sum_of_nonempty hP (fun v hv => (Finset.mem_filter.mp hv).2)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    rw [hTdef, lt_sub_iff_add_lt, lt_div_iff₀ hm]
    linarith
  have hT0 : 0 < T := lt_trans hH hTH
  -- power mean: T ≤ H(P)
  have hTP : T ≤ momentNorm G P Y c s := by
    have havg := wgp_avg_eq G P Y hP hY
    set z : V → ℝ := fun y => max (colDensity G P y - c) 0 with hz
    have hz0 : ∀ y ∈ Y, 0 ≤ z y := fun y _ => le_max_right _ _
    have hTE : T ≤ ∑ y ∈ Y, (1 / (Y.card : ℝ)) * z y := by
      rw [hTdef, ← havg, ← Finset.mul_sum, one_div_mul_eq_div]
      have : ∑ y ∈ Y, colDensity G P y - (Y.card : ℝ) * c ≤ ∑ y ∈ Y, z y := by
        rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_sub_distrib]
        exact Finset.sum_le_sum (fun y _ => le_max_left _ _)
      rw [sub_le_iff_le_add, div_add' _ _ _ hY0.ne', div_le_div_iff_of_pos_right hY0]
      linarith
    have hw1 : ∑ y ∈ Y, (1 / (Y.card : ℝ)) = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]; field_simp
    have hJ := Real.rpow_arith_mean_le_arith_mean_rpow Y (fun _ => 1 / (Y.card : ℝ)) z
      (fun _ _ => by positivity) hw1 hz0 hs1
    have hE0 : 0 ≤ ∑ y ∈ Y, (1 / (Y.card : ℝ)) * z y :=
      Finset.sum_nonneg (fun y hy => mul_nonneg (by positivity) (hz0 y hy))
    have hJ' : ∑ y ∈ Y, (1 / (Y.card : ℝ)) * z y ≤ momentNorm G P Y c s := by
      have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hE0 s) hJ (by positivity : (0:ℝ) ≤ 1 / s)
      rw [← Real.rpow_mul hE0, mul_one_div_cancel hs.ne', Real.rpow_one] at h2
      refine h2.trans (le_of_eq ?_)
      unfold momentNorm
      congr 1
      rw [← Finset.mul_sum, one_div_mul_eq_div]
    linarith
  -- row maximality at P
  have hmaxP := hrow P hPX hP
  unfold potential at hmaxP
  have hPr : T ^ r ≤ (momentNorm G P Y c s) ^ r := Real.rpow_le_rpow hT0.le hTP hr.le
  have h1 : m ^ w * T ^ r ≤ N ^ w * H ^ r := by
    have hmw : 0 < m ^ w := Real.rpow_pos_of_pos hm w
    have := mul_le_mul_of_nonneg_left hPr (mul_nonneg hmw.le hY0.le)
    nlinarith
  -- take r-th roots
  have h2 : m ^ (w / r) * T ≤ N ^ (w / r) * H := by
    have hN : 0 ≤ N := by positivity
    have h3 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0:ℝ) ≤ 1 / r)
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hm.le, ← Real.rpow_mul hT0.le, ← Real.rpow_mul hN, ← Real.rpow_mul hH.le,
      mul_one_div_cancel hr.ne', Real.rpow_one, Real.rpow_one, mul_one_div] at h3
    exact h3
  set θ := w / r with hθdef
  have hθ0 : 0 < θ := div_pos hw hr
  have hθ1 : θ < 1 := (div_lt_one hr).mpr hwr
  have hmT : m * T ≤ N ^ θ * m ^ (1 - θ) * H := by
    have hsplit : m = m ^ (1 - θ) * m ^ θ := by
      rw [← Real.rpow_add hm]; simp
    have hpow : 0 < m ^ (1 - θ) := Real.rpow_pos_of_pos hm _
    calc m * T = m ^ (1 - θ) * (m ^ θ * T) := by
            conv_lhs => rw [hsplit]
            ring
      _ ≤ m ^ (1 - θ) * (N ^ θ * H) := mul_le_mul_of_nonneg_left h2 hpow.le
      _ = N ^ θ * m ^ (1 - θ) * H := by ring
  have hyoung : N ^ θ * m ^ (1 - θ) ≤ θ * N + (1 - θ) * m :=
    Real.geom_mean_le_arith_mean2_weighted hθ0.le (by linarith) (by positivity) hm.le (by ring)
  rw [hsumT]
  have h4 := mul_le_mul_of_nonneg_right hyoung hH.le
  have h5 : 0 ≤ θ * m * H := by positivity
  have e : (θ * N + (1 - θ) * m) * H = θ * N * H + m * H - θ * m * H := by ring
  linarith

end WeightedGoodPages

theorem cl_weighted_good_pages {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V)
    (w β r c ε : ℝ) (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1) (hr : w < r) (hs : 1 < β * r) (hε : 0 ≤ ε)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y)
    (hH : 0 < momentNorm G X Y c (β * r)) (hmax : RowColMaximal G X Y c w r (β * r)) :
    1 - ((X.filter (fun v => c - ε ≤ rowDensity G v Y)).card : ℝ) / (X.card : ℝ) ≤
        (w / (r - w) + 1 - (1 - β) ^ (1 / (β * r))) *
          (momentNorm G X Y c (β * r) / (momentNorm G X Y c (β * r) + ε)) ∧
      (w / (r - w) + 1 - (1 - β) ^ (1 / (β * r))) *
          (momentNorm G X Y c (β * r) / (momentNorm G X Y c (β * r) + ε)) ≤
        w / (r - w) + 1 - (1 - β) ^ (1 / (β * r)) := by
  have hr0 : 0 < r := lt_trans hw hr
  have hsr : β * r < r := by nlinarith
  have hs0 : 0 < β * r := by linarith
  set s := β * r with hsdef
  set H := momentNorm G X Y c s with hHdef
  set a0 := (1 - β) ^ (1 / s) with ha0def
  have ha0 : a0 ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by positivity)
  have hwrw : w / r ≤ w / (r - w) := div_le_div_of_nonneg_left hw.le (by linarith) (by linarith)
  have hD : 0 < w / (r - w) + 1 - a0 := by
    have : 0 < w / (r - w) := div_pos hw (by linarith)
    linarith
  have hHe : 0 < H + ε := by linarith
  have hfrac0 : 0 < H / (H + ε) := div_pos hH hHe
  have hfrac1 : H / (H + ε) ≤ 1 := (div_le_one hHe).mpr (by linarith)
  refine ⟨?_, mul_le_of_le_one_right hD.le hfrac1⟩
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  -- columns
  have hβs : 1 - s / r = 1 - β := by rw [hsdef]; field_simp
  have hcol := wgp_col_lower G X Y c w r s hs0 hsr hX hY hH hmax.2
  rw [hβs] at hcol
  have hsumg : (Y.card : ℝ) * (c + a0 * H) ≤ ∑ y ∈ Y, colDensity G X y := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun y hy => by have := hcol y hy; linarith)
  have hsumπ : (X.card : ℝ) * (c + a0 * H) ≤ ∑ v ∈ X, rowDensity G v Y := by
    have havg := wgp_avg_eq G X Y hX hY
    have h1 : c + a0 * H ≤ (∑ y ∈ Y, colDensity G X y) / (Y.card : ℝ) := by
      rw [le_div_iff₀ hY0]; linarith
    rw [havg, le_div_iff₀ hX0] at h1
    linarith
  -- rows
  have hrow := wgp_row_excess G X Y c w r s hw hr hs.le hY hH hmax.1
  -- (RC)
  have hRC : ∑ v ∈ X, max (c + H - rowDensity G v Y) 0 ≤ (X.card : ℝ) * H * (w / r + 1 - a0) := by
    have hid : ∀ v ∈ X, max (c + H - rowDensity G v Y) 0 =
        max (rowDensity G v Y - c - H) 0 - (rowDensity G v Y - c - H) := by
      intro v _
      rcases le_total (rowDensity G v Y - c - H) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    rw [Finset.sum_congr rfl hid, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    nlinarith
  -- Markov
  set Gd := X.filter (fun v => c - ε ≤ rowDensity G v Y) with hGd
  have hbad : ((X.card : ℝ) - Gd.card) * (H + ε) ≤ ∑ v ∈ X, max (c + H - rowDensity G v Y) 0 := by
    classical
    have hcard : (X.filter (fun v => ¬ (c - ε ≤ rowDensity G v Y))).card + Gd.card = X.card := by
      rw [hGd, add_comm]; exact Finset.card_filter_add_card_filter_not _
    have hcard' : ((X.filter (fun v => ¬ (c - ε ≤ rowDensity G v Y))).card : ℝ) =
        (X.card : ℝ) - Gd.card := by
      rw [← hcard]; push_cast; ring
    rw [← hcard', ← nsmul_eq_mul, ← Finset.sum_const]
    calc ∑ v ∈ X.filter (fun v => ¬ (c - ε ≤ rowDensity G v Y)), (H + ε)
        ≤ ∑ v ∈ X.filter (fun v => ¬ (c - ε ≤ rowDensity G v Y)), max (c + H - rowDensity G v Y) 0 :=
          Finset.sum_le_sum (fun v hv => by
            have := (Finset.mem_filter.mp hv).2
            exact le_max_of_le_left (by linarith))
      _ ≤ ∑ v ∈ X, max (c + H - rowDensity G v Y) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun v _ _ => le_max_right _ _)
  -- conclude
  have hmain : ((X.card : ℝ) - Gd.card) * (H + ε) ≤ (X.card : ℝ) * H * (w / (r - w) + 1 - a0) := by
    have : (X.card : ℝ) * H * (w / r + 1 - a0) ≤ (X.card : ℝ) * H * (w / (r - w) + 1 - a0) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hlhs : 1 - (Gd.card : ℝ) / X.card = ((X.card : ℝ) - Gd.card) / X.card := by
    field_simp
  rw [hlhs, div_le_iff₀ hX0, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hHe]
  nlinarith

end DiagRamsey.ClosureEnv
