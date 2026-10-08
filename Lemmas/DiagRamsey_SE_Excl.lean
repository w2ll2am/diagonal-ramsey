import Mathlib
import Lemmas.DiagRamsey_SE_PRL

open Filter Topology

namespace DiagRamsey.SE

/-- Rows of degree `q = 0` cannot be red-failing when `m, π` are near a density `≥ p > x`. -/
theorem excl0 {p β x : ℝ} (hp0 : 0 < p) (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 < x) (hxp : x < p) :
    ∃ δ' > 0, ∀ m π : ℝ, p - δ' ≤ m → m ≤ 1 → 0 ≤ π → |m - π| ≤ δ' →
      m < x ^ β * π ^ (1 - β) → False := by
  by_contra hcon
  have H : ∀ n : ℕ, ∃ m π : ℝ, p - 1 / ((n:ℝ) + 1) ≤ m ∧ m ≤ 1 ∧ 0 ≤ π ∧
      |m - π| ≤ 1 / ((n:ℝ) + 1) ∧ m < x ^ β * π ^ (1 - β) := by
    intro n; by_contra hn; apply hcon
    refine ⟨1 / ((n:ℝ) + 1), by positivity, ?_⟩
    intro m π h1 h2 h3 h4 h5
    exact hn ⟨m, π, h1, h2, h3, h4, h5⟩
  choose m π hm1 hm2 hπ0 hmπ hlt using H
  have hmem : ∀ n, m n ∈ Set.Icc (-1:ℝ) 1 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    exact ⟨by linarith [hm1 n], hm2 n⟩
  obtain ⟨d, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hM : Tendsto (fun n => m (φ n)) atTop (𝓝 d) := hlim
  have hinv : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
  have hP : Tendsto (fun n => π (φ n)) atTop (𝓝 d) := by
    have h0 : Tendsto (fun n => m (φ n) - π (φ n)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ hinv
      exact Eventually.of_forall fun n => by rw [Real.norm_eq_abs]; exact hmπ (φ n)
    have := hM.sub h0
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  have hd_ge : p ≤ d := by
    have := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hinv) hM
      (Eventually.of_forall fun n => hm1 (φ n))
    simpa using this
  have hd0 : 0 < d := lt_of_lt_of_le hp0 hd_ge
  have hle : d ≤ x ^ β * d ^ (1 - β) :=
    le_of_tendsto_of_tendsto hM (tendsto_const_nhds.mul (hP.rpow_const (Or.inr (by linarith))))
      (Eventually.of_forall fun n => (hlt (φ n)).le)
  have hsplit : d = d ^ β * d ^ (1 - β) := by
    rw [← Real.rpow_add hd0]; simp
  have hpos : 0 < d ^ (1 - β) := Real.rpow_pos_of_pos hd0 _
  have h2 : d ^ β ≤ x ^ β := by
    have hle2 : d ^ β * d ^ (1 - β) ≤ x ^ β * d ^ (1 - β) := by rw [← hsplit]; exact hle
    exact le_of_mul_le_mul_right hle2 hpos
  have h3 := (Real.rpow_le_rpow_iff hd0.le hx0.le hβ0).1 h2
  linarith

/-- Small positive degrees are excluded for regular rows. -/
theorem excl {p μ w β x : ℝ} (hp0 : 0 < p) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hw : 0 < w)
    (hβ0 : 0 < β) (hx0 : 0 < x) (hxp : x < p) :
    ∃ δ > 0, ∃ δ' > 0, ∃ R0 : ℝ, ∀ r ≥ R0, ∀ q m π E : ℝ, 0 < q → q < δ → p - δ' ≤ m →
      m ≤ 1 → p - δ' ≤ π → π ≤ 1 → |m - π| ≤ δ' → RowBound μ w β x q m π r E → False := by
  by_contra hcon
  have H : ∀ n : ℕ, ∃ r ≥ (n:ℝ) + 1 + 2 * w, ∃ q m π E : ℝ, 0 < q ∧ q < 1 / ((n:ℝ) + 1) ∧
      p - 1 / ((n:ℝ) + 1) ≤ m ∧ m ≤ 1 ∧ p - 1 / ((n:ℝ) + 1) ≤ π ∧ π ≤ 1 ∧
      |m - π| ≤ 1 / ((n:ℝ) + 1) ∧ RowBound μ w β x q m π r E := by
    intro n; by_contra hn; apply hcon
    refine ⟨1 / ((n:ℝ) + 1), by positivity, 1 / ((n:ℝ) + 1), by positivity,
      (n:ℝ) + 1 + 2 * w, ?_⟩
    intro r hr q m π E h1 h2 h3 h4 h5 h6 h7 h8
    exact hn ⟨r, hr, q, m, π, E, h1, h2, h3, h4, h5, h6, h7, h8⟩
  choose r hr q m π E hq0 hq1 hm1 hm2 hπ1 hπ2 hmπ hRB using H
  have hmem : ∀ n, m n ∈ Set.Icc (-1:ℝ) 1 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    exact ⟨by linarith [hm1 n], hm2 n⟩
  obtain ⟨d, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hM : Tendsto (fun n => m (φ n)) atTop (𝓝 d) := hlim
  have hφt := hφ.tendsto_atTop
  have hinv : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφt
  have hR : Tendsto (fun n => r (φ n)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => by have := hr (φ n); linarith : ∀ n,
      (φ n : ℝ) + 1 ≤ r (φ n))
    exact tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hφt)
  have hQ : Tendsto (fun n => q (φ n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv
      (fun n => (hq0 (φ n)).le) (fun n => (hq1 (φ n)).le)
  have hP : Tendsto (fun n => π (φ n)) atTop (𝓝 d) := by
    have h0 : Tendsto (fun n => m (φ n) - π (φ n)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ hinv
      exact Eventually.of_forall fun n => by rw [Real.norm_eq_abs]; exact hmπ (φ n)
    have := hM.sub h0
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  have hd_ge : p ≤ d := by
    have := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hinv) hM
      (Eventually.of_forall fun n => hm1 (φ n))
    simpa using this
  have hd0 : 0 < d := lt_of_lt_of_le hp0 hd_ge
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hell : Tendsto (fun n => ellF w β x (q (φ n)) (m (φ n)) (π (φ n))) atTop
      (𝓝 (ellF w β x 0 d d)) := by
    unfold ellF
    have h1 : Tendsto (fun n => Real.log (1 - q (φ n))) atTop (𝓝 (Real.log (1 - 0))) :=
      (hone.sub hQ).log (by norm_num)
    exact ((h1.const_mul (-w)).add tendsto_const_nhds).add
      (((((hP.log hd0.ne').const_mul (1 - β))).sub (hM.log hd0.ne')).div_const β)
  have hellv : -(1 - 0) * ellF w β x 0 d d = Real.log d - Real.log x := by
    unfold ellF; simp only [sub_zero, Real.log_one, mul_zero, zero_add]; field_simp; ring
  have hgap : 0 < Real.log d - Real.log x := by
    have := Real.log_lt_log hx0 (lt_of_lt_of_le hxp hd_ge); linarith
  have hqrL : Tendsto (fun n => q (φ n) * r (φ n) *
      LF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n))) atTop
      (𝓝 (Real.log d - Real.log x)) := by
    rw [← hellv]
    have h := ((hone.sub hQ).neg).mul
      (tendsto_mul_exp_div_sub_one (a := fun n => ellF w β x (q (φ n)) (m (φ n)) (π (φ n)))
        (r := fun n => r (φ n)) hell hR)
    refine h.congr fun n => ?_
    have := (hq0 (φ n)).ne'
    unfold LF; field_simp; ring
  -- the upper bound `G → 0`
  have hQ' : Tendsto (fun n => q (φ n)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hQ, Eventually.of_forall fun n => hq0 (φ n)⟩
  have hT : Tendsto (fun n => -Real.log (q (φ n))) atTop atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hQ')
  have hc : Tendsto (fun n => -Real.log (m (φ n)) / β) atTop (𝓝 (-Real.log d / β)) :=
    ((hM.log hd0.ne').neg).div_const β
  have hT2 := hT.atTop_div_const (by norm_num : (0:ℝ) < 2)
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hT2
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp hT2
  have hG := (((h1.const_mul (2 * w)).mul hc.rexp).add ((hc.mul hc.rexp).mul h2))
  simp only [mul_zero, zero_mul, add_zero] at hG
  -- eventual facts
  have hmpos : ∀ᶠ n in atTop, 0 < m (φ n) := hM.eventually (lt_mem_nhds hd0)
  have hqsmall : ∀ᶠ n in atTop, q (φ n) < 1 := hQ.eventually (gt_mem_nhds (by norm_num))
  have hev1 : ∀ᶠ n in atTop, (Real.log d - Real.log x) / 2 < q (φ n) * r (φ n) *
      LF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n)) :=
    hqrL.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ n in atTop, 2 * w * ((-Real.log (q (φ n)) / 2) ^ 1 *
      Real.exp (-(-Real.log (q (φ n)) / 2))) * Real.exp (-Real.log (m (φ n)) / β) +
      -Real.log (m (φ n)) / β * Real.exp (-Real.log (m (φ n)) / β) *
        Real.exp (-(-Real.log (q (φ n)) / 2)) < (Real.log d - Real.log x) / 2 :=
    hG.eventually (gt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (hmpos.and (hqsmall.and (hev1.and hev2))).exists
  -- abbreviations
  set qq := q (φ n) with hqq
  set mm := m (φ n) with hmm
  set rr := r (φ n) with hrr
  set LL := LF w β x qq mm (π (φ n)) rr with hLL
  have hqpos : 0 < qq := hq0 (φ n)
  have hr2w : 2 * w ≤ rr := by have := hr (φ n); linarith [(Nat.cast_nonneg (φ n) : (0:ℝ) ≤ _)]
  have hr1 : 1 ≤ rr := by have := hr (φ n); linarith [(Nat.cast_nonneg (φ n) : (0:ℝ) ≤ _)]
  have hrpos : 0 < rr := by linarith
  have hLpos : 0 < LL := by
    have : 0 < qq * rr * LL := by linarith
    by_contra hL'; have hL := le_of_not_gt hL'
    have : qq * rr * LL ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hL
    linarith
  have hcl2 := (hRB (φ n)).2.1 (by linarith)
  unfold PwF at hcl2
  unfold certU certB at hcl2
  rw [← hLL] at hcl2
  have hlog := Real.log_lt_log (mul_pos hn1 (Real.exp_pos _)) hcl2
  rw [Real.log_mul hn1.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hlog
  set t := -Real.log qq with ht
  set c := -Real.log mm / β with hc'
  have hqexp : qq = Real.exp (-t) := by rw [ht, neg_neg, Real.exp_log hqpos]
  have ht0 : 0 ≤ t := by
    have := Real.log_nonpos hqpos.le hn2.le; linarith
  have hc0 : 0 ≤ c := by
    have := Real.log_nonpos hn1.le (hm2 (φ n)); rw [hc']
    exact div_nonneg (by linarith) hβ0.le
  have hlogμq : Real.log (μ / qq) = Real.log μ + t := by
    rw [Real.log_div hμ0.ne' hqpos.ne', ht]; ring
  set b := w * Real.log (μ / qq) + c with hb
  have hrb : rr * Real.log (1 + LL) < b := by
    have : β * (rr * Real.log (1 + LL)) < β * b := by
      rw [hb, hc', mul_add, mul_div_cancel₀ _ hβ0.ne']; linarith
    exact lt_of_mul_lt_mul_left this hβ0.le
  have h1L : 1 + LL < Real.exp (b / rr) := by
    rw [← Real.log_lt_iff_lt_exp (by linarith)]
    rw [lt_div_iff₀ hrpos]; linarith
  have hexp : rr * (Real.exp (b / rr) - 1) ≤ b * Real.exp (b / rr) := by
    have h := Real.add_one_le_exp (-(b / rr))
    have h' : (1 - b / rr) * Real.exp (b / rr) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right h (Real.exp_pos (b / rr)).le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this; linarith
    have : rr * (Real.exp (b / rr) - 1) - b * Real.exp (b / rr) =
        rr * ((1 - b / rr) * Real.exp (b / rr) - 1) := by field_simp; ring
    have h3 : rr * ((1 - b / rr) * Real.exp (b / rr) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hrpos.le (by linarith)
    linarith
  have hmain : qq * rr * LL < qq * (b * Real.exp (b / rr)) := by
    have : rr * LL < rr * (Real.exp (b / rr) - 1) := mul_lt_mul_of_pos_left (by linarith) hrpos
    calc qq * rr * LL = qq * (rr * LL) := by ring
      _ < qq * (rr * (Real.exp (b / rr) - 1)) := mul_lt_mul_of_pos_left this hqpos
      _ ≤ qq * (b * Real.exp (b / rr)) := mul_le_mul_of_nonneg_left hexp hqpos.le
  have hlogμ : Real.log μ < 0 := Real.log_neg hμ0 hμ1
  have hGn : qq * (b * Real.exp (b / rr)) ≤ (w * t + c) * Real.exp c * Real.exp (-(t / 2)) := by
    have hwμ : w * Real.log μ < 0 := mul_neg_of_pos_of_neg hw hlogμ
    have hbt : b ≤ w * t + c := by rw [hb, hlogμq]; linarith
    rcases le_or_gt b 0 with hb0 | hb0
    · have : qq * (b * Real.exp (b / rr)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hqpos.le (mul_nonpos_of_nonpos_of_nonneg hb0 (Real.exp_pos _).le)
      have : 0 ≤ (w * t + c) * Real.exp c * Real.exp (-(t / 2)) := by positivity
      linarith
    · have hbr : b / rr ≤ t / 2 + c := by
        rw [div_le_iff₀ hrpos, hb, hlogμq]
        have k1 := mul_le_mul_of_nonneg_left hr1 hc0
        have k2 := mul_le_mul_of_nonneg_left hr2w ht0
        linarith
      have he : Real.exp (b / rr) ≤ Real.exp (t / 2 + c) := Real.exp_le_exp.2 hbr
      calc qq * (b * Real.exp (b / rr)) ≤ qq * (b * Real.exp (t / 2 + c)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hb0.le) hqpos.le
        _ = b * Real.exp c * Real.exp (-(t / 2)) := by
            rw [hqexp]
            have : Real.exp (-t) * Real.exp (t / 2 + c) = Real.exp c * Real.exp (-(t / 2)) := by
              rw [← Real.exp_add, ← Real.exp_add]; ring_nf
            calc Real.exp (-t) * (b * Real.exp (t / 2 + c)) =
                b * (Real.exp (-t) * Real.exp (t / 2 + c)) := by ring
              _ = _ := by rw [this]; ring
        _ ≤ (w * t + c) * Real.exp c * Real.exp (-(t / 2)) := by
            have h0 : 0 ≤ Real.exp c * Real.exp (-(t / 2)) := by positivity
            have := mul_le_mul_of_nonneg_right hbt h0
            calc b * Real.exp c * Real.exp (-(t / 2)) = b * (Real.exp c * Real.exp (-(t / 2))) := by
                  ring
              _ ≤ (w * t + c) * (Real.exp c * Real.exp (-(t / 2))) := this
              _ = _ := by ring
  have hn4' : (w * t + c) * Real.exp c * Real.exp (-(t / 2)) < (Real.log d - Real.log x) / 2 := by
    have : (w * t + c) * Real.exp c * Real.exp (-(t / 2)) =
        2 * w * ((t / 2) ^ 1 * Real.exp (-(t / 2))) * Real.exp c +
          c * Real.exp c * Real.exp (-(t / 2)) := by ring
    rw [this]; exact hn4
  linarith

end DiagRamsey.SE
