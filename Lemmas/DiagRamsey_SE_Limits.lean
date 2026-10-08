import Mathlib

open Filter Topology

namespace DiagRamsey.SE

theorem tendsto_mul_exp_div_sub_one {ι : Type*} {l : Filter ι} {a r : ι → ℝ} {a0 : ℝ}
    (ha : Tendsto a l (𝓝 a0)) (hr : Tendsto r l atTop) :
    Tendsto (fun i => r i * (Real.exp (a i / r i) - 1)) l (𝓝 a0) := by
  have hinv : Tendsto (fun i => (r i)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hr
  have hbound : Tendsto (fun i => a i ^ 2 / r i) l (𝓝 0) := by
    have := (ha.pow 2).mul hinv
    simpa [div_eq_mul_inv] using this
  have hdiv : Tendsto (fun i => a i / r i) l (𝓝 0) := by
    have := ha.mul hinv
    simpa [div_eq_mul_inv] using this
  have habs : Tendsto (fun i => |a i / r i|) l (𝓝 0) := by simpa using hdiv.abs
  have h1 := habs.eventually (gt_mem_nhds one_pos)
  have hdiff : Tendsto (fun i => r i * (Real.exp (a i / r i) - 1) - a i) l (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [hr.eventually_gt_atTop 0, h1] with i hri hi
    rw [Real.norm_eq_abs]
    have hy := Real.abs_exp_sub_one_sub_id_le hi.le
    have hra : r i * (a i / r i) = a i := mul_div_cancel₀ (a i) hri.ne'
    calc |r i * (Real.exp (a i / r i) - 1) - a i|
        = |r i * (Real.exp (a i / r i) - 1 - a i / r i)| := by rw [mul_sub _ _ (a i / r i), hra]
      _ = r i * |Real.exp (a i / r i) - 1 - a i / r i| := by rw [abs_mul, abs_of_pos hri]
      _ ≤ r i * (a i / r i) ^ 2 := mul_le_mul_of_nonneg_left hy hri.le
      _ = a i ^ 2 / r i := by field_simp
  have := hdiff.add ha
  simpa using this

theorem tendsto_mul_exp_div_sub_one_atBot {ι : Type*} {l : Filter ι} {a r : ι → ℝ}
    (ha : Tendsto a l atBot) (hr : Tendsto r l atTop) :
    Tendsto (fun i => r i * (Real.exp (a i / r i) - 1)) l atBot := by
  rw [tendsto_atBot]
  intro K0
  set K := min K0 (-1) with hK
  have hKneg : K < 0 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  filter_upwards [hr.eventually_ge_atTop (-2 * K), ha.eventually_le_atBot (2 * K)] with i hri hai
  have hr0 : 0 < r i := by linarith
  set e := Real.exp (a i / r i) with he
  have he0 : 0 < e := Real.exp_pos _
  have h1 : e * (1 - a i / r i) ≤ 1 := by
    have := Real.add_one_le_exp (-(a i / r i))
    have h2 : e * Real.exp (-(a i / r i)) = 1 := by
      rw [he, ← Real.exp_add]; simp
    nlinarith
  have h2 : e * (r i - a i) ≤ r i := by
    have : e * (r i - a i) = r i * (e * (1 - a i / r i)) := by field_simp
    rw [this]; nlinarith
  have hra : 0 < r i - a i := by linarith
  have key : (r i * (e - 1) - K) * (r i - a i) ≤ 0 := by nlinarith
  have : r i * (e - 1) - K ≤ 0 := by
    by_contra hc
    have hc := lt_of_not_ge hc
    have := mul_pos hc hra
    linarith
  have : K ≤ K0 := min_le_left _ _
  linarith

theorem tendsto_mul_log_one_add {ι : Type*} {l : Filter ι} {L r : ι → ℝ} {A : ℝ}
    (hL : Tendsto (fun i => r i * L i) l (𝓝 A)) (hr : Tendsto r l atTop) :
    Tendsto (fun i => r i * Real.log (1 + L i)) l (𝓝 A) := by
  have hinv : Tendsto (fun i => (r i)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hr
  have hL0 : Tendsto L l (𝓝 0) := by
    have := hL.mul hinv
    rw [mul_zero] at this
    apply this.congr'
    filter_upwards [hr.eventually_gt_atTop 0] with i hi
    field_simp
  have hlow : Tendsto (fun i => r i * L i / (1 + L i)) l (𝓝 A) := by
    have := hL.div (tendsto_const_nhds.add hL0) (by norm_num : (1:ℝ) + 0 ≠ 0)
    rw [add_zero, div_one] at this
    exact this
  have hpos := (tendsto_const_nhds.add hL0).eventually (lt_mem_nhds (by norm_num : (0:ℝ) < 1 + 0))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hL
  · filter_upwards [hr.eventually_gt_atTop 0, hpos] with i hri hi
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + L i by linarith)
    have : r i * L i / (1 + L i) = r i * (1 - (1 + L i)⁻¹) := by
      field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h hri.le
  · filter_upwards [hr.eventually_gt_atTop 0, hpos] with i hri hi
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + L i by linarith)
    have : 1 + L i - 1 = L i := by ring
    rw [this] at h
    exact mul_le_mul_of_nonneg_left h hri.le

end DiagRamsey.SE
