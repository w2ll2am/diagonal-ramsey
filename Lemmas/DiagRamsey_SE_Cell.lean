import Mathlib
import Lemmas.DiagRamsey_SE_Mono
import Lemmas.DiagRamsey_SE_Calc

open MeasureTheory

namespace DiagRamsey.SE

lemma certM_le_certB {p μ w β x q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 < β)
    (hq : q ∈ certFeasible p μ w β x) : certM p μ w β x q ≤ certB μ w q := by
  unfold certM
  split_ifs with h
  · exact le_rfl
  · rcases hq.2.2 with h' | ⟨_, h'⟩
    · exact absurd h' h
    · exact Md_le_certB hβ hp0 hp1 h'

lemma q_certB_le {μ w q : ℝ} (hw : 0 ≤ w) (hq0 : 0 < q) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    q * certB μ w q ≤ w := by
  unfold certB
  have h := Real.log_le_sub_one_of_pos (div_pos hμ0 hq0)
  have h2 : q * Real.log (μ / q) ≤ μ - q := by
    have := mul_le_mul_of_nonneg_left h hq0.le
    rw [mul_sub, mul_div_cancel₀ _ hq0.ne', mul_one] at this; exact this
  have h3 : q * Real.log (μ / q) ≤ 1 := by linarith
  calc q * (w * Real.log (μ / q)) = w * (q * Real.log (μ / q)) := by ring
    _ ≤ w * 1 := mul_le_mul_of_nonneg_left h3 hw
    _ = w := mul_one w

lemma integrand_le {p μ w β x q t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 < β) (hw : 0 ≤ w)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq : q ∈ certFeasible p μ w β x) :
    q * certM p μ w β x q + w * q * (1 + Real.log t) ≤ 2 * w := by
  have h1 := mul_le_mul_of_nonneg_left (certM_le_certB hp0 hp1 hβ hq) hq.1.le
  have h2 := q_certB_le (μ := μ) hw hq.1 hμ0 hμ1
  have hl := Real.log_nonpos ht0 ht1
  have hq1 : q ≤ 1 := hq.2.1.trans hμ1.le
  have : w * q * (1 + Real.log t) ≤ w := by
    have : w * q * (1 + Real.log t) ≤ w * q * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hw hq.1.le)
    nlinarith
  linarith

lemma le_certIntegrand {p μ w β x q t : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 < β) (hw : 0 ≤ w)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq : q ∈ certFeasible p μ w β x) :
    q * certM p μ w β x q + w * q * (1 + Real.log t) ≤ certIntegrand p μ w β x t := by
  unfold certIntegrand
  apply le_csSup
  · refine ⟨2 * w, ?_⟩
    rintro _ ⟨q', hq', rfl⟩
    exact integrand_le hp0 hp1 hβ hw hμ0 hμ1 ht0 ht1 hq'
  · exact ⟨q, hq, rfl⟩

lemma integrable_of_cert_neg {p μ w β x : ℝ} (h : cert p μ w β x < 0) :
    IntervalIntegrable (certIntegrand p μ w β x) volume 0 1 := by
  by_contra hn
  unfold cert at h
  rw [intervalIntegral.integral_undef hn] at h
  exact lt_irrefl _ h

lemma cell_lower {p μ w β x q a b : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ : 0 < β) (hw : 0 ≤ w)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hI : IntervalIntegrable (certIntegrand p μ w β x) volume 0 1)
    (hq : q ∈ certFeasible p μ w β x) :
    (b - a) * (q * certM p μ w β x q) + w * q * (PhiL b - PhiL a) ≤
      ∫ t in a..b, certIntegrand p μ w β x t := by
  have hlog : IntervalIntegrable (fun t => 1 + Real.log t) volume a b :=
    intervalIntegrable_const.add intervalIntegral.intervalIntegrable_log'
  have hlow : IntervalIntegrable
      (fun t => q * certM p μ w β x q + w * q * (1 + Real.log t)) volume a b :=
    intervalIntegrable_const.add (hlog.const_mul _)
  have hval : ∫ t in a..b, (q * certM p μ w β x q + w * q * (1 + Real.log t)) =
      (b - a) * (q * certM p μ w β x q) + w * q * (PhiL b - PhiL a) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hlog.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
      intervalIntegral.integral_const, integral_log]
    unfold PhiL
    simp only [smul_eq_mul, mul_one]
    ring
  rw [← hval]
  have hsub : Set.uIcc a b ⊆ Set.uIcc 0 1 :=
    Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨ha, hab.trans hb⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨ha.trans hab, hb⟩))
  apply intervalIntegral.integral_mono_on hab hlow (hI.mono_set hsub)
  intro t ht
  exact le_certIntegrand hp0 hp1 hβ hw hμ0 hμ1 (ha.trans ht.1) (ht.2.trans hb) hq

lemma cells_sum {f : ℝ → ℝ} {N : ℕ} (hN : 0 < N) (hI : IntervalIntegrable f volume 0 1) :
    ∑ k ∈ Finset.range N, ∫ t in ((k:ℕ):ℝ) / N..(((k + 1 : ℕ)) : ℝ) / N, f t =
      ∫ t in (0:ℝ)..1, f t := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := fun k : ℕ => (k:ℝ) / N) (n := N) (fun k hk => by
      apply hI.mono_set
      apply Set.uIcc_subset_uIcc
      · refine Set.mem_uIcc.2 (Or.inl ⟨by positivity, ?_⟩)
        rw [div_le_one hN']; exact_mod_cast hk.le
      · refine Set.mem_uIcc.2 (Or.inl ⟨by positivity, ?_⟩)
        rw [div_le_one hN']; exact_mod_cast hk)
  rw [h]
  simp [hN'.ne']

end DiagRamsey.SE
