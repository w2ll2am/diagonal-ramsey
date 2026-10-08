import Mathlib

open Filter Topology

namespace DiagRamsey.SE

/-- Antiderivative of the drift kernel `k_r(t) = r(g t^(g-1) - 1)`, `g = 1 - w/r`. -/
noncomputable def PhiK (r g t : ℝ) : ℝ := r * t ^ g - r * t

/-- Antiderivative of `1 + log t`. -/
noncomputable def PhiL (t : ℝ) : ℝ := t * Real.log t

/-- Antiderivative of the majorant `|k_r(t) + w(1 + log t)| ≤ (r+w) t^(g-1) - r - w + w log t`. -/
noncomputable def Phi2 (w r g t : ℝ) : ℝ :=
  (r + w) * t ^ g / g - (r + 2 * w) * t + w * (t * Real.log t)

/-- Antiderivative of `1 - log t ≥ |1 + log t|`. -/
noncomputable def JF (t : ℝ) : ℝ := 2 * t - t * Real.log t

lemma mono_of_deriv {f f' : ℝ → ℝ} (hc : ContinuousOn f (Set.Icc 0 1))
    (hd : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (f' t) t)
    (hn : ∀ t ∈ Set.Ioo (0:ℝ) 1, 0 ≤ f' t) : MonotoneOn f (Set.Icc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hc
  · intro t ht; rw [interior_Icc] at ht ⊢; exact (hd t ht).hasDerivWithinAt
  · intro t ht; rw [interior_Icc] at ht; exact hn t ht

lemma continuous_rpow_of_pos {g : ℝ} (hg : 0 < g) : Continuous (fun t : ℝ => t ^ g) :=
  continuous_iff_continuousAt.2 fun t => Real.continuousAt_rpow_const t g (Or.inr hg.le)

theorem phi_bound {w r g a b : ℝ} (hw : 0 < w) (hr : 0 < r) (hg0 : 0 < g) (hg1 : g < 1)
    (hg : r * g = r - w) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(PhiK r g b - PhiK r g a) + w * (PhiL b - PhiL a)| ≤ Phi2 w r g b - Phi2 w r g a := by
  have hcp := continuous_rpow_of_pos hg0
  have hml := Real.continuous_mul_log
  have hc1 : Continuous (fun t => Phi2 w r g t - PhiK r g t - w * PhiL t) := by
    unfold Phi2 PhiK PhiL
    exact (((((hcp.const_mul (r + w)).div_const g).sub (continuous_id'.const_mul (r + 2 * w))).add
      (hml.const_mul w)).sub ((hcp.const_mul r).sub (continuous_id'.const_mul r))).sub
      (hml.const_mul w)
  have hc2 : Continuous (fun t => Phi2 w r g t + PhiK r g t + w * PhiL t) := by
    unfold Phi2 PhiK PhiL
    exact (((((hcp.const_mul (r + w)).div_const g).sub (continuous_id'.const_mul (r + 2 * w))).add
      (hml.const_mul w)).add ((hcp.const_mul r).sub (continuous_id'.const_mul r))).add
      (hml.const_mul w)
  have hder : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (Phi2 w r g) ((r + w) * (g * t ^ (g - 1)) / g - (r + 2 * w) * 1 +
        w * (Real.log t + 1)) t ∧
      HasDerivAt (PhiK r g) (r * (g * t ^ (g - 1)) - r * 1) t ∧
      HasDerivAt PhiL (Real.log t + 1) t := by
    intro t ht
    have hpow : HasDerivAt (fun t : ℝ => t ^ g) (g * t ^ (g - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht.1.ne')
    have hlog := Real.hasDerivAt_mul_log ht.1.ne'
    refine ⟨?_, ?_, hlog⟩
    · exact (((hpow.const_mul (r + w)).div_const g).sub
        ((hasDerivAt_id' t).const_mul (r + 2 * w))).add (hlog.const_mul w)
    · exact (hpow.const_mul r).sub ((hasDerivAt_id' t).const_mul r)
  have hX : ∀ t ∈ Set.Ioo (0:ℝ) 1, 1 ≤ t ^ (g - 1) ∧
      Real.log t * (g - 1) + 1 ≤ t ^ (g - 1) := by
    intro t ht
    refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2.le (by linarith), ?_⟩
    rw [Real.rpow_def_of_pos ht.1]
    exact Real.add_one_le_exp _
  have e1 : ∀ X : ℝ, (r + w) * (g * X) / g = (r + w) * X := fun X => by field_simp
  have e2 : ∀ X : ℝ, r * (g * X) = (r - w) * X := fun X => by rw [← mul_assoc, hg]
  have hm1 : MonotoneOn (fun t => Phi2 w r g t - PhiK r g t - w * PhiL t) (Set.Icc 0 1) := by
    apply mono_of_deriv hc1.continuousOn (fun t ht =>
      (((hder t ht).1.sub (hder t ht).2.1).sub ((hder t ht).2.2.const_mul w)))
    intro t ht
    obtain ⟨h1, -⟩ := hX t ht
    rw [e1, e2]
    nlinarith
  have hm2 : MonotoneOn (fun t => Phi2 w r g t + PhiK r g t + w * PhiL t) (Set.Icc 0 1) := by
    apply mono_of_deriv hc2.continuousOn (fun t ht =>
      (((hder t ht).1.add (hder t ht).2.1).add ((hder t ht).2.2.const_mul w)))
    intro t ht
    obtain ⟨-, h2⟩ := hX t ht
    rw [e1, e2]
    have h3 : r * (Real.log t * (g - 1)) = -(w * Real.log t) := by
      linear_combination (Real.log t) * hg
    nlinarith [mul_le_mul_of_nonneg_left h2 hr.le]
  have hai : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hbi : b ∈ Set.Icc (0:ℝ) 1 := ⟨ha.trans hab, hb⟩
  have k1 := hm1 hai hbi hab
  have k2 := hm2 hai hbi hab
  simp only at k1 k2
  rw [abs_le]
  constructor <;> linarith

theorem phi2_total {w r g : ℝ} (hw : 0 < w) (hr : 0 < r) (hg : r * g = r - w) (h2w : 2 * w ≤ r) :
    Phi2 w r g 1 - Phi2 w r g 0 ≤ 4 * w ^ 2 / r := by
  have hg0 : g ≠ 0 := by
    intro h; rw [h, mul_zero] at hg; linarith
  have hg' : g = (r - w) / r := by field_simp; linarith [hg]
  unfold Phi2
  rw [Real.one_rpow, Real.zero_rpow hg0, Real.log_one]
  simp only [mul_zero, zero_div, mul_one, sub_zero, add_zero, zero_mul]
  have hrw : r - w ≠ 0 := (by linarith : (0:ℝ) < r - w).ne'
  rw [hg', show (r + w) / ((r - w) / r) - (r + 2 * w) = 2 * w ^ 2 / (r - w) by
    field_simp; ring]
  rw [div_le_div_iff₀ (by linarith) hr]
  nlinarith [sq_nonneg w]

theorem phiL_bound {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |PhiL b - PhiL a| ≤ JF b - JF a := by
  have hml := Real.continuous_mul_log
  have hm1 : MonotoneOn (fun t => JF t - PhiL t) (Set.Icc 0 1) := by
    have hc : Continuous (fun t => JF t - PhiL t) := by
      unfold JF PhiL
      exact ((continuous_id'.const_mul 2).sub hml).sub hml
    apply mono_of_deriv hc.continuousOn (f' := fun t => 2 * 1 - (Real.log t + 1) - (Real.log t + 1))
    · intro t ht
      have hlog := Real.hasDerivAt_mul_log ht.1.ne'
      exact (((hasDerivAt_id' t).const_mul 2).sub hlog).sub hlog
    · intro t ht
      have := Real.log_nonpos ht.1.le ht.2.le
      linarith
  have hai : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hbi : b ∈ Set.Icc (0:ℝ) 1 := ⟨ha.trans hab, hb⟩
  have k1 := hm1 hai hbi hab
  simp only at k1
  rw [abs_le]
  unfold JF PhiL at *
  constructor <;> linarith

lemma JF_eq (t : ℝ) : JF t = 2 * t + Real.negMulLog t := by
  unfold JF Real.negMulLog; ring

lemma JF_zero : JF 0 = 0 := by unfold JF; simp

lemma JF_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : JF a ≤ JF b := by
  have h := phiL_bound ha hab hb
  have := abs_nonneg (PhiL b - PhiL a)
  linarith

/-- Equal-length increments of the concave `JF` decrease. -/
lemma JF_incr_anti {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) :
    JF (a + 2 * h) - JF (a + h) ≤ JF (a + h) - JF a := by
  have hc := Real.strictConcaveOn_negMulLog.concaveOn.2 (Set.mem_Ici.2 ha)
    (Set.mem_Ici.2 (by linarith : (0:ℝ) ≤ a + 2 * h)) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [show 1 / 2 * a + 1 / 2 * (a + 2 * h) = a + h by ring] at hc
  rw [JF_eq, JF_eq, JF_eq]
  linarith

/-- The sum of an antitone sequence over any finite set is at most its sum over an initial segment of
the same size. -/
theorem sum_le_sum_range_card_of_antitone {f : ℕ → ℝ} (hf : Antitone f) (S : Finset ℕ) :
    ∑ k ∈ S, f k ≤ ∑ k ∈ Finset.range S.card, f k := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s has ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (has a h)
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.sum_range_succ]
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (has x hx)
      simpa using Finset.card_le_card this
    have := hf hcard
    linarith

lemma neg_mul_log_le (φ a : ℝ) (hφ : 0 ≤ φ) : -(φ * Real.log φ) ≤ a * φ + Real.exp (-a - 1) := by
  rcases hφ.lt_or_eq with h | h
  · have hz : 0 < Real.exp (-a - 1) / φ := div_pos (Real.exp_pos _) h
    have hl := Real.log_le_sub_one_of_pos hz
    rw [Real.log_div (Real.exp_pos _).ne' h.ne', Real.log_exp] at hl
    have : Real.exp (-a - 1) / φ * φ = Real.exp (-a - 1) := by field_simp
    nlinarith
  · subst h; simp; exact (Real.exp_pos _).le

/-- Discrete Abel inequality behind the quantile drift. -/
theorem abel_drift (q D : ℕ → ℝ) (n : ℕ) (hq : ∀ k < n, q k ≤ q (k + 1))
    (hD : ∀ k ≤ n + 1, D k ≤ 0) (hD0 : D 0 = 0) :
    q n * D (n + 1) ≤ ∑ k ∈ Finset.range (n + 1), q k * (D (k + 1) - D k) := by
  induction n with
  | zero => simp [hD0]
  | succ n ih =>
    have ih' := ih (fun k hk => hq k (by omega)) (fun k hk => hD k (by omega))
    rw [Finset.sum_range_succ]
    have h1 := hq n (by omega)
    have h2 := hD (n + 1) (by omega)
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : q n - q (n + 1) ≤ 0) h2]

end DiagRamsey.SE
