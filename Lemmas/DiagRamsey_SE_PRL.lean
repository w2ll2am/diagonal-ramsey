import Mathlib
import Definitions.Def_DiagRamsey_Cert
import Lemmas.DiagRamsey_SE_Limits
import Lemmas.DiagRamsey_SE_Mono

open Filter Topology

namespace DiagRamsey.SE

/-- `ℓ = -w log(1-q) + log x + ((1-β) log π - log m)/β`, so that the red threshold is `K = (1-q) e^{ℓ/r}`. -/
noncomputable def ellF (w β x q m π : ℝ) : ℝ :=
  -w * Real.log (1 - q) + Real.log x + ((1 - β) * Real.log π - Real.log m) / β

/-- The red lower bound `L = ((1-q) - K)/q` on the red-cell mean of `Z`. -/
noncomputable def LF (w β x q m π r : ℝ) : ℝ :=
  (1 - q) * (1 - Real.exp (ellF w β x q m π / r)) / q

/-- `T = (μ/q)^{w/r}`. -/
noncomputable def TF (μ w q r : ℝ) : ℝ := Real.exp (certB μ w q / r)

/-- `(1+L)^s` with `s = β r`. -/
noncomputable def PwF (w β x q m π r : ℝ) : ℝ :=
  Real.exp (β * (r * Real.log (1 + LF w β x q m π r)))

/-- `W = (U - m(1+L)^s)/(1-m)`. -/
noncomputable def WF (μ w β x q m π r : ℝ) : ℝ :=
  (certU μ w β q - m * PwF w β x q m π r) / (1 - m)

/-- The per-row information extracted from the blue and red failure inequalities, for a row with
mean `E = E_ν Z`. -/
def RowBound (μ w β x q m π r E : ℝ) : Prop :=
  E ≤ TF μ w q r - 1 ∧
  (0 < 1 + LF w β x q m π r → m * PwF w β x q m π r < certU μ w β q) ∧
  (TF μ w q r < 1 + LF w β x q m π r → m < 1 ∧
    E ≤ m * LF w β x q m π r +
      (1 - m) * (Real.exp (Real.log (WF μ w β x q m π r) / (β * r)) - 1))

lemma certA_eq_ell {d w β x q : ℝ} (hd : 0 < d) (hq0 : 0 < q) (hq1 : q < 1) (hx : 0 < x)
    (hβ : β ≠ 0) : certA d w x q = -((1 - q) / q) * ellF w β x q d d := by
  rw [certA_eq hd hq1 hx]
  unfold ellF
  rw [Real.log_div (Real.rpow_pos_of_pos (by linarith) _).ne' hx.ne',
    Real.log_rpow (by linarith)]
  field_simp
  ring

theorem prl {p μ w β x : ℝ} (hp0 : 0 < p) (hμ1 : μ < 1) (hμ0 : 0 < μ)
    (hβ0 : 0 < β) (hx0 : 0 < x) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ δ' > 0, ∃ R0 : ℝ, ∀ r ≥ R0, ∀ q m π E : ℝ, δ ≤ q → q ≤ μ + δ' → p - δ' ≤ m → m ≤ 1 →
      p - δ' ≤ π → π ≤ 1 → |m - π| ≤ δ' → RowBound μ w β x q m π r E →
      (∃ q' ∈ certFeasible p μ w β x, |q' - q| ≤ ε ∧ q * r * E ≤ q' * certM p μ w β x q' + ε) ∨
        q * r * E ≤ -K := by
  by_contra hcon
  have H : ∀ n : ℕ, ∃ r ≥ (n:ℝ) + 1, ∃ q m π E : ℝ, δ ≤ q ∧ q ≤ μ + 1 / ((n:ℝ) + 1) ∧
      p - 1 / ((n:ℝ) + 1) ≤ m ∧ m ≤ 1 ∧ p - 1 / ((n:ℝ) + 1) ≤ π ∧ π ≤ 1 ∧
      |m - π| ≤ 1 / ((n:ℝ) + 1) ∧ RowBound μ w β x q m π r E ∧
      ¬((∃ q' ∈ certFeasible p μ w β x, |q' - q| ≤ ε ∧
          q * r * E ≤ q' * certM p μ w β x q' + ε) ∨ q * r * E ≤ -K) := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨1 / ((n:ℝ) + 1), by positivity, (n:ℝ) + 1, ?_⟩
    intro r hr q m π E h1 h2 h3 h4 h5 h6 h7 h8
    by_contra h9
    exact hn ⟨r, hr, q, m, π, E, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  choose r hr q m π E hq1 hq2 hm1 hm2 hπ1 hπ2 hmπ hRB hnot using H
  have hmem : ∀ n, (q n, m n) ∈ Set.Icc (0:ℝ) 2 ×ˢ Set.Icc (-1:ℝ) 1 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    exact ⟨⟨by linarith [hq1 n], by linarith [hq2 n]⟩, ⟨by linarith [hm1 n], hm2 n⟩⟩
  obtain ⟨⟨qs, d⟩, -, φ, hφ, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
  have hQ : Tendsto (fun n => q (φ n)) atTop (𝓝 qs) := (continuous_fst.tendsto _).comp hlim
  have hM : Tendsto (fun n => m (φ n)) atTop (𝓝 d) := (continuous_snd.tendsto _).comp hlim
  have hφt := hφ.tendsto_atTop
  have hinv : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφt
  have hR : Tendsto (fun n => r (φ n)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => hr (φ n))
    exact tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hφt)
  have hP : Tendsto (fun n => π (φ n)) atTop (𝓝 d) := by
    have h0 : Tendsto (fun n => m (φ n) - π (φ n)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ hinv
      exact Eventually.of_forall fun n => by rw [Real.norm_eq_abs]; exact hmπ (φ n)
    have := hM.sub h0
    simp only [sub_sub_cancel, sub_zero] at this
    exact this
  have hqs_ge : δ ≤ qs := ge_of_tendsto hQ (Eventually.of_forall fun n => hq1 (φ n))
  have hqs_le : qs ≤ μ := by
    have := le_of_tendsto_of_tendsto hQ (tendsto_const_nhds.add hinv)
      (Eventually.of_forall fun n => hq2 (φ n))
    simpa using this
  have hd_ge : p ≤ d := by
    have := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hinv) hM
      (Eventually.of_forall fun n => hm1 (φ n))
    simpa using this
  have hd_le : d ≤ 1 := le_of_tendsto hM (Eventually.of_forall fun n => hm2 (φ n))
  have hqs0 : 0 < qs := lt_of_lt_of_le hδ hqs_ge
  have hqs1 : qs < 1 := lt_of_le_of_lt hqs_le hμ1
  have hd0 : 0 < d := lt_of_lt_of_le hp0 hd_ge
  have hQpos : ∀ n, 0 < q (φ n) := fun n => lt_of_lt_of_le hδ (hq1 (φ n))
  have hRpos : ∀ᶠ n in atTop, 0 < r (φ n) := hR.eventually_gt_atTop 0
  -- limits
  have hBl : Tendsto (fun n => certB μ w (q (φ n))) atTop (𝓝 (certB μ w qs)) := by
    unfold certB
    exact ((tendsto_const_nhds.div hQ hqs0.ne').log (div_pos hμ0 hqs0).ne').const_mul w
  have hUl : Tendsto (fun n => certU μ w β (q (φ n))) atTop (𝓝 (certU μ w β qs)) := by
    unfold certU
    exact (hBl.const_mul β).rexp
  have hT : Tendsto (fun n => r (φ n) * (TF μ w (q (φ n)) (r (φ n)) - 1)) atTop
      (𝓝 (certB μ w qs)) :=
    tendsto_mul_exp_div_sub_one (a := fun n => certB μ w (q (φ n))) (r := fun n => r (φ n)) hBl hR
  have hell : Tendsto (fun n => ellF w β x (q (φ n)) (m (φ n)) (π (φ n))) atTop
      (𝓝 (ellF w β x qs d d)) := by
    unfold ellF
    have h1 : Tendsto (fun n => Real.log (1 - q (φ n))) atTop (𝓝 (Real.log (1 - qs))) :=
      (tendsto_const_nhds.sub hQ).log (by linarith)
    exact ((h1.const_mul (-w)).add tendsto_const_nhds).add
      (((((hP.log hd0.ne').const_mul (1 - β))).sub (hM.log hd0.ne')).div_const β)
  have hRL : Tendsto (fun n => r (φ n) * LF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n)))
      atTop (𝓝 (certA d w x qs)) := by
    rw [certA_eq_ell (β := β) hd0 hqs0 hqs1 hx0 hβ0.ne']
    have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := (((h1.sub hQ).div hQ hqs0.ne').neg).mul
      (tendsto_mul_exp_div_sub_one (a := fun n => ellF w β x (q (φ n)) (m (φ n)) (π (φ n)))
        (r := fun n => r (φ n)) hell hR)
    refine h.congr fun n => ?_
    simp only [Pi.div_apply, LF]; ring
  have hPw : Tendsto (fun n => PwF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n))) atTop
      (𝓝 (Real.exp (β * certA d w x qs))) :=
    ((tendsto_mul_log_one_add hRL hR).const_mul β).rexp
  have hev1 : ∀ᶠ n in atTop, |qs - q (φ n)| ≤ ε := by
    filter_upwards [Metric.tendsto_nhds.1 hQ ε hε] with n hn
    rw [Real.dist_eq] at hn
    rw [abs_sub_comm]; exact hn.le
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  by_cases hcase : certA d w x qs ≤ certB μ w qs
  · have hAp : certA p w x qs ≤ certB μ w qs :=
      le_trans (certA_mono hp0 hd_ge hqs0 hqs1 hx0) hcase
    have hF : qs ∈ certFeasible p μ w β x := ⟨hqs0, hqs_le, Or.inl hAp⟩
    have hMv : certM p μ w β x qs = certB μ w qs := by unfold certM; rw [if_pos hAp]
    have hev2 : ∀ᶠ n in atTop, q (φ n) * (r (φ n) * (TF μ w (q (φ n)) (r (φ n)) - 1)) <
        qs * certB μ w qs + ε :=
      (hQ.mul hT).eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
    obtain ⟨n, h1, h2, hR0⟩ := (hev1.and (hev2.and hRpos)).exists
    apply hnot (φ n)
    left
    refine ⟨qs, hF, h1, ?_⟩
    rw [hMv]
    have hE := (hRB (φ n)).1
    have : q (φ n) * r (φ n) * E (φ n) ≤
        q (φ n) * (r (φ n) * (TF μ w (q (φ n)) (r (φ n)) - 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hR0.le) (hQpos _).le
    linarith
  · have hBA : certB μ w qs < certA d w x qs := lt_of_not_ge hcase
    have hbind : ∀ᶠ n in atTop, TF μ w (q (φ n)) (r (φ n)) <
        1 + LF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n)) := by
      filter_upwards [(hRL.sub hT).eventually (lt_mem_nhds (sub_pos.2 hBA)), hRpos] with n h1 h2
      have h3 : r (φ n) * (TF μ w (q (φ n)) (r (φ n)) - 1) <
          r (φ n) * LF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n)) := by linarith
      have := lt_of_mul_lt_mul_left h3 h2.le
      linarith
    have hmPw : ∀ᶠ n in atTop, m (φ n) * PwF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n)) <
        certU μ w β (q (φ n)) := by
      filter_upwards [hbind] with n h
      have hT0 : 0 < TF μ w (q (φ n)) (r (φ n)) := Real.exp_pos _
      exact (hRB (φ n)).2.1 (lt_trans hT0 h)
    have hlimle : d * Real.exp (β * certA d w x qs) ≤ certU μ w β qs :=
      le_of_tendsto_of_tendsto (hM.mul hPw) hUl (hmPw.mono fun n h => h.le)
    have hd1 : d < 1 := by
      rcases lt_or_eq_of_le hd_le with h | h
      · exact h
      · exfalso
        subst h
        rw [one_mul] at hlimle
        unfold certU at hlimle
        have := Real.exp_le_exp.1 hlimle
        nlinarith [mul_lt_mul_of_pos_left hBA hβ0]
    have hbound : ∀ᶠ n in atTop, q (φ n) * r (φ n) * E (φ n) ≤
        q (φ n) * (m (φ n) * (r (φ n) * LF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n))) +
          (1 - m (φ n)) * (r (φ n) * (Real.exp
            (Real.log (WF μ w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n))) / β / r (φ n)) - 1))) := by
      filter_upwards [hbind, hRpos] with n h hR0
      obtain ⟨-, hE⟩ := (hRB (φ n)).2.2 h
      rw [div_div]
      calc q (φ n) * r (φ n) * E (φ n) = q (φ n) * (r (φ n) * E (φ n)) := by ring
        _ ≤ q (φ n) * (r (φ n) * (m (φ n) * LF w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n)) +
            (1 - m (φ n)) * (Real.exp (Real.log (WF μ w β x (q (φ n)) (m (φ n)) (π (φ n))
              (r (φ n))) / (β * r (φ n))) - 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hR0.le) (hQpos _).le
        _ = _ := by ring
    have hW : Tendsto (fun n => WF μ w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n))) atTop
        (𝓝 ((certU μ w β qs - d * Real.exp (β * certA d w x qs)) / (1 - d))) :=
      (hUl.sub (hM.mul hPw)).div (hone.sub hM) (sub_pos.2 hd1).ne'
    rcases lt_or_eq_of_le hlimle with hlt | heq
    · obtain ⟨hF, hMle⟩ := Md_le_certM hβ0 hx0 hp0 hd_ge hd1 hqs0 hqs_le hμ1 hlt
      have hWpos : 0 < (certU μ w β qs - d * Real.exp (β * certA d w x qs)) / (1 - d) :=
        div_pos (sub_pos.2 hlt) (sub_pos.2 hd1)
      have hX := tendsto_mul_exp_div_sub_one ((hW.log hWpos.ne').div_const β) hR
      have hlim2 := hQ.mul ((hM.mul hRL).add ((hone.sub hM).mul hX))
      have hval : qs * (d * certA d w x qs + (1 - d) *
          (Real.log ((certU μ w β qs - d * Real.exp (β * certA d w x qs)) / (1 - d)) / β)) =
          qs * Md μ w β x d qs := by unfold Md; ring
      rw [hval] at hlim2
      obtain ⟨n, h1, h2, h3⟩ := (hev1.and ((hlim2.eventually
        (gt_mem_nhds (lt_add_of_pos_right _ hε))).and hbound)).exists
      apply hnot (φ n); left
      refine ⟨qs, hF, h1, ?_⟩
      have : qs * Md μ w β x d qs ≤ qs * certM p μ w β x qs :=
        mul_le_mul_of_nonneg_left hMle hqs0.le
      linarith
    · have hW0' : (certU μ w β qs - d * Real.exp (β * certA d w x qs)) / (1 - d) = 0 := by
        rw [heq]; simp
      rw [hW0'] at hW
      have hWpos : ∀ᶠ n in atTop, WF μ w β x (q (φ n)) (m (φ n)) (π (φ n)) (r (φ n)) ∈
          Set.Ioi 0 := by
        filter_upwards [hbind, hmPw] with n h1 h2
        obtain ⟨hm1', -⟩ := (hRB (φ n)).2.2 h1
        exact div_pos (sub_pos.2 h2) (sub_pos.2 hm1')
      have hW0 := tendsto_nhdsWithin_iff.2 ⟨hW, hWpos⟩
      have hlogW := Real.tendsto_log_nhdsGT_zero.comp hW0
      have hX := tendsto_mul_exp_div_sub_one_atBot ((hlogW.atBot_div_const hβ0)) hR
      have hY := Tendsto.pos_mul_atBot hqs0 hQ (Tendsto.add_atBot (hM.mul hRL)
        (Tendsto.pos_mul_atBot (sub_pos.2 hd1) (hone.sub hM) hX))
      obtain ⟨n, h1, h2⟩ := ((hY.eventually_lt_atBot (-K)).and hbound).exists
      apply hnot (φ n); right
      simp only [Function.comp] at h1
      linarith

end DiagRamsey.SE
