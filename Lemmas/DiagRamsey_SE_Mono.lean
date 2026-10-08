import Mathlib
import Definitions.Def_DiagRamsey_Cert

open Filter Topology

namespace DiagRamsey.SE

/-- The binding-branch envelope `M_d(q)` with `p` replaced by `d`. -/
noncomputable def Md (μ w β x d q : ℝ) : ℝ :=
  d * certA d w x q + (1 - d) / β *
    Real.log ((certU μ w β q - d * Real.exp (β * certA d w x q)) / (1 - d))

lemma certA_eq {d w x q : ℝ} (hd : 0 < d) (hq : q < 1) (hx : 0 < x) :
    certA d w x q = (1 - q) / q * (Real.log d + Real.log ((1 - q) ^ w / x)) := by
  unfold certA
  rw [mul_div_assoc, Real.log_mul hd.ne'
    (div_pos (Real.rpow_pos_of_pos (by linarith) _) hx).ne']

lemma certA_mono {d1 d2 w x q : ℝ} (hd1 : 0 < d1) (h12 : d1 ≤ d2) (hq0 : 0 < q) (hq : q < 1)
    (hx : 0 < x) : certA d1 w x q ≤ certA d2 w x q := by
  rw [certA_eq hd1 hq hx, certA_eq (lt_of_lt_of_le hd1 h12) hq hx]
  have hk : 0 ≤ (1 - q) / q := div_nonneg (by linarith) hq0.le
  apply mul_le_mul_of_nonneg_left _ hk
  have := Real.log_le_log hd1 h12
  linarith

lemma Md_le_certB {μ w β x d q : ℝ} (hβ : 0 < β) (hd0 : 0 < d) (hd1 : d < 1)
    (hfeas : d * Real.exp (β * certA d w x q) < certU μ w β q) :
    Md μ w β x d q ≤ certB μ w q := by
  unfold Md
  set E := Real.exp (β * certA d w x q) with hEdef
  set U := certU μ w β q with hUdef
  set z := (U - d * E) / (1 - d) with hzdef
  have hz : 0 < z := div_pos (by linarith) (by linarith)
  have hE : 0 < E := Real.exp_pos _
  have h1d : (1:ℝ) - d ≠ 0 := by linarith
  have hcomb : d * E + (1 - d) * z = U := by
    rw [hzdef, mul_div_cancel₀ _ h1d]; ring
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 hE) (Set.mem_Ioi.2 hz)
    hd0.le (by linarith : (0:ℝ) ≤ 1 - d) (by ring)
  simp only [smul_eq_mul] at hconc
  rw [hcomb] at hconc
  have hlogE : Real.log E = β * certA d w x q := Real.log_exp _
  have hlogU : Real.log U = β * certB μ w q := Real.log_exp _
  rw [hlogE, hlogU] at hconc
  rw [← sub_nonneg]
  have : certB μ w q - (d * certA d w x q + (1 - d) / β * Real.log z) =
      (β * certB μ w q - (d * (β * certA d w x q) + (1 - d) * Real.log z)) / β := by
    field_simp
  rw [this]
  apply div_nonneg _ hβ.le
  linarith

/-- The log-split form of `Md` used for differentiation. -/
noncomputable def MdSplit (μ w β x q e : ℝ) : ℝ :=
  e * certA e w x q + (1 - e) / β *
    (Real.log (certU μ w β q - e * Real.exp (β * certA e w x q)) - Real.log (1 - e))

lemma MdSplit_deriv {μ w β x q d : ℝ} (hβ : 0 < β) (hx : 0 < x) (hq0 : 0 < q) (hq1 : q < 1)
    (hd0 : 0 < d) (hd1 : d < 1)
    (hN : 0 < certU μ w β q - d * Real.exp (β * certA d w x q))
    (hAB : certB μ w q < certA d w x q) :
    ∃ g', HasDerivAt (MdSplit μ w β x q) g' d ∧ g' ≤ 0 := by
  set k := (1 - q) / q with hk
  have hkpos : 0 < k := div_pos (by linarith) hq0
  have hc0 : 0 < (1 - q) ^ w / x := div_pos (Real.rpow_pos_of_pos (by linarith) _) hx
  have hne : d * (1 - q) ^ w / x ≠ 0 := by
    rw [mul_div_assoc]; exact (mul_pos hd0 hc0).ne'
  have hA : HasDerivAt (fun e => certA e w x q) (k / d) d := by
    have h := ((((hasDerivAt_id' d).mul_const ((1 - q) ^ w)).div_const x).log hne).const_mul k
    have hfun : (fun e => certA e w x q) = fun e => k * Real.log (e * (1 - q) ^ w / x) := by
      funext e; simp only [certA, hk]
    have hw0 : (1 - q) ^ w ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    have hval : k * (1 * (1 - q) ^ w / x / (d * (1 - q) ^ w / x)) = k / d := by
      field_simp
    rw [hfun, ← hval]; exact h
  set A := certA d w x q with hAdef
  set E := Real.exp (β * A) with hEdef
  set U := certU μ w β q with hUdef
  have hE : HasDerivAt (fun e => Real.exp (β * certA e w x q)) (E * (β * (k / d))) d :=
    (hA.const_mul β).exp
  have hNd : HasDerivAt (fun e => U - e * Real.exp (β * certA e w x q))
      (0 - (1 * E + d * (E * (β * (k / d))))) d :=
    (hasDerivAt_const d U).sub ((hasDerivAt_id' d).mul hE)
  have hlogN := hNd.log hN.ne'
  have h1d : (1 : ℝ) - d ≠ 0 := by linarith
  have hlog1 := ((hasDerivAt_id' d).const_sub (1 : ℝ)).log h1d
  set N := U - d * E with hNdef
  set G := (1 * A + d * (k / d)) + ((-1) / β * (Real.log N - Real.log (1 - d)) +
      (1 - d) / β * ((0 - (1 * E + d * (E * (β * (k / d))))) / N - (-1) / (1 - d))) with hGdef
  have htot : HasDerivAt (MdSplit μ w β x q) G d := by
    have h := ((hasDerivAt_id' d).mul hA).add
      ((((hasDerivAt_id' d).const_sub (1 : ℝ)).div_const β).mul (hlogN.sub hlog1))
    exact h
  refine ⟨G, htot, ?_⟩
  have hEpos : 0 < E := Real.exp_pos _
  have hEU : U < E := by
    rw [hEdef, hUdef]; unfold certU
    exact Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hAB hβ)
  set t := E * (1 - d) / N with htdef
  have ht1 : 1 ≤ t := by
    rw [htdef, le_div_iff₀ hN]; nlinarith
  have htpos : 0 < t := by linarith
  have hlogt : Real.log t = β * A - (Real.log N - Real.log (1 - d)) := by
    rw [htdef, Real.log_div (mul_pos hEpos (by linarith)).ne' hN.ne',
      Real.log_mul hEpos.ne' h1d, hEdef, Real.log_exp]
    ring
  have hβg : β * G =
      β * A - (Real.log N - Real.log (1 - d)) + 1 - t + β * k * (1 - t) := by
    rw [htdef, hGdef]; field_simp; ring
  have hlt := Real.log_le_sub_one_of_pos htpos
  have hfin : β * G ≤ 0 := by
    rw [hβg, ← hlogt]
    have : β * k * (1 - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  by_contra hc
  have hc := lt_of_not_ge hc
  have := mul_pos hβ hc
  linarith

lemma Md_antitone {μ w β x p d2 q : ℝ} (hβ : 0 < β) (hx : 0 < x) (hq0 : 0 < q) (hq1 : q < 1)
    (hp : 0 < p) (hpd : p ≤ d2) (hd2 : d2 < 1)
    (hfeas : d2 * Real.exp (β * certA d2 w x q) < certU μ w β q)
    (hAB : certB μ w q < certA p w x q) :
    Md μ w β x d2 q ≤ Md μ w β x p q := by
  have hpt : ∀ e ∈ Set.Icc p d2, 0 < e ∧ e < 1 ∧
      0 < certU μ w β q - e * Real.exp (β * certA e w x q) ∧ certB μ w q < certA e w x q := by
    intro e he
    have he0 : 0 < e := lt_of_lt_of_le hp he.1
    have hAe := certA_mono (w := w) (x := x) (q := q) hp he.1 hq0 hq1 hx
    have hAe2 := certA_mono (w := w) (x := x) (q := q) he0 he.2 hq0 hq1 hx
    refine ⟨he0, lt_of_le_of_lt he.2 hd2, ?_, lt_of_lt_of_le hAB hAe⟩
    have : e * Real.exp (β * certA e w x q) ≤ d2 * Real.exp (β * certA d2 w x q) :=
      mul_le_mul he.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hAe2 hβ.le))
        (Real.exp_pos _).le (by linarith)
    linarith
  have hder : ∀ e ∈ Set.Icc p d2, ∃ g', HasDerivAt (MdSplit μ w β x q) g' e ∧ g' ≤ 0 := by
    intro e he
    obtain ⟨h0, h1, hN, hAB'⟩ := hpt e he
    exact MdSplit_deriv hβ hx hq0 hq1 h0 h1 hN hAB'
  choose! g' hg' hg'neg using hder
  have hanti : AntitoneOn (MdSplit μ w β x q) (Set.Icc p d2) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc p d2) (f' := g')
    · intro e he
      exact (hg' e he).continuousAt.continuousWithinAt
    · intro e he
      rw [interior_Icc] at he
      exact (hg' e (Set.Ioo_subset_Icc_self he)).hasDerivWithinAt
    · intro e he
      rw [interior_Icc] at he
      exact hg'neg e (Set.Ioo_subset_Icc_self he)
  have heq : ∀ e ∈ Set.Icc p d2, Md μ w β x e q = MdSplit μ w β x q e := by
    intro e he
    obtain ⟨h0, h1, hN, -⟩ := hpt e he
    unfold Md MdSplit
    rw [Real.log_div hN.ne' (by linarith)]
  rw [heq d2 ⟨hpd, le_rfl⟩, heq p ⟨le_rfl, hpd⟩]
  exact hanti ⟨le_rfl, hpd⟩ ⟨hpd, le_rfl⟩ hpd

/-- Monotonicity in the density: a binding feasible point at density `d ≥ p` is feasible at `p`
and its envelope value is at most `M_p`. -/
theorem Md_le_certM {μ w β x p d q : ℝ} (hβ : 0 < β) (hx : 0 < x) (hp : 0 < p) (hpd : p ≤ d)
    (hd1 : d < 1) (hq0 : 0 < q) (hqμ : q ≤ μ) (hμ1 : μ < 1)
    (hfeas : d * Real.exp (β * certA d w x q) < certU μ w β q) :
    q ∈ certFeasible p μ w β x ∧ Md μ w β x d q ≤ certM p μ w β x q := by
  have hq1 : q < 1 := lt_of_le_of_lt hqμ hμ1
  by_cases hp' : certA p w x q ≤ certB μ w q
  · refine ⟨⟨hq0, hqμ, Or.inl hp'⟩, ?_⟩
    unfold certM; rw [if_pos hp']
    exact Md_le_certB hβ (lt_of_lt_of_le hp hpd) hd1 hfeas
  · have hBA : certB μ w q < certA p w x q := lt_of_not_ge hp'
    have hAe := certA_mono (w := w) (x := x) (q := q) hp hpd hq0 hq1 hx
    have hpf : p * Real.exp (β * certA p w x q) < certU μ w β q := by
      have : p * Real.exp (β * certA p w x q) ≤ d * Real.exp (β * certA d w x q) :=
        mul_le_mul hpd (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hAe hβ.le))
          (Real.exp_pos _).le (by linarith)
      linarith
    refine ⟨⟨hq0, hqμ, Or.inr ⟨hBA, hpf⟩⟩, ?_⟩
    unfold certM; rw [if_neg hp']
    exact Md_antitone hβ hx hq0 hq1 hp hpd hd1 hfeas hBA

end DiagRamsey.SE
