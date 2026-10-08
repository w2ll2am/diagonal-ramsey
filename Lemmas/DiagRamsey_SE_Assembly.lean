import Mathlib
import Lemmas.DiagRamsey_SE_PRL
import Lemmas.DiagRamsey_SE_Excl
import Lemmas.DiagRamsey_SE_Calc
import Lemmas.DiagRamsey_SE_Cell

open MeasureTheory

namespace DiagRamsey.SE

lemma cell_mem {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    0 ≤ (k:ℝ) / N ∧ (k:ℝ) / N ≤ ((k:ℝ) + 1) / N ∧ ((k:ℝ) + 1) / N ≤ 1 ∧
      ((k:ℝ) + 1) / N - (k:ℝ) / N = 1 / N := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hk' : (k:ℝ) + 1 ≤ N := by exact_mod_cast hk
  refine ⟨by positivity, div_le_div_of_nonneg_right (by linarith) hN'.le, (div_le_one hN').2 hk', ?_⟩
  rw [← sub_div]; congr 1; ring

lemma sum_dJ_le {N : ℕ} (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Finset.range N) (a : ℝ) :
    ∑ k ∈ S, (JF (((k:ℝ) + 1) / N) - JF ((k:ℝ) / N)) ≤
      (2 + a) * ((S.card:ℝ) / N) + Real.exp (-a - 1) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hanti : Antitone (fun k : ℕ => JF (((k:ℝ) + 1) / N) - JF ((k:ℝ) / N)) := by
    apply antitone_nat_of_succ_le
    intro k
    have := JF_incr_anti (a := (k:ℝ) / N) (h := 1 / N) (by positivity) (by positivity)
    have e1 : (k:ℝ) / N + 2 * (1 / N) = ((k:ℝ) + 1 + 1) / N := by field_simp; ring
    have e2 : (k:ℝ) / N + 1 / N = ((k:ℝ) + 1) / N := by field_simp
    rw [e1, e2] at this
    simp only [Nat.cast_add, Nat.cast_one]
    exact this
  have h1 := sum_le_sum_range_card_of_antitone hanti S
  have htel : ∑ k ∈ Finset.range S.card, (JF (((k:ℝ) + 1) / N) - JF ((k:ℝ) / N)) =
      JF ((S.card:ℝ) / N) := by
    have := Finset.sum_range_sub (fun k : ℕ => JF ((k:ℝ) / N)) S.card
    simp only [Nat.cast_add, Nat.cast_one] at this
    rw [this]; simp [JF_zero]
  have hφ0 : 0 ≤ (S.card:ℝ) / N := by positivity
  have hJ : JF ((S.card:ℝ) / N) ≤ (2 + a) * ((S.card:ℝ) / N) + Real.exp (-a - 1) := by
    unfold JF; have := neg_mul_log_le ((S.card:ℝ) / N) a hφ0; linarith
  linarith

lemma lower_sum {w r : ℝ} {N : ℕ} (hN : 0 < N) (hw : 0 < w) (hr : 2 * w ≤ r) (qs Ps : ℕ → ℝ)
    (hq : ∀ k < N, 0 ≤ qs k ∧ qs k ≤ 1)
    (hdrift : (N:ℝ) * ∑ k ∈ Finset.range N, qs k * (PhiK r (1 - w / r) (((k:ℝ) + 1) / N) -
      PhiK r (1 - w / r) ((k:ℝ) / N)) ≤ r * ∑ k ∈ Finset.range N, Ps k) :
    -(4 * w ^ 2 / r) ≤ ∑ k ∈ Finset.range N,
      (r * Ps k / N + w * qs k * (PhiL (((k:ℝ) + 1) / N) - PhiL ((k:ℝ) / N))) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 < r := by linarith
  set g := 1 - w / r with hgdef
  have hg : r * g = r - w := by rw [hgdef]; field_simp
  have hg0 : 0 < g := by rw [hgdef, sub_pos, div_lt_one hr0]; linarith
  have hg1 : g < 1 := by have : 0 < w / r := div_pos hw hr0; linarith
  have hcell : ∀ k ∈ Finset.range N,
      -(Phi2 w r g (((k:ℝ) + 1) / N) - Phi2 w r g ((k:ℝ) / N)) ≤
      qs k * (PhiK r g (((k:ℝ) + 1) / N) - PhiK r g ((k:ℝ) / N)) +
        w * qs k * (PhiL (((k:ℝ) + 1) / N) - PhiL ((k:ℝ) / N)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨h0, h1, h2, -⟩ := cell_mem hN hk
    have hb := phi_bound hw hr0 hg0 hg1 hg h0 h1 h2
    obtain ⟨hq0, hq1⟩ := hq k hk
    have habs := (abs_le.1 hb).1
    have hD : 0 ≤ Phi2 w r g (((k:ℝ) + 1) / N) - Phi2 w r g ((k:ℝ) / N) := (abs_nonneg _).trans hb
    nlinarith [mul_le_mul_of_nonneg_left habs hq0, mul_nonneg (sub_nonneg.2 hq1) hD]
  have htel : ∑ k ∈ Finset.range N, (Phi2 w r g (((k:ℝ) + 1) / N) - Phi2 w r g ((k:ℝ) / N)) =
      Phi2 w r g 1 - Phi2 w r g 0 := by
    have := Finset.sum_range_sub (fun k : ℕ => Phi2 w r g ((k:ℝ) / N)) N
    simp only [Nat.cast_add, Nat.cast_one] at this
    rw [this, div_self hN'.ne', Nat.cast_zero, zero_div]
  have htot := phi2_total hw hr0 hg hr
  have hsum := Finset.sum_le_sum hcell
  rw [Finset.sum_neg_distrib, htel, Finset.sum_add_distrib] at hsum
  have h1 : ∑ k ∈ Finset.range N, qs k * (PhiK r g (((k:ℝ) + 1) / N) - PhiK r g ((k:ℝ) / N)) ≤
      (r * ∑ k ∈ Finset.range N, Ps k) / N := by
    rw [le_div_iff₀ hN']; linarith [hdrift]
  have h2 : ∑ k ∈ Finset.range N,
      (r * Ps k / N + w * qs k * (PhiL (((k:ℝ) + 1) / N) - PhiL ((k:ℝ) / N))) =
      (r * ∑ k ∈ Finset.range N, Ps k) / N + ∑ k ∈ Finset.range N,
        w * qs k * (PhiL (((k:ℝ) + 1) / N) - PhiL ((k:ℝ) / N)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  rw [h2]
  linarith

/-- Cost of a row compared with a fixed feasible `q0`. -/
lemma cost_vs_q0 {N r P q q0 M0 w ΔL ΔJ I Bd C0 : ℝ} (hN : 0 < N) (hw : 0 ≤ w)
    (hq : 0 ≤ q ∧ q ≤ 1) (hq0 : 0 ≤ q0 ∧ q0 ≤ 1) (hC0 : |q0 * M0| ≤ C0) (hL : |ΔL| ≤ ΔJ)
    (hlow : 1 / N * (q0 * M0) + w * q0 * ΔL ≤ I) (hP : r * P ≤ Bd) :
    r * P / N + w * q * ΔL - I ≤ (Bd + C0) / N + w * ΔJ := by
  have h1 : r * P / N ≤ Bd / N := div_le_div_of_nonneg_right hP hN.le
  have h2 : -(1 / N * (q0 * M0)) ≤ C0 / N := by
    have := neg_abs_le (q0 * M0)
    rw [show -(1 / N * (q0 * M0)) = -(q0 * M0) / N by ring]
    exact div_le_div_of_nonneg_right (by linarith [neg_le_abs (q0 * M0)]) hN.le
  have h3 : w * (q - q0) * ΔL ≤ w * ΔJ := by
    have hqq : |q - q0| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have : (q - q0) * ΔL ≤ ΔJ := by
      calc (q - q0) * ΔL ≤ |(q - q0) * ΔL| := le_abs_self _
        _ = |q - q0| * |ΔL| := abs_mul _ _
        _ ≤ 1 * ΔJ := mul_le_mul hqq hL (abs_nonneg _) zero_le_one
        _ = ΔJ := one_mul _
    have := mul_le_mul_of_nonneg_left this hw
    linarith
  have : (Bd + C0) / N = Bd / N + C0 / N := add_div _ _ _
  nlinarith

/-- Cost of a row with a nearby feasible `q'` (first PRL alternative). -/
lemma cost_vs_near {N r P q q' M' w ΔL ΔJ I ε : ℝ} (hN : 0 < N) (hw : 0 ≤ w)
    (hqq : |q' - q| ≤ ε) (hL : |ΔL| ≤ ΔJ)
    (hlow : 1 / N * (q' * M') + w * q' * ΔL ≤ I) (hP : r * P ≤ q' * M' + ε) :
    r * P / N + w * q * ΔL - I ≤ ε / N + w * ε * ΔJ := by
  have h1 : r * P / N ≤ (q' * M' + ε) / N := div_le_div_of_nonneg_right hP hN.le
  have h3 : (q - q') * ΔL ≤ ε * ΔJ := by
    calc (q - q') * ΔL ≤ |(q - q') * ΔL| := le_abs_self _
      _ = |q' - q| * |ΔL| := by rw [abs_mul, abs_sub_comm]
      _ ≤ ε * ΔJ := mul_le_mul hqq hL (abs_nonneg _) ((abs_nonneg _).trans hqq)
  have h4 := mul_le_mul_of_nonneg_left h3 hw
  have : (q' * M' + ε) / N = 1 / N * (q' * M') + ε / N := by ring
  nlinarith

set_option maxHeartbeats 1000000 in
theorem assembly {p μ w β x : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1) (hx0 : 0 < x) (hxp : x < p)
    (hF : (certFeasible p μ w β x).Nonempty) (hcert : cert p μ w β x < 0) :
    ∃ δ' > 0, δ' < p / 2 ∧ μ + δ' < 1 ∧ ∃ φ0 > 0, ∃ R1 : ℝ, ∀ r ≥ R1, ∀ N : ℕ, 0 < N →
      ∀ qs Ps ms πs : ℕ → ℝ, ∀ Gd : Finset ℕ, Gd ⊆ Finset.range N →
      (N:ℝ) - Gd.card ≤ φ0 * N →
      (∀ k < N, 0 ≤ qs k ∧ qs k ≤ 1) →
      (N:ℝ) * ∑ k ∈ Finset.range N, qs k * (PhiK r (1 - w / r) (((k:ℝ) + 1) / N) -
        PhiK r (1 - w / r) ((k:ℝ) / N)) ≤ r * ∑ k ∈ Finset.range N, Ps k →
      (∀ k < N, r * Ps k ≤ w) →
      (∀ k ∈ Gd, qs k ≤ μ + δ' ∧ p - δ' ≤ ms k ∧ ms k ≤ 1 ∧ p - δ' ≤ πs k ∧ πs k ≤ 1 ∧
         |ms k - πs k| ≤ δ' ∧ (qs k = 0 → ms k < x ^ β * πs k ^ (1 - β)) ∧
         (0 < qs k → RowBound μ w β x (qs k) (ms k) (πs k) r (Ps k / qs k))) →
      False := by
  classical
  obtain ⟨q0, hq0F⟩ := hF
  have hq0b : 0 ≤ q0 ∧ q0 ≤ 1 := ⟨hq0F.1.le, hq0F.2.1.trans hμ1.le⟩
  set C := -cert p μ w β x with hC
  have hCpos : 0 < C := by linarith
  set C0 := |q0 * certM p μ w β x q0| with hC0
  have hC0n : 0 ≤ C0 := abs_nonneg _
  set a := 16 * w / C with ha
  have hapos : 0 < a := by positivity
  have hea : w * Real.exp (-a - 1) ≤ C / 16 := by
    have h1 : a + 2 ≤ Real.exp (a + 1) := by linarith [Real.add_one_le_exp (a + 1)]
    have h2 : Real.exp (-a - 1) = 1 / Real.exp (a + 1) := by
      rw [one_div, ← Real.exp_neg]; ring_nf
    rw [h2]
    have h3 : 1 / Real.exp (a + 1) ≤ 1 / a := one_div_le_one_div_of_le hapos (by linarith)
    have h4 : w * (1 / a) = C / 16 := by rw [ha]; field_simp
    linarith [mul_le_mul_of_nonneg_left h3 hw.le]
  set ε := C / (16 * (1 + 2 * w)) with hε
  have hεpos : 0 < ε := by positivity
  have hεC : ε + w * ε * 2 = C / 16 := by rw [hε]; field_simp
  set K := C0 + w * (2 + a) with hK
  obtain ⟨δe, hδe, δ'e, hδ'e, Re, hexcl⟩ := excl hp0 hμ0 hμ1 hw hβ0 hx0 hxp
  obtain ⟨δ'0, hδ'0, hexcl0⟩ := excl0 hp0 hβ0 hβ1 hx0 hxp
  obtain ⟨δ'P, hδ'P, RP, hprl⟩ := prl (w := w) hp0 hμ1 hμ0 hβ0 hx0 hδe hεpos K
  set δ' := min (min (min δ'e δ'0) δ'P) (min (p / 4) ((1 - μ) / 4)) with hδ'
  have hδ'1 : δ' ≤ δ'e := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ'2 : δ' ≤ δ'0 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ'3 : δ' ≤ δ'P := (min_le_left _ _).trans (min_le_right _ _)
  have hδ'4 : δ' ≤ p / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ'5 : δ' ≤ (1 - μ) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hδ'pos : 0 < δ' := lt_min (lt_min (lt_min hδ'e hδ'0) hδ'P)
    (lt_min (by linarith) (by linarith))
  set φ0 := C / (16 * (1 + w + C0 + w * (2 + a))) with hφ0
  have hφ0pos : 0 < φ0 := by positivity
  have hφ0C : φ0 * (w + C0 + w * (2 + a)) ≤ C / 16 := by
    rw [hφ0, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ C * (w + C0 + w * (2 + a)) := by positivity
    linarith
  refine ⟨δ', hδ'pos, by linarith, by linarith, φ0, hφ0pos,
    max (max Re RP) (max (2 * w) (64 * w ^ 2 / C)), ?_⟩
  intro r hr N hN qs Ps ms πs Gd hGd hcard hq hdrift hub hgood
  have hrRe : Re ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr
  have hrRP : RP ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hr
  have hr2w : 2 * w ≤ r := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hr
  have hrC : 64 * w ^ 2 / C ≤ r := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hr
  have hr0 : 0 < r := by linarith
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hI := integrable_of_cert_neg hcert
  have h4w : 4 * w ^ 2 / r ≤ C / 16 := by
    rw [div_le_iff₀ hr0]
    rw [div_le_iff₀ hCpos] at hrC
    linarith
  -- per-cell notation
  set ΔL : ℕ → ℝ := fun k => PhiL (((k:ℝ) + 1) / N) - PhiL ((k:ℝ) / N) with hΔL
  set ΔJ : ℕ → ℝ := fun k => JF (((k:ℝ) + 1) / N) - JF ((k:ℝ) / N) with hΔJ
  set I : ℕ → ℝ := fun k => ∫ t in ((k:ℝ) / N)..(((k:ℝ) + 1) / N), certIntegrand p μ w β x t
    with hIdef
  set S2 := Gd.filter (fun k => r * Ps k ≤ -K) with hS2
  set S3 := Finset.range N \ Gd with hS3
  have hS2sub : S2 ⊆ Finset.range N := (Finset.filter_subset _ _).trans hGd
  have hS3sub : S3 ⊆ Finset.range N := Finset.sdiff_subset
  have hlowsum := lower_sum hN hw hr2w qs Ps hq hdrift
  have hcellsum : ∑ k ∈ Finset.range N, I k = cert p μ w β x := by
    have := cells_sum (f := certIntegrand p μ w β x) hN hI
    push_cast at this
    exact this
  have hbound : ∀ k ∈ Finset.range N,
      r * Ps k / N + w * qs k * ΔL k - I k ≤ (ε / N + w * ε * ΔJ k) +
        ((if k ∈ S2 then (-K + C0) / N + w * ΔJ k else 0) +
         (if k ∈ S3 then (w + C0) / N + w * ΔJ k else 0)) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    obtain ⟨c1, c2, c3, c4⟩ := cell_mem hN hk'
    have hLJ : |ΔL k| ≤ ΔJ k := phiL_bound c1 c2 c3
    have hJ0 : 0 ≤ ΔJ k := (abs_nonneg _).trans hLJ
    have hlowq : ∀ q' ∈ certFeasible p μ w β x,
        1 / N * (q' * certM p μ w β x q') + w * q' * ΔL k ≤ I k := by
      intro q' hq'
      have := cell_lower hp0 hp1 hβ0 hw.le hμ0 hμ1 c1 c2 c3 hI hq'
      rw [c4] at this; exact this
    have hbase : 0 ≤ ε / N + w * ε * ΔJ k := by positivity
    by_cases hkG : k ∈ Gd
    · have hk3 : k ∉ S3 := fun h => (Finset.mem_sdiff.1 h).2 hkG
      rw [if_neg hk3, add_zero]
      by_cases hk2 : r * Ps k ≤ -K
      · have hkS2 : k ∈ S2 := Finset.mem_filter.2 ⟨hkG, hk2⟩
        rw [if_pos hkS2]
        have := cost_vs_q0 hN' hw.le (hq k hk') hq0b (le_refl C0) hLJ (hlowq q0 hq0F) hk2
        have e : (-K + C0) / N = (-K + C0) / N := rfl
        linarith
      · have hkS2 : k ∉ S2 := fun h => hk2 (Finset.mem_filter.1 h).2
        rw [if_neg hkS2, add_zero]
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hgood k hkG
        have hqpos : 0 < qs k := by
          rcases (hq k hk').1.lt_or_eq with h | h
          · exact h
          · exfalso
            exact hexcl0 (ms k) (πs k) (by linarith) g3 (by linarith) (g6.trans hδ'2) (g7 h.symm)
        have hRB := g8 hqpos
        have hqδ : δe ≤ qs k := by
          by_contra hlt
          exact hexcl r hrRe (qs k) (ms k) (πs k) (Ps k / qs k) hqpos (lt_of_not_ge hlt)
            (by linarith) g3 (by linarith) g5 (g6.trans hδ'1) hRB
        have hqrE : qs k * r * (Ps k / qs k) = r * Ps k := by field_simp
        rcases hprl r hrRP (qs k) (ms k) (πs k) (Ps k / qs k) hqδ (by linarith) (by linarith) g3
            (by linarith) g5 (g6.trans hδ'3) hRB with ⟨q', hq'F, hq'd, hq'b⟩ | hK'
        · rw [hqrE] at hq'b
          exact cost_vs_near hN' hw.le hq'd hLJ (hlowq q' hq'F) hq'b
        · rw [hqrE] at hK'
          exact absurd hK' hk2
    · have hk3 : k ∈ S3 := Finset.mem_sdiff.2 ⟨hk, hkG⟩
      have hk2 : k ∉ S2 := fun h => hkG (Finset.mem_filter.1 h).1
      rw [if_pos hk3, if_neg hk2, zero_add]
      have := cost_vs_q0 hN' hw.le (hq k hk') hq0b (le_refl C0) hLJ (hlowq q0 hq0F) (hub k hk')
      linarith
  have hsum := Finset.sum_le_sum hbound
  have hsplit : ∑ k ∈ Finset.range N, ((if k ∈ S2 then (-K + C0) / N + w * ΔJ k else 0) +
      (if k ∈ S3 then (w + C0) / N + w * ΔJ k else 0)) =
      ∑ k ∈ S2, ((-K + C0) / N + w * ΔJ k) + ∑ k ∈ S3, ((w + C0) / N + w * ΔJ k) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 hS2sub, Finset.inter_eq_right.2 hS3sub]
  rw [Finset.sum_sub_distrib, hcellsum, Finset.sum_add_distrib (s := Finset.range N)
    (f := fun k => ε / N + w * ε * ΔJ k), hsplit] at hsum
  -- evaluate the pieces
  have hall : ∑ k ∈ Finset.range N, (ε / N + w * ε * ΔJ k) = ε + w * ε * 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    have := Finset.sum_range_sub (fun k : ℕ => JF ((k:ℝ) / N)) N
    simp only [Nat.cast_add, Nat.cast_one] at this
    rw [hΔJ]; simp only
    rw [this, div_self hN'.ne', Nat.cast_zero, zero_div, JF_zero]
    unfold JF; rw [Real.log_one]; field_simp; ring
  have hS2b : ∑ k ∈ S2, ((-K + C0) / N + w * ΔJ k) ≤ w * Real.exp (-a - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have hJ := sum_dJ_le hN S2 hS2sub a
    have hm := mul_le_mul_of_nonneg_left hJ hw.le
    have : (S2.card : ℝ) * ((-K + C0) / N) = -(w * (2 + a)) * ((S2.card : ℝ) / N) := by
      rw [hK]; ring
    rw [this]
    linarith
  have hS3card : (S3.card : ℝ) ≤ φ0 * N := by
    rw [hS3, Finset.card_sdiff_of_subset hGd, Finset.card_range, Nat.cast_sub (Finset.card_le_card hGd |>.trans (by simp))]
    exact hcard
  have hS3b : ∑ k ∈ S3, ((w + C0) / N + w * ΔJ k) ≤ C / 16 + w * Real.exp (-a - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have hJ := sum_dJ_le hN S3 hS3sub a
    have hm := mul_le_mul_of_nonneg_left hJ hw.le
    have hφ : (S3.card : ℝ) / N ≤ φ0 := by rw [div_le_iff₀ hN']; exact hS3card
    have hφn : 0 ≤ (S3.card : ℝ) / N := by positivity
    have : (S3.card : ℝ) * ((w + C0) / N) = (w + C0) * ((S3.card : ℝ) / N) := by ring
    rw [this]
    have h5 : (w + C0 + w * (2 + a)) * ((S3.card : ℝ) / N) ≤ (w + C0 + w * (2 + a)) * φ0 :=
      mul_le_mul_of_nonneg_left hφ (by positivity)
    linarith
  rw [hall] at hsum
  have hc : -(4 * w ^ 2 / r) ≤ ∑ k ∈ Finset.range N, (r * Ps k / N + w * qs k * ΔL k) := hlowsum
  linarith

end DiagRamsey.SE
