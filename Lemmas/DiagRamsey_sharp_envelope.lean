import Mathlib
import Definitions.Def_DiagRamsey_WeightedHost
import Definitions.Def_DiagRamsey_Cert
import Lemmas.DiagRamsey_SE_Assembly
import Lemmas.DiagRamsey_SE_Drift
import Lemmas.DiagRamsey_SE_Conc

/-! Proof of the positive-weight sharp envelope (`positive_weight_sharp_envelope_proof`), from the
real-variable assembly `SE.assembly` and the finite graph-side lemmas (`SE.drift`, `SE.row_RB`,
`SE.crop`, `SE.m_point`, ...). -/

open Classical

namespace DiagRamsey

set_option maxHeartbeats 2000000 in
theorem positive_weight_sharp_envelope_proof (p μ w β x : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx0 : 0 < x) (hxp : x < p) (hxμ : x < (1 - μ) ^ w)
    (hF : (certFeasible p μ w β x).Nonempty) (hcert : cert p μ w β x < 0) :
    ∃ η τ ζ R : ℝ, 0 < η ∧ 0 < τ ∧ 0 < ζ ∧ w < R ∧ 1 < β * R ∧
      ∀ r : ℝ, R ≤ r →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G B : SimpleGraph V) (X Y : Finset V) (c : ℝ),
        X.Nonempty → Y.Nonempty → Disjoint X Y → |c - p| ≤ η →
        (∀ y ∈ Y, c < colDensity G X y) →
        RowColMaximal G X Y c w r (β * r) →
        (∀ i ∈ X, 0 < graphFrac B X i →
          SharpBlueFailure G B X Y c μ w β (β * r) i) →
        ∀ Xg : Finset V, Xg ⊆ X →
          (X.card : ℝ) - (Xg.card : ℝ) ≤ ζ * (X.card : ℝ) →
          (∀ i ∈ Xg,
            graphFrac B X i ≤ μ + τ ∧
            SharpRedFailure G B X Y c w β (β * r) x i) →
          False := by
  obtain ⟨δ', hδ', hδp, hμδ, φ0, hφ0, R1, hasm⟩ :=
    SE.assembly hp0 hp1 hμ0 hμ1 hw hβ0 hβ1 hx0 hxp hF hcert
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = δ' / 8 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  obtain ⟨κ1, hκ1⟩ : ∃ k : ℝ, k = min (1 / 2) (min (δ' / 64) (φ0 * t / 4)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ1 := by rw [hκ1]; positivity
  have hκa : κ1 ≤ 1 / 2 := by rw [hκ1]; exact min_le_left _ _
  have hκb : κ1 ≤ δ' / 64 := by rw [hκ1]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hκc : κ1 ≤ φ0 * t / 4 := by rw [hκ1]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ε, hε⟩ : ∃ e : ℝ, e = δ' / 32 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨Rθ, hRθ0, hRθ⟩ := SE.theta_tend hβ0 hβ1 hκ0
  obtain ⟨Rt, hRt0, hRt⟩ := SE.tail_tend (β := β) hβ1 hε0 hε0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max (max R1 (2 * w + 1))
      (max (max (2 / β) (16 * w / (φ0 * t) + 1)) (max Rθ Rt)) := ⟨_, rfl⟩
  have hR1 : R1 ≤ R := by rw [hR]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hR2 : 2 * w + 1 ≤ R := by rw [hR]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hR3 : 2 / β ≤ R := by
    rw [hR]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hR4 : 16 * w / (φ0 * t) + 1 ≤ R := by
    rw [hR]; exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hR5 : Rθ ≤ R := by
    rw [hR]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hR6 : Rt ≤ R := by
    rw [hR]; exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨δ' / 2, δ', φ0 / 2, R, by positivity, hδ', by positivity, by linarith, ?_, ?_⟩
  · rw [div_le_iff₀ hβ0] at hR3; linarith
  intro r hr V _ _ G B X Y c hX hY hXY hc hpos hRC hblue Xg hXgX hXgcard hXg
  have hr0 : 0 < r := by linarith
  have hwr : w < r := by linarith
  have h2wr : 2 * w ≤ r := by linarith
  have hs1 : 1 ≤ β * r := by
    have := le_trans hR3 hr
    rw [div_le_iff₀ hβ0] at this; linarith
  have hs0 : 0 < β * r := by linarith
  have hsr : β * r < r := by nlinarith
  have hwr16 : w / r ≤ φ0 * t / 16 := by
    have hpos' : 0 < φ0 * t := by positivity
    have h1 : 16 * w / (φ0 * t) ≤ r := by linarith
    rw [div_le_iff₀ hpos'] at h1
    rw [div_le_iff₀ hr0]; linarith
  obtain ⟨hc1, hc2⟩ := abs_le.1 hc
  have hcpos : 0 < c := by linarith
  obtain ⟨y0, hy0⟩ := id hY
  have hc_lt1 : c < 1 := lt_of_lt_of_le (hpos y0 hy0) (by unfold colDensity; exact SE.frac_le_one X _)
  have habsc : |c| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hrow := hRC.1
  have hcol := hRC.2
  have hH0 := SE.H_pos G X Y c (β * r) hY hpos
  have hH1 := SE.H_le_one G X Y c (β * r) hY hpos hcpos.le hs0
  have hlow := DiagRamsey.ClosureEnv.wgp_col_lower G X Y c w r (β * r) hs0 hsr hX hY hH0 hcol
  have hβr : β * r / r = β := by field_simp
  rw [hβr] at hlow
  have htail := SE.crop G X Y c (β * r) w r hX hY hpos hs0 hsr hcol ε hε0.le
  have hL1π0 := SE.L1_pi G X Y c (β * r) w r ((1 - β) ^ (1 / (β * r))) hw hwr hs1 hX hY hpos
    hlow hrow
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = momentNorm G X Y c (β * r) := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 - β) ^ (1 / (β * r)) := ⟨_, rfl⟩
  rw [← hHdef] at hH0 hH1 htail hL1π0 hlow
  rw [← hθ] at hlow hL1π0
  have hθ0 : 0 < θ := by rw [hθ]; exact Real.rpow_pos_of_pos (by linarith) _
  have hθ1 : θ ≤ 1 := by rw [hθ]; exact Real.rpow_le_one (by linarith) (by linarith) (by positivity)
  have hθκ : 1 - θ ≤ κ1 := by rw [hθ]; exact hRθ r (le_trans hR5 hr)
  have hθinv : 1 / θ - 1 ≤ 2 * κ1 := by
    have h12 : 1 / 2 ≤ θ := by linarith
    rw [div_sub_one hθ0.ne', div_le_iff₀ hθ0]
    nlinarith [mul_le_mul_of_nonneg_left h12 hκ0.le]
  have hlow' : ∀ y ∈ Y, θ * H ≤ SE.uC G X c y := hlow
  have htail' : (1 + ε) ^ (β * r - r) ≤ ε := hRt r (le_trans hR6 hr)
  have hρ := SE.rho_bound G X Y c (β * r) hY hpos H θ ε hθ0 hθ1 hε0.le hH0 hlow'
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ∑ y ∈ Y, SE.nuW G X Y c (β * r) y * |1 - H / SE.uC G X c y| :=
    ⟨_, rfl⟩
  rw [← hρdef] at hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    exact Finset.sum_nonneg fun y hy =>
      mul_nonneg (SE.nu_nonneg G X Y c (β * r) hY hpos hy) (abs_nonneg _)
  have hρle : ρ ≤ δ' / 8 := by linarith
  -- sorted drift
  have hγ : 0 < 1 - w / r := by rw [sub_pos, div_lt_one hr0]; exact hwr
  obtain ⟨idx, hmem, hsumF, hdrift⟩ := SE.drift X hX (graphFrac B X) (SE.Vr G X Y c (β * r)) r
    (1 - w / r) hr0 hγ (SE.sumV G X Y c (β * r) hX hY hpos)
    (fun A hA hAn => SE.Sbin G X Y c (β * r) w r hX hY hpos hr0 hs1 hrow A hA hAn)
  have hNpos : 0 < X.card := hX.card_pos
  have hN' : (0:ℝ) < X.card := by exact_mod_cast hNpos
  -- good rows
  obtain ⟨Good, hGood⟩ : ∃ S : Finset V, S = Xg.filter (fun i =>
      |rowDensity G i Y - (c + H)| ≤ t ∧ |SE.Vr G X Y c (β * r) i - 1| ≤ t) := ⟨_, rfl⟩
  obtain ⟨Gd, hGd⟩ : ∃ S : Finset ℕ, S = (Finset.range X.card).filter (fun k => idx k ∈ Good) :=
    ⟨_, rfl⟩
  have hGoodX : Good ⊆ X := by rw [hGood]; exact (Finset.filter_subset _ _).trans hXgX
  have hGdcard : (Gd.card : ℝ) = Good.card := by
    have e := hsumF (fun i => if i ∈ Good then (1:ℝ) else 0)
    simp only [Finset.sum_boole] at e
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hGoodX] at e
    rw [hGd]; exact e.symm
  have hcg := SE.card_good X Xg hXgX (fun i => |rowDensity G i Y - (c + H)| ≤ t)
    (fun i => |SE.Vr G X Y c (β * r) i - 1| ≤ t)
  have hP := SE.markov_card X (fun i => |rowDensity G i Y - (c + H)|) (fun i _ => abs_nonneg _) t ht0
  have hQ := SE.markov_card X (fun i => |SE.Vr G X Y c (β * r) i - 1|) (fun i _ => abs_nonneg _) t
    ht0
  beta_reduce at hcg hP hQ
  have eP : X.filter (fun i => ¬ |rowDensity G i Y - (c + H)| ≤ t) =
      X.filter (fun i => t < |rowDensity G i Y - (c + H)|) := Finset.filter_congr fun i _ => not_le
  have eQ : X.filter (fun i => ¬ |SE.Vr G X Y c (β * r) i - 1| ≤ t) =
      X.filter (fun i => t < |SE.Vr G X Y c (β * r) i - 1|) := Finset.filter_congr fun i _ => not_le
  rw [eP, eQ, ← hGood] at hcg
  have hL1V := SE.L1_V G X Y c (β * r) w r hX hY hpos hr0 hs1 hw.le hwr.le hrow
  rw [le_div_iff₀ ht0] at hP hQ
  have hπb : ∑ i ∈ X, |rowDensity G i Y - (c + H)| ≤ X.card * (κ1 + 2 * (w / r)) := by
    have a1 : (1 - θ) * H ≤ κ1 := by
      nlinarith [mul_le_mul_of_nonneg_left hH1 (sub_nonneg.2 hθ1)]
    have a2 : 2 * (w / r) * H ≤ 2 * (w / r) := by
      have := mul_le_mul_of_nonneg_left hH1 (by positivity : 0 ≤ 2 * (w / r)); linarith
    have := mul_le_mul_of_nonneg_left (add_le_add a1 a2) hN'.le
    linarith
  have hcount : (X.card : ℝ) - Gd.card ≤ φ0 * X.card := by
    rw [hGdcard]
    have b1 : (X.card : ℝ) * κ1 ≤ X.card * (φ0 * t / 4) := mul_le_mul_of_nonneg_left hκc hN'.le
    have b2 : (X.card : ℝ) * (w / r) ≤ X.card * (φ0 * t / 16) :=
      mul_le_mul_of_nonneg_left hwr16 hN'.le
    have b3 : (((X.filter (fun i => t < |rowDensity G i Y - (c + H)|)).card : ℝ) +
        ((X.filter (fun i => t < |SE.Vr G X Y c (β * r) i - 1|)).card : ℝ)) * t ≤
        (φ0 / 2 * X.card) * t := by nlinarith
    have b4 := le_of_mul_le_mul_right b3 ht0
    linarith
  refine hasm r (le_trans hR1 hr) X.card hNpos (fun k => graphFrac B X (idx k))
    (fun k => graphFrac B X (idx k) * SE.Er G B X Y c (β * r) (idx k))
    (fun k => SE.mr G X Y c (β * r) (idx k)) (fun k => rowDensity G (idx k) Y) Gd
    (by rw [hGd]; exact Finset.filter_subset _ _) hcount ?_ ?_ ?_ ?_
  · intro k _
    beta_reduce
    exact ⟨by unfold graphFrac graphNbhd; exact SE.frac_nonneg X _,
      by unfold graphFrac graphNbhd; exact SE.frac_le_one X _⟩
  · beta_reduce
    have e1 := hsumF (fun i => graphFrac B X i * (SE.Vr G X Y c (β * r) i - 1))
    have e2 := hsumF (fun i => graphFrac B X i * SE.Er G B X Y c (β * r) i)
    beta_reduce at e1 e2
    have hst := SE.stationarity G B X Y c (β * r) hY hpos
    rw [← e2, hst, e1]; exact hdrift
  · intro k hk
    beta_reduce
    have hi := hmem k hk
    rcases (show 0 ≤ graphFrac B X (idx k) by
      unfold graphFrac graphNbhd; exact SE.frac_nonneg X _).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, mul_zero]; exact hw.le
    · exact SE.ub_scalar h0 hμ0 hμ1 hw h2wr
        (SE.row_E_le G B X Y c hY hpos hμ0 hβ0 hr0 hs1 (idx k) h0 (hblue _ hi h0))
  · intro k hk
    beta_reduce
    rw [hGd, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkN, hkG⟩ := hk
    rw [hGood, Finset.mem_filter] at hkG
    obtain ⟨hiXg, hπt, hVt⟩ := hkG
    have hiX := hXgX hiXg
    obtain ⟨hqμ, hred⟩ := hXg _ hiXg
    have hmp := SE.m_point G X Y c (β * r) hY hpos H hH0.le (idx k)
    rw [← hρdef] at hmp
    have hm_close : |SE.mr G X Y c (β * r) (idx k) - (c + H)| ≤ 3 * δ' / 8 := by
      have c1 : (1 + |c|) * ρ ≤ 2 * ρ := by nlinarith [mul_le_mul_of_nonneg_right habsc hρ0]
      have c2 : H * |SE.Vr G X Y c (β * r) (idx k) - 1| ≤ t := by
        calc _ ≤ 1 * t := mul_le_mul hH1 hVt (abs_nonneg _) zero_le_one
          _ = t := one_mul t
      linarith
    obtain ⟨hm1, hm2⟩ := abs_le.1 hm_close
    obtain ⟨hπ1, hπ2⟩ := abs_le.1 hπt
    have hmle := SE.mr_le_one G X Y c (β * r) hY hpos (idx k)
    have hπle : rowDensity G (idx k) Y ≤ 1 := by unfold rowDensity; exact SE.frac_le_one Y _
    have hmpos : 0 < SE.mr G X Y c (β * r) (idx k) := by linarith
    have hπpos : 0 < rowDensity G (idx k) Y := by linarith
    refine ⟨by linarith, by linarith, hmle, by linarith, hπle, ?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · intro hq0; exact SE.row_q0 G B X Y c hY hpos (idx k) hq0 hred
    · intro hq0
      have hq1 : graphFrac B X (idx k) < 1 := by linarith
      have e : graphFrac B X (idx k) * SE.Er G B X Y c (β * r) (idx k) / graphFrac B X (idx k) =
          SE.Er G B X Y c (β * r) (idx k) := by field_simp
      rw [e]
      exact SE.row_RB G B X Y c hY hpos hβ0 hr0 hs1 hμ0 hx0 (idx k) hq0 hq1 hmpos hπpos
        (hblue _ hiX hq0) hred

end DiagRamsey
