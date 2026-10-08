import Lemmas.DiagRamsey_closure_induction
import Definitions.Def_DiagRamsey_Cert

/-! `positive_weight_finite_host_closure_of_envelope`: the closure theorem
(`Theorems/Thm_DiagRamsey_positive_weight_finite_host_closure.lean`) with the exact proposition of
`positive_weight_sharp_envelope` taken as an explicit hypothesis `henv`. Proof:
`proofs/DiagRamsey_positive_weight_finite_host_closure.md`, using only the statement of the envelope. -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DiagRamsey.ClosureEnv

/-- `(n + m_n)^{m_n} ≤ K e^{an}` when `m_n ≤ μ₀ + μ₁ log n`. -/
lemma Q_bound (a μ₀ μ₁ : ℝ) (ha : 0 < a) (hμ₀ : 0 ≤ μ₀) (hμ₁ : 0 ≤ μ₁) (m : ℕ → ℕ)
    (hm : ∀ n : ℕ, 1 ≤ n → (m n : ℝ) ≤ μ₀ + μ₁ * Real.log n) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → (((n + m n : ℕ)) : ℝ) ^ (m n) ≤ K * Real.exp a ^ n := by
  have hc2 : (1 : ℝ) ≤ 1 + μ₀ + μ₁ := by linarith
  have hlc : 0 ≤ Real.log (1 + μ₀ + μ₁) := Real.log_nonneg hc2
  have hκ : 0 ≤ μ₀ + μ₁ * Real.log (1 + μ₀ + μ₁) := add_nonneg hμ₀ (mul_nonneg hμ₁ hlc)
  obtain ⟨K, hK, hKb⟩ := exp_logsq_le (μ₁ + (μ₀ + μ₁ * Real.log (1 + μ₀ + μ₁)))
    ((μ₀ + μ₁ * Real.log (1 + μ₀ + μ₁)) + μ₀ * Real.log (1 + μ₀ + μ₁)) (Real.exp a)
    (Real.one_lt_exp_iff.mpr ha)
  refine ⟨K, hK, fun n hn => le_trans ?_ (hKb n)⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hLn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hm' := hm n hn
  have hnm : (((n + m n : ℕ)) : ℝ) = (n : ℝ) + m n := by push_cast; ring
  have hpos : 0 < (n : ℝ) + m n := by have := Nat.cast_nonneg (α := ℝ) (m n); linarith
  have hcn : (n : ℝ) + m n ≤ (1 + μ₀ + μ₁) * n := by
    have e1 := mul_le_mul_of_nonneg_left hn1 hμ₀
    have e2 := mul_le_mul_of_nonneg_left hLn hμ₁
    linarith
  have hlog : Real.log ((n : ℝ) + m n) ≤ Real.log (1 + μ₀ + μ₁) + Real.log n := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log hpos hcn
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + m n) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (m n); linarith)
  rw [hnm, ← Real.exp_log hpos, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h1 : (m n : ℝ) * Real.log ((n : ℝ) + m n) ≤
      (μ₀ + μ₁ * Real.log n) * (Real.log (1 + μ₀ + μ₁) + Real.log n) :=
    mul_le_mul hm' hlog hlog0 (add_nonneg hμ₀ (mul_nonneg hμ₁ hL0))
  have h2 : Real.log n ≤ Real.log n ^ 2 + 1 := by nlinarith [sq_nonneg (Real.log n - 1)]
  have h3 := mul_le_mul_of_nonneg_left h2 hκ
  nlinarith

/-- `n^r ≤ K A^n` for `A > 1`. -/
lemma pow_r_bound (r A : ℝ) (hA : 1 < A) : ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ r ≤ K * A ^ n := by
  obtain ⟨K, hK, hKb⟩ := exp_logsq_le 1 (r ^ 2 / 4) A hA
  refine ⟨K, hK, fun n hn => le_trans ?_ (hKb n)⟩
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn1]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log n - r / 2)]

end DiagRamsey.ClosureEnv

namespace DiagRamsey

open DiagRamsey.ClosureEnv

set_option maxHeartbeats 4000000 in
theorem positive_weight_finite_host_closure_of_envelope (p μ w β x ξ y₀ ν xhat yhat : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx0 : 0 < x) (hxp : x < p) (hxμ : x < (1 - μ) ^ w)
    (hF : (certFeasible p μ w β x).Nonempty) (hcert : cert p μ w β x < 0)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hy0 : 0 < y₀) (hy1 : y₀ < 1) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hxh0 : 0 < xhat) (hxh1 : xhat < 1) (hyh0 : 0 < yhat) (hyh1 : yhat < 1)
    (hξx : ξ < x) (hξxh : ξ < xhat) (hyy : y₀ < yhat) (hνμ : ν < μ)
    (henv : ∀ (p μ w β x : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx0 : 0 < x) (hxp : x < p) (hxμ : x < (1 - μ) ^ w)
    (hF : (certFeasible p μ w β x).Nonempty) (hcert : cert p μ w β x < 0),
      ∃ η τ ζ R : ℝ, 0 < η ∧ 0 < τ ∧ 0 < ζ ∧ w < R ∧ 1 < β * R ∧
      ∀ r : ℝ, R ≤ r →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G B : SimpleGraph V) (X Y : Finset V) (c : ℝ),
        X.Nonempty → Y.Nonempty → Disjoint X Y → |c - p| ≤ η →
        (∀ y ∈ Y, c < colDensity G X y) →
        RowColMaximal G X Y c w r (β * r) →
        (∀ i ∈ X, 0 < graphFrac B X i → SharpBlueFailure G B X Y c μ w β (β * r) i) →
        ∀ Xg : Finset V, Xg ⊆ X → (X.card : ℝ) - (Xg.card : ℝ) ≤ ζ * (X.card : ℝ) →
        (∀ i ∈ Xg, graphFrac B X i ≤ μ + τ ∧ SharpRedFailure G B X Y c w β (β * r) x i) →
        False) :
    ∃ L₀ : ℕ, ∀ C : ℝ, 1 ≤ C → ∀ ℓ : ℕ, L₀ ≤ ℓ →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        HostStopping G C xhat yhat ℓ →
        ∀ k t : ℕ, 0 < k → 0 < t → ∀ X Y : Finset V,
          X.Nonempty → Y.Nonempty → Disjoint X Y →
          p ≤ redDensity G X Y →
          C ^ (w + 1) * ξ ^ (-(k : ℝ)) * y₀ ^ (-(ℓ : ℝ)) * ν ^ (-(w * (t : ℝ))) ≤
            (X.card : ℝ) ^ w * (Y.card : ℝ) →
          HasRedClique G (X ∪ Y) k ∨ HasBlueClique G X t ∨ HasBlueClique G Y ℓ := by
  classical
  obtain ⟨η, τ, ζ, R, hη, hτ, hζ, hwR, hβR, hloc⟩ :=
    henv p μ w β x hp0 hp1 hμ0 hμ1 hw hβ0 hβ1 hx0 hxp hxμ hF hcert
  -- the intermediate parameters `λ = lam`, `y = yy`
  obtain ⟨lam, hlamd⟩ : ∃ lam : ℝ, lam = (ξ + min x xhat) / 2 := ⟨_, rfl⟩
  have hmin1 : ξ < min x xhat := lt_min hξx hξxh
  have hlamξ : ξ < lam := by rw [hlamd]; linarith
  have hlamx : lam < x := by have := min_le_left x xhat; rw [hlamd]; linarith
  have hlamxh : lam < xhat := by have := min_le_right x xhat; rw [hlamd]; linarith
  have hlam0 : 0 < lam := by linarith
  obtain ⟨yy, hyyd⟩ : ∃ yy : ℝ, yy = (y₀ + yhat) / 2 := ⟨_, rfl⟩
  have hy0yy : y₀ < yy := by rw [hyyd]; linarith
  have hyyh : yy < yhat := by rw [hyyd]; linarith
  have hyy0 : 0 < yy := by linarith
  -- cap and θ
  obtain ⟨τ', hτ'd⟩ : ∃ τ' : ℝ, τ' = min τ ((1 - μ) / 2) := ⟨_, rfl⟩
  have hτ'0 : 0 < τ' := by rw [hτ'd]; exact lt_min hτ (by linarith)
  have hτ'τ : τ' ≤ τ := by rw [hτ'd]; exact min_le_left _ _
  have hτ'μ : τ' ≤ (1 - μ) / 2 := by rw [hτ'd]; exact min_le_right _ _
  obtain ⟨cap, hcapd⟩ : ∃ cap : ℝ, cap = μ + τ' := ⟨_, rfl⟩
  have hcap0 : 0 ≤ cap := by rw [hcapd]; linarith
  have hcapτ : cap ≤ μ + τ := by rw [hcapd]; linarith
  have hcap1 : cap < 1 := by rw [hcapd]; linarith
  have hμcap : μ < cap := by rw [hcapd]; linarith
  obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = (μ + cap) / 2 := ⟨_, rfl⟩
  have hμθ : μ < θ := by rw [hθd]; linarith
  have hθcap : θ < cap := by rw [hθd]; linarith
  have hθ0 : 0 < θ := by linarith
  -- the moment exponent `r` and page-loss constant `D`
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = min (1 / 4) ((cap - θ) / 2) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεd]; exact lt_min (by norm_num) (by linarith)
  obtain ⟨r, hrR, h2w, hDr⟩ := exists_r_small w β (max R (2 / β)) ε hw hβ0 hβ1 hε
  have hRr : R ≤ r := (le_max_left _ _).trans hrR
  have hr2 : 2 / β ≤ r := (le_max_right _ _).trans hrR
  have hs1 : 1 < β * r := by
    have := mul_le_mul_of_nonneg_left hr2 hβ0.le
    rw [mul_div_cancel₀ _ hβ0.ne'] at this; linarith
  have hwr : w < r := by linarith
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = w / (r - w) + 1 - (1 - β) ^ (1 / (β * r)) := ⟨_, rfl⟩
  have hDε : D < ε := by rw [hDd]; exact hDr
  have hD4 : D ≤ 1 / 4 := by have := min_le_left (1 / 4 : ℝ) ((cap - θ) / 2); rw [← hεd] at this; linarith
  have hDh : D < (cap - θ) / 2 := by
    have := min_le_right (1 / 4 : ℝ) ((cap - θ) / 2); rw [← hεd] at this; linarith
  have hh : 0 < cap - θ - D := by linarith
  -- the shift `δ`
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = min (p / 2) η / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδd]; exact half_pos (lt_min (by linarith) hη)
  have hδη : δ ≤ η := by have := min_le_right (p / 2) η; rw [hδd]; linarith
  have hδp : δ < p := by have := min_le_left (p / 2) η; rw [hδd]; linarith
  -- the growth rate `a`
  have hlx : 0 < Real.log (xhat / lam) := Real.log_pos (by rw [lt_div_iff₀ hlam0]; linarith)
  have hly : 0 < Real.log (yhat / yy) := Real.log_pos (by rw [lt_div_iff₀ hyy0]; linarith)
  have hlμ : 0 < Real.log (1 / μ) := Real.log_pos (by rw [lt_div_iff₀ hμ0]; linarith)
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = min (Real.log (xhat / lam) / w)
      (min (Real.log (yhat / yy) / w) (Real.log (1 / μ))) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [had]; exact lt_min (div_pos hlx hw) (lt_min (div_pos hly hw) hlμ)
  have hax : a * w ≤ Real.log (xhat / lam) := by
    have : a ≤ Real.log (xhat / lam) / w := by rw [had]; exact min_le_left _ _
    rwa [le_div_iff₀ hw] at this
  have hay : a * w ≤ Real.log (yhat / yy) := by
    have : a ≤ Real.log (yhat / yy) / w := by rw [had]; exact (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hw] at this
  have haμ : a ≤ Real.log (1 / μ) := by rw [had]; exact (min_le_right _ _).trans (min_le_right _ _)
  -- book sizes `b_n`, `m_n = M₀ b_n`
  have hρ : 0 < Real.log (θ / μ) := Real.log_pos (by rw [lt_div_iff₀ hμ0]; linarith)
  have hwρ : 0 < w * Real.log (θ / μ) := mul_pos hw hρ
  obtain ⟨B₀, hB₀d⟩ : ∃ B₀ : ℝ, B₀ = |w * Real.log 2 - r * Real.log δ| / (w * Real.log (θ / μ)) :=
    ⟨_, rfl⟩
  obtain ⟨B₁, hB₁d⟩ : ∃ B₁ : ℝ, B₁ = 2 * r / (w * Real.log (θ / μ)) := ⟨_, rfl⟩
  have hB₀ : 0 ≤ B₀ := by rw [hB₀d]; exact div_nonneg (abs_nonneg _) hwρ.le
  have hB₁ : 0 ≤ B₁ := by rw [hB₁d]; exact div_nonneg (by linarith) hwρ.le
  obtain ⟨M₀, hM₀d⟩ : ∃ M₀ : ℕ, M₀ = ⌈2 / (cap - θ - D)⌉₊ + 2 := ⟨_, rfl⟩
  have hM₀2 : 2 ≤ M₀ := by omega
  have hM₀h : 2 / (cap - θ - D) ≤ (M₀ : ℝ) := by
    have := Nat.le_ceil (2 / (cap - θ - D))
    have h' : ((⌈2 / (cap - θ - D)⌉₊ : ℕ) : ℝ) ≤ M₀ := by exact_mod_cast (show _ ≤ M₀ by omega)
    linarith
  obtain ⟨b, hbd⟩ : ∃ b : ℕ → ℕ, b = fun n : ℕ => ⌈B₀ + B₁ * Real.log (n : ℝ)⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨m, hmd⟩ : ∃ m : ℕ → ℕ, m = fun n => M₀ * b n := ⟨_, rfl⟩
  have hbn : ∀ n, 1 ≤ b n ∧ b n ≤ m n ∧ (b n : ℝ) / (m n) ≤ (cap - θ - D) / 2 := by
    intro n
    have hb1 : 1 ≤ b n := by rw [hbd]; exact Nat.le_add_left 1 _
    refine ⟨hb1, ?_, ?_⟩
    · rw [hmd]; exact Nat.le_mul_of_pos_left _ (by omega)
    · have hb0 : (0 : ℝ) < b n := by exact_mod_cast hb1
      have hM0 : (0 : ℝ) < M₀ := by exact_mod_cast (show 0 < M₀ by omega)
      rw [hmd]
      push_cast
      rw [show (b n : ℝ) / ((M₀ : ℝ) * b n) = 1 / M₀ by field_simp, div_le_div_iff₀ hM0 two_pos]
      rw [div_le_iff₀ hh] at hM₀h
      linarith
  have hm2 : ∀ n, 2 ≤ m n := by
    intro n
    rw [hmd]
    calc 2 = 2 * 1 := by norm_num
      _ ≤ M₀ * b n := Nat.mul_le_mul hM₀2 (hbn n).1
  have hbook : ∀ n : ℕ, 1 ≤ n → (μ ^ w) ^ (b n) ≤ (θ ^ w) ^ (b n) * (δ / (n : ℝ) ^ 2) ^ r / 2 ^ w := by
    intro n hn
    have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
    have hbL : B₀ + B₁ * Real.log n ≤ (b n : ℝ) := by
      rw [hbd]; push_cast
      have := Nat.le_ceil (B₀ + B₁ * Real.log n); linarith
    have hkey : w * Real.log 2 - r * Real.log δ + 2 * r * Real.log n ≤
        (b n : ℝ) * (w * Real.log (θ / μ)) := by
      have h1 := mul_le_mul_of_nonneg_right hbL hwρ.le
      have e : (B₀ + B₁ * Real.log n) * (w * Real.log (θ / μ)) =
          |w * Real.log 2 - r * Real.log δ| + 2 * r * Real.log n := by
        rw [hB₀d, hB₁d]; field_simp
      have := le_abs_self (w * Real.log 2 - r * Real.log δ)
      linarith
    rw [← Real.log_le_log_iff (by positivity) (by positivity)]
    rw [Real.log_pow, Real.log_rpow hμ0, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_rpow hθ0,
      Real.log_rpow (by positivity), Real.log_div hδ0.ne' (by positivity), Real.log_pow,
      Real.log_rpow two_pos]
    rw [Real.log_div hθ0.ne' hμ0.ne'] at hkey
    push_cast
    linarith
  -- size requirements
  have hmb : ∀ n : ℕ, 1 ≤ n → (m n : ℝ) ≤ M₀ * (B₀ + 2) + M₀ * B₁ * Real.log n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hc := Nat.ceil_lt_add_one (show 0 ≤ B₀ + B₁ * Real.log n by positivity)
    rw [hmd, hbd]; push_cast
    have hM0 : (0 : ℝ) ≤ M₀ := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left
      (show (⌈B₀ + B₁ * Real.log n⌉₊ : ℝ) + 1 ≤ B₀ + B₁ * Real.log n + 2 by linarith) hM0
    linarith
  obtain ⟨K, hK0, hKb⟩ := Q_bound a (M₀ * (B₀ + 2)) (M₀ * B₁) ha0 (by positivity) (by positivity) m hmb
  -- seed constant
  have hνw : 0 < ν ^ w := Real.rpow_pos_of_pos hν0 w
  have hμw : 0 < μ ^ w := Real.rpow_pos_of_pos hμ0 w
  have hνμw : ν ^ w < μ ^ w := Real.rpow_lt_rpow hν0.le hνμ hw
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = min (lam / ξ) (μ ^ w / ν ^ w) := ⟨_, rfl⟩
  have hA : 1 < A := by
    rw [hAd]
    exact lt_min (by rw [lt_div_iff₀ hξ0]; linarith) (by rw [lt_div_iff₀ hνw]; linarith)
  obtain ⟨K', hK'0, hK'b⟩ := pow_r_bound r A hA
  obtain ⟨Kc, hKcd⟩ : ∃ Kc : ℝ, Kc = 4 + 2 / (cap - θ - D) + 1 / ζ + (1 + 1 / δ) / (1 - cap) :=
    ⟨_, rfl⟩
  have hk1 : 0 ≤ 2 / (cap - θ - D) := by positivity
  have hk2 : 0 ≤ 1 / ζ := by positivity
  have hk3 : 0 ≤ (1 + 1 / δ) / (1 - cap) := div_nonneg (by positivity) (by linarith)
  have hKc0 : 0 < Kc := by rw [hKcd]; linarith
  obtain ⟨L1, hL1⟩ := pow_unbounded_of_one_lt (Kc * K) (Real.one_lt_exp_iff.mpr ha0)
  have hyy1 : 1 < yy / y₀ := by rw [lt_div_iff₀ hy0]; linarith
  obtain ⟨L2, hL2⟩ := pow_unbounded_of_one_lt (K' / δ ^ r) hyy1
  refine ⟨max L1 L2, ?_⟩
  intro C hC ℓ hℓ V _ _ G hstop k t hk ht X Y hX hY hXY hd hsz
  have hsize : ∀ n : ℕ, 1 ≤ n → ∀ N : ℝ, Real.exp (a * ((n : ℝ) + ℓ)) < N →
      4 * (m n : ℝ) ≤ N ∧ 2 * (m n : ℝ) / (cap - θ - D) ≤ N ∧
        (((n + m n : ℕ)) : ℝ) ^ (m n) ≤ ζ * N ∧ 1 + (n : ℝ) ^ 2 / δ ≤ N * (1 - cap) := by
    intro n hn N hN
    have hQ := hKb n hn
    have hexp : Real.exp (a * ((n : ℝ) + ℓ)) = Real.exp a ^ n * Real.exp a ^ ℓ := by
      rw [mul_add, Real.exp_add, mul_comm a, mul_comm a, Real.exp_nat_mul, Real.exp_nat_mul]
    have hℓ1 : Kc * K < Real.exp a ^ ℓ :=
      hL1.trans_le (pow_le_pow_right₀ (Real.one_lt_exp_iff.mpr ha0).le ((le_max_left _ _).trans hℓ))
    obtain ⟨Q, hQd⟩ : ∃ Q : ℝ, Q = (((n + m n : ℕ)) : ℝ) ^ (m n) := ⟨_, rfl⟩
    rw [← hQd] at hQ ⊢
    have hNQ : Kc * Q ≤ N := by
      calc Kc * Q ≤ Kc * (K * Real.exp a ^ n) := mul_le_mul_of_nonneg_left hQ hKc0.le
        _ = (Kc * K) * Real.exp a ^ n := by ring
        _ ≤ Real.exp a ^ ℓ * Real.exp a ^ n := mul_le_mul_of_nonneg_right hℓ1.le (by positivity)
        _ = Real.exp (a * ((n : ℝ) + ℓ)) := by rw [hexp]; ring
        _ ≤ N := hN.le
    have hm1 : 1 ≤ m n := le_trans (by norm_num) (hm2 n)
    have hmQ : (m n : ℝ) ≤ Q := by
      rw [hQd]
      have : m n ≤ (n + m n) ^ (m n) :=
        (Nat.le_add_left _ _).trans (Nat.le_self_pow (by omega) _)
      exact_mod_cast this
    have hn2Q : (n : ℝ) ^ 2 ≤ Q := by
      rw [hQd]
      have : n ^ 2 ≤ (n + m n) ^ (m n) :=
        (Nat.pow_le_pow_left (Nat.le_add_right _ _) 2).trans
          (Nat.pow_le_pow_right (by omega) (hm2 n))
      exact_mod_cast this
    have hQ0 : 0 ≤ Q := le_trans (Nat.cast_nonneg _) hmQ
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hKc4 : 4 * Q ≤ Kc * Q := by
      apply mul_le_mul_of_nonneg_right _ hQ0; rw [hKcd]; linarith
    have hKc1 : 2 / (cap - θ - D) * Q ≤ Kc * Q := by
      apply mul_le_mul_of_nonneg_right _ hQ0; rw [hKcd]; linarith
    have hKc2 : 1 / ζ * Q ≤ Kc * Q := by
      apply mul_le_mul_of_nonneg_right _ hQ0; rw [hKcd]; linarith
    have hKc3 : (1 + 1 / δ) / (1 - cap) * Q ≤ Kc * Q := by
      apply mul_le_mul_of_nonneg_right _ hQ0; rw [hKcd]; linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith
    · have e : 2 * (m n : ℝ) / (cap - θ - D) = 2 / (cap - θ - D) * m n := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hmQ hk1
      linarith
    · have e : Q = ζ * (1 / ζ * Q) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (hKc2.trans hNQ) hζ.le
    · have h1c : 0 < 1 - cap := by linarith
      have e : (1 - cap) * ((1 + 1 / δ) / (1 - cap) * Q) = (1 + 1 / δ) * Q := by
        have e0 : (1 - cap) * ((1 + 1 / δ) / (1 - cap) * Q) = ((1 - cap) / (1 - cap)) * ((1 + 1 / δ) * Q) := by
          ring
        rw [e0, div_self h1c.ne', one_mul]
      have h5 : 1 + (n : ℝ) ^ 2 / δ ≤ (1 + 1 / δ) * Q := by
        have : 1 + (n : ℝ) ^ 2 / δ ≤ (1 + 1 / δ) * (n : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
          have e2 : (1 + 1 / δ) * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 + (n : ℝ) ^ 2 / δ := by ring
          linarith
        exact this.trans (mul_le_mul_of_nonneg_left hn2Q (by positivity))
      have h6 := mul_le_mul_of_nonneg_left (hKc3.trans hNQ) h1c.le
      rw [e] at h6
      linarith
  -- seed: `Thr ≤ Φ_n(X, Y)` at `n = k + t`
  have hn1 : 1 ≤ k + t := by omega
  have hseed : Thr C w lam yy μ ℓ k t ≤ potential G X Y (p - δ / ((k + t : ℕ) : ℝ)) w r (β * r) := by
    have hn : (1 : ℝ) ≤ ((k + t : ℕ) : ℝ) := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < ((k + t : ℕ) : ℝ) := by linarith
    have hr0 : 0 < r := by linarith
    have hN0 : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    have hM0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
    have hH := avg_sub_le_momentNorm G X Y (p - δ / ((k + t : ℕ) : ℝ)) (β * r) hY hs1.le
    rw [← redDensity_eq_avg G X Y hX] at hH
    have hH' : δ / ((k + t : ℕ) : ℝ) ≤ momentNorm G X Y (p - δ / ((k + t : ℕ) : ℝ)) (β * r) := by
      linarith
    have hHr := Real.rpow_le_rpow (by positivity) hH' hr0.le
    have hC0 : 0 < C := by linarith
    have hsz' : C ^ (w + 1) / (ξ ^ k * y₀ ^ ℓ * (ν ^ w) ^ t) ≤ (X.card : ℝ) ^ w * (Y.card : ℝ) := by
      have e : C ^ (w + 1) / (ξ ^ k * y₀ ^ ℓ * (ν ^ w) ^ t) =
          C ^ (w + 1) * ξ ^ (-(k : ℝ)) * y₀ ^ (-(ℓ : ℝ)) * ν ^ (-(w * (t : ℝ))) := by
        rw [Real.rpow_neg hξ0.le, Real.rpow_neg hy0.le, Real.rpow_neg hν0.le, Real.rpow_mul hν0.le]
        simp only [Real.rpow_natCast]
        rw [div_eq_mul_inv, mul_inv, mul_inv]; ring
      rw [e]; exact hsz
    have hA1 : A * ξ ≤ lam := by
      have : A ≤ lam / ξ := by rw [hAd]; exact min_le_left _ _
      rwa [le_div_iff₀ hξ0] at this
    have hA2 : A * ν ^ w ≤ μ ^ w := by
      have : A ≤ μ ^ w / ν ^ w := by rw [hAd]; exact min_le_right _ _
      rwa [le_div_iff₀ hνw] at this
    have hA0 : 0 < A := by linarith
    have h1 : A ^ k * ξ ^ k ≤ lam ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hA1 k
    have h2 : A ^ t * (ν ^ w) ^ t ≤ (μ ^ w) ^ t := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hA2 t
    have hℓ2 : K' / δ ^ r < (yy / y₀) ^ ℓ :=
      hL2.trans_le (pow_le_pow_right₀ hyy1.le ((le_max_right _ _).trans hℓ))
    have h3 : K' * y₀ ^ ℓ < yy ^ ℓ * δ ^ r := by
      rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity)] at hℓ2
      exact hℓ2
    have h4 := hK'b (k + t) hn1
    have hP1 : 0 < ξ ^ k * y₀ ^ ℓ * (ν ^ w) ^ t := by positivity
    have key : ξ ^ k * y₀ ^ ℓ * (ν ^ w) ^ t * ((k + t : ℕ) : ℝ) ^ r ≤
        lam ^ k * yy ^ ℓ * (μ ^ w) ^ t * δ ^ r := by
      calc ξ ^ k * y₀ ^ ℓ * (ν ^ w) ^ t * ((k + t : ℕ) : ℝ) ^ r
          ≤ ξ ^ k * y₀ ^ ℓ * (ν ^ w) ^ t * (K' * A ^ (k + t)) := mul_le_mul_of_nonneg_left h4 hP1.le
        _ = (A ^ k * ξ ^ k) * (A ^ t * (ν ^ w) ^ t) * (K' * y₀ ^ ℓ) := by rw [pow_add]; ring
        _ ≤ lam ^ k * (μ ^ w) ^ t * (yy ^ ℓ * δ ^ r) :=
          mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3.le (by positivity)
            (by positivity)
        _ = lam ^ k * yy ^ ℓ * (μ ^ w) ^ t * δ ^ r := by ring
    unfold Thr potential
    calc C ^ (w + 1) / (lam ^ k * yy ^ ℓ * (μ ^ w) ^ t)
        = C ^ (w + 1) * δ ^ r / (lam ^ k * yy ^ ℓ * (μ ^ w) ^ t * δ ^ r) := by
          field_simp
      _ ≤ C ^ (w + 1) * δ ^ r / (ξ ^ k * y₀ ^ ℓ * (ν ^ w) ^ t * ((k + t : ℕ) : ℝ) ^ r) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) key
      _ = C ^ (w + 1) / (ξ ^ k * y₀ ^ ℓ * (ν ^ w) ^ t) * (δ ^ r / ((k + t : ℕ) : ℝ) ^ r) := by
          rw [mul_div_mul_comm]
      _ ≤ (X.card : ℝ) ^ w * (Y.card : ℝ) * (δ ^ r / ((k + t : ℕ) : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_right hsz' (by positivity)
      _ = (X.card : ℝ) ^ w * (Y.card : ℝ) * (δ / ((k + t : ℕ) : ℝ)) ^ r := by
          rw [Real.div_rpow hδ0.le hn0.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left hHr (by positivity)
  exact closure_induction G p μ w β x η τ ζ R C lam yy xhat yhat cap θ D δ r a ℓ b m hloc hstop hw hβ0 hβ1
    hx0 hμ0 hlam0 hlamx hyy0 hC (by linarith) (by linarith) hRr hwr hs1 hcap0 hcapτ hcap1 hθ0 hθcap hδ0
    hδη hδp (le_of_eq hDd.symm) hD4 hh hax hay haμ hbn hbook hsize (k + t) k t rfl hk ht X Y hX hY hXY
    hseed

end DiagRamsey
