import RamseyRefinement.ProfileExpr
import RamseyLean.Frontier
import Bridge.Foundations

/-! B4: tangent-line bounds for the project's source at `t₀ = 763/2000` and at the 1.2625 point
`t₀ = 32801066153/85899345920`.  `A = F'(t₀)` and `B = F(t₀) - t₀ F'(t₀)` are enclosed by Lu--Wang's
verified fixed-point interval arithmetic (`RamseyRefinement.IntervalExpr.Expr.bound_sound`), checked by
the kernel. -/

set_option maxRecDepth 100000

namespace LuWangBridge

open Set DiagRamsey RamseyRefinement RamseyRefinement.IntervalExpr RamseyRefinement.FixedPointInterval
  RamseyRefinement.ShapeCertificate RamseyCurrent
open RamseyCurrent.CurrentSourceGeometry (rationalData)

theorem hasDerivAt_source {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt luWangSource (CurrentSourceGeometry.D t) t := by
  have hF : HasDerivAt CurrentSourceGeometry.F (CurrentSourceGeometry.D t) t :=
    (CurrentSourceGeometry.derivative ⟨h0, h1.le⟩).hasDerivAt (Ioc_mem_nhds h0 h1)
  exact hF.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Icc_mem_nhds h0 h1) source_eqOn)

theorem deriv_source {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    deriv luWangSource t = CurrentSourceGeometry.D t :=
  (hasDerivAt_source h0 h1).deriv

/-- The symmetric profile lies below the tangent plane at any interior `t₀`
(concavity, plus `B ≤ A`, i.e. Lu--Wang's `tangent_intercept_order`, for the orientation `b < a`). -/
theorem symmetricProfile_le_tangent {t0 : ℝ} (h0 : 0 < t0) (h1 : t0 < 1) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    DiagRamsey.symmetricProfile luWangSource a b ≤
      deriv luWangSource t0 * a + (luWangSource t0 - t0 * deriv luWangSource t0) * b := by
  have hAB : luWangSource t0 - t0 * deriv luWangSource t0 ≤ deriv luWangSource t0 := by
    rw [deriv_source h0 h1, source_eq ⟨h0.le, h1.le⟩]
    exact CurrentSourceGeometry.tangent_intercept_order ⟨h0, h1.le⟩
  have hconc : ConcaveOn ℝ (Ioc (0 : ℝ) 1) luWangSource :=
    lu_wang_source_concave.subset Ioc_subset_Icc_self (convex_Ioc 0 1)
  have hA : HasDerivAt luWangSource (deriv luWangSource t0) t0 := by
    rw [deriv_source h0 h1]; exact hasDerivAt_source h0 h1
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : 0 < max (a : ℝ) b := lt_max_of_lt_left ha'
  have hs : min (a : ℝ) b / max (a : ℝ) b ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (lt_min ha' hb') hM, (div_le_one hM).2 min_le_max⟩
  have key := RamseyLean.concaveOn_le_tangentLine (D := fun _ => deriv luWangSource t0)
    hconc hs ⟨h0, h1.le⟩ hA
  simp only [DiagRamsey.symmetricProfile]
  have hcancel : max (a : ℝ) b * (min (a : ℝ) b / max (a : ℝ) b) = min (a : ℝ) b :=
    mul_div_cancel₀ _ hM.ne'
  calc max (a : ℝ) b * luWangSource (min (a : ℝ) b / max (a : ℝ) b)
      ≤ max (a : ℝ) b * (luWangSource t0 +
          (min (a : ℝ) b / max (a : ℝ) b - t0) * deriv luWangSource t0) :=
        mul_le_mul_of_nonneg_left key hM.le
    _ = max (a : ℝ) b * (luWangSource t0 - t0 * deriv luWangSource t0) +
          max (a : ℝ) b * (min (a : ℝ) b / max (a : ℝ) b) * deriv luWangSource t0 := by ring
    _ = max (a : ℝ) b * (luWangSource t0 - t0 * deriv luWangSource t0) +
          min (a : ℝ) b * deriv luWangSource t0 := by rw [hcancel]
    _ ≤ deriv luWangSource t0 * a + (luWangSource t0 - t0 * deriv luWangSource t0) * b := by
        rcases le_total (a : ℝ) b with h | h
        · rw [min_eq_left h, max_eq_right h]; linarith
        · rw [min_eq_right h, max_eq_left h]; nlinarith

/-- Tangent bound at any interior point, from `lu_wang_uniform_source_bound` with `ε = δ`. -/
theorem tangent_source_bound {t0 : ℝ} (h0 : 0 < t0) (h1 : t0 < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℕ, 0 < a → 0 < b → ∀ N : ℕ,
      C * Real.exp ((deriv luWangSource t0 + δ) * (a : ℝ) +
          (luWangSource t0 - t0 * deriv luWangSource t0 + δ) * (b : ℝ)) ≤ (N : ℝ) →
      RamseyArrows a b N := by
  obtain ⟨C, hC, h⟩ := lu_wang_uniform_source_bound δ hδ
  refine ⟨C, hC, fun a b ha hb N hN => h a b ha hb N (le_trans ?_ hN)⟩
  have := symmetricProfile_le_tangent h0 h1 ha hb
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith)
  linarith

/-! ### Interval enclosures -/

theorem contains_point_zero : (point 0).Contains 0 := by
  simpa [value] using Interval.contains_point 0

theorem enclose {e : Expr} {v : ℝ} (hv : e.eval 0 = v) (hsafe : e.safe (point 0) = true) :
    ((e.bound (point 0)).lo : ℝ) / (scale : ℝ) ≤ v ∧ v ≤ ((e.bound (point 0)).hi : ℝ) / (scale : ℝ) := by
  have := e.bound_sound contains_point_zero hsafe
  rw [hv] at this
  exact this

/-- `A` and `B` of the profile of piece `i` at the rational point `p/q`. -/
def exprA (i : Fin 2279) (p : ℤ) (q : ℕ) : Expr :=
  ProfileExpr.fp (rationalData.coefficients i) (p / q) 24 48 (.rat p q)

def exprB (i : Fin 2279) (p : ℤ) (q : ℕ) : Expr :=
  ProfileExpr.sub (ProfileExpr.f (rationalData.coefficients i) (p / q) 24 48 (.rat p q))
    (.mul (.rat p q) (ProfileExpr.fp (rationalData.coefficients i) (p / q) 24 48 (.rat p q)))

theorem source_at {i : Fin 2279} {t : ℝ}
    (ht : t ∈ Icc (rationalData.knot i.castSucc : ℝ) (rationalData.knot i.succ : ℝ)) (h0 : 0 < t)
    (h1 : t < 1) :
    deriv luWangSource t = profileSlope (hornerPoly (rationalData.coefficients i)) t ∧
      luWangSource t - t * deriv luWangSource t =
        profile (hornerPoly (rationalData.coefficients i)) t -
          t * profileSlope (hornerPoly (rationalData.coefficients i)) t := by
  rw [deriv_source h0 h1, source_eq ⟨h0.le, h1.le⟩, CurrentSourceGeometry.D_piece ht h0,
    CurrentSourceGeometry.F_piece ht]
  exact ⟨rfl, rfl⟩

theorem enclose_AB (i : Fin 2279) (p : ℤ) (q : ℕ) {t : ℝ} (htq : t = (p : ℝ) / (q : ℝ))
    (ht : t ∈ Icc (rationalData.knot i.castSucc : ℝ) (rationalData.knot i.succ : ℝ)) (h0 : 0 < t)
    (h1 : t < 1) (hA : (exprA i p q).safe (point 0) = true)
    (hB : (exprB i p q).safe (point 0) = true) :
    (((exprA i p q).bound (point 0)).lo : ℝ) / (scale : ℝ) ≤ deriv luWangSource t ∧
    deriv luWangSource t ≤ (((exprA i p q).bound (point 0)).hi : ℝ) / (scale : ℝ) ∧
    (((exprB i p q).bound (point 0)).lo : ℝ) / (scale : ℝ) ≤ luWangSource t - t * deriv luWangSource t ∧
    luWangSource t - t * deriv luWangSource t ≤ (((exprB i p q).bound (point 0)).hi : ℝ) / (scale : ℝ) := by
  obtain ⟨hdA, hdB⟩ := source_at ht h0 h1
  have eA : (exprA i p q).eval 0 = deriv luWangSource t := by
    rw [hdA, htq]; simp [exprA, Expr.eval]
  have eB : (exprB i p q).eval 0 = luWangSource t - t * deriv luWangSource t := by
    rw [hdB, htq]; simp [exprB, Expr.eval]
  obtain ⟨a1, a2⟩ := enclose eA hA
  obtain ⟨b1, b2⟩ := enclose eB hB
  exact ⟨a1, a2, b1, b2⟩

/-! ### Concrete tangent points -/

theorem scale_pos : (0 : ℝ) < (scale : ℝ) := by
  have : (0 : ℤ) < scale := by decide +kernel
  exact_mod_cast this

theorem le_of_scaled {z p : ℤ} {q : ℕ} (hq : 0 < q) (h : z * q ≤ p * scale) :
    (z : ℝ) / (scale : ℝ) ≤ (p : ℝ) / (q : ℝ) := by
  rw [div_le_div_iff₀ scale_pos (by exact_mod_cast hq)]
  exact_mod_cast h

theorem ge_of_scaled {z p : ℤ} {q : ℕ} (hq : 0 < q) (h : p * scale ≤ z * q) :
    (p : ℝ) / (q : ℝ) ≤ (z : ℝ) / (scale : ℝ) := by
  rw [div_le_div_iff₀ (by exact_mod_cast hq) scale_pos]
  exact_mod_cast h

theorem mem_knots {i : Fin 2279} {p : ℤ} {q : ℕ} (hq : 0 < q)
    (h1 : rationalData.knot i.castSucc ≤ (p : ℚ) / q) (h2 : (p : ℚ) / q ≤ rationalData.knot i.succ) :
    (p : ℝ) / (q : ℝ) ∈ Icc (rationalData.knot i.castSucc : ℝ) (rationalData.knot i.succ : ℝ) := by
  have e : ((((p : ℚ) / q : ℚ)) : ℝ) = (p : ℝ) / (q : ℝ) := by push_cast; rfl
  constructor
  · rw [← e]; exact_mod_cast h1
  · rw [← e]; exact_mod_cast h2

/-- `t₀ = 763/2000` lies in piece 930: `A ≤ 1.21355`, `B ≤ 0.28084` (with `0 < B < A`). -/
theorem tangent_763_bounds :
    0 < luWangSource (763 / 2000) - 763 / 2000 * deriv luWangSource (763 / 2000) ∧
    luWangSource (763 / 2000) - 763 / 2000 * deriv luWangSource (763 / 2000) <
      deriv luWangSource (763 / 2000) ∧
    deriv luWangSource (763 / 2000) ≤ 121355 / 100000 ∧
    luWangSource (763 / 2000) - 763 / 2000 * deriv luWangSource (763 / 2000) ≤ 28084 / 100000 := by
  have ht : (763 / 2000 : ℝ) = ((763 : ℤ) : ℝ) / ((2000 : ℕ) : ℝ) := by norm_num
  obtain ⟨a1, a2, b1, b2⟩ := enclose_AB 930 763 2000 ht
    (by rw [ht]; exact mem_knots (by norm_num) (by decide +kernel) (by decide +kernel))
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hA := le_of_scaled (p := 121355) (q := 100000) (by norm_num)
    (show ((exprA 930 763 2000).bound (point 0)).hi * ((100000 : ℕ) : ℤ) ≤ 121355 * scale by
      decide +kernel)
  have hB := le_of_scaled (p := 28084) (q := 100000) (by norm_num)
    (show ((exprB 930 763 2000).bound (point 0)).hi * ((100000 : ℕ) : ℤ) ≤ 28084 * scale by
      decide +kernel)
  have hB0 := ge_of_scaled (p := 28) (q := 100) (by norm_num)
    (show 28 * scale ≤ ((exprB 930 763 2000).bound (point 0)).lo * ((100 : ℕ) : ℤ) by
      decide +kernel)
  have hA0 := ge_of_scaled (p := 121) (q := 100) (by norm_num)
    (show 121 * scale ≤ ((exprA 930 763 2000).bound (point 0)).lo * ((100 : ℕ) : ℤ) by
      decide +kernel)
  push_cast at hA hB hB0 hA0
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `t₀ = 32801066153/85899345920` (the 1.2625 point) lies in piece 931. -/
theorem tangent_12625_bounds :
    12130035 / 10000000 ≤ deriv luWangSource (32801066153 / 85899345920) ∧
    deriv luWangSource (32801066153 / 85899345920) ≤ 12130036 / 10000000 ∧
    2810451 / 10000000 ≤ luWangSource (32801066153 / 85899345920) -
      32801066153 / 85899345920 * deriv luWangSource (32801066153 / 85899345920) ∧
    luWangSource (32801066153 / 85899345920) -
      32801066153 / 85899345920 * deriv luWangSource (32801066153 / 85899345920) ≤
        2810452 / 10000000 := by
  have ht : (32801066153 / 85899345920 : ℝ) =
      ((32801066153 : ℤ) : ℝ) / ((85899345920 : ℕ) : ℝ) := by norm_num
  obtain ⟨a1, a2, b1, b2⟩ := enclose_AB 931 32801066153 85899345920 ht
    (by rw [ht]; exact mem_knots (by norm_num) (by decide +kernel) (by decide +kernel))
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
  have hA1 := ge_of_scaled (p := 12130035) (q := 10000000) (by norm_num)
    (show 12130035 * scale ≤
      ((exprA 931 32801066153 85899345920).bound (point 0)).lo * ((10000000 : ℕ) : ℤ) by
      decide +kernel)
  have hA2 := le_of_scaled (p := 12130036) (q := 10000000) (by norm_num)
    (show ((exprA 931 32801066153 85899345920).bound (point 0)).hi * ((10000000 : ℕ) : ℤ) ≤
      12130036 * scale by decide +kernel)
  have hB1 := ge_of_scaled (p := 2810451) (q := 10000000) (by norm_num)
    (show 2810451 * scale ≤
      ((exprB 931 32801066153 85899345920).bound (point 0)).lo * ((10000000 : ℕ) : ℤ) by
      decide +kernel)
  have hB2 := le_of_scaled (p := 2810452) (q := 10000000) (by norm_num)
    (show ((exprB 931 32801066153 85899345920).bound (point 0)).hi * ((10000000 : ℕ) : ℤ) ≤
      2810452 * scale by decide +kernel)
  push_cast at hA1 hA2 hB1 hB2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The tangent source bound at the 1.2625 point `t₀ = 32801066153/85899345920`, slack `10⁻⁶`. -/
theorem tangent_source_bound_12625 :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℕ, 0 < a → 0 < b → ∀ N : ℕ,
      C * Real.exp ((deriv luWangSource (32801066153 / 85899345920) + 1 / 1000000) * (a : ℝ) +
          (luWangSource (32801066153 / 85899345920) -
            32801066153 / 85899345920 * deriv luWangSource (32801066153 / 85899345920) +
            1 / 1000000) * (b : ℝ))
        ≤ (N : ℝ) →
      RamseyArrows a b N :=
  tangent_source_bound (by norm_num) (by norm_num) (by norm_num)

theorem gt_of_scaled {z p : ℤ} {q : ℕ} (hq : 0 < q) (h : p * scale < z * q) :
    (p : ℝ) / (q : ℝ) < (z : ℝ) / (scale : ℝ) := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hq) scale_pos]
  exact_mod_cast h

def exprE : Expr := .mul (.exp 24 (.rat (-60678) 100000)) (.exp 24 (.rat (-60678) 100000))
def exprL1 : Expr := .log 48 (.rat 29699 100000)
def exprL2 : Expr := .log 48 (.rat 44999 100000)

theorem exp_lower : (297 / 1000 : ℝ) < Real.exp (-(121356 / 100000)) := by
  have hv : exprE.eval 0 = Real.exp (-(121356 / 100000)) := by
    simp only [exprE, Expr.eval]; rw [← Real.exp_add]; norm_num
  obtain ⟨h1, -⟩ := enclose hv (by decide +kernel)
  have := gt_of_scaled (p := 297) (q := 1000) (by norm_num)
    (show 297 * scale < (exprE.bound (point 0)).lo * ((1000 : ℕ) : ℤ) by decide +kernel)
  push_cast at this
  linarith

theorem log_29699 : -(12140569 / 10000000 : ℝ) ≤ Real.log (29699 / 100000) := by
  have hv : exprL1.eval 0 = Real.log (29699 / 100000) := by
    simp only [exprL1, Expr.eval]; norm_num
  obtain ⟨h1, -⟩ := enclose hv (by decide +kernel)
  have := ge_of_scaled (p := -12140569) (q := 10000000) (by norm_num)
    (show -12140569 * scale ≤ (exprL1.bound (point 0)).lo * ((10000000 : ℕ) : ℤ) by decide +kernel)
  push_cast at this
  linarith

theorem log_44999 : -(7985300 / 10000000 : ℝ) ≤ Real.log (44999 / 100000) := by
  have hv : exprL2.eval 0 = Real.log (44999 / 100000) := by
    simp only [exprL2, Expr.eval]; norm_num
  obtain ⟨h1, -⟩ := enclose hv (by decide +kernel)
  have := ge_of_scaled (p := -7985300) (q := 10000000) (by norm_num)
    (show -7985300 * scale ≤ (exprL2.bound (point 0)).lo * ((10000000 : ℕ) : ℤ) by decide +kernel)
  push_cast at this
  linarith

end LuWangBridge

namespace DiagRamsey

open LuWangBridge

theorem lu_wang_tangent_source_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℕ, 0 < a → 0 < b → ∀ N : ℕ,
      C * Real.exp ((deriv luWangSource (763 / 2000) + 1 / 1000000) * (a : ℝ) +
          (luWangSource (763 / 2000) - 763 / 2000 * deriv luWangSource (763 / 2000) + 1 / 1000000) * (b : ℝ))
        ≤ (N : ℝ) →
      RamseyArrows a b N :=
  tangent_source_bound (by norm_num) (by norm_num) (by norm_num)

/-- Hypothesis `hSource` of `DiagRamsey.diagonal_exp_1263_conditional`. -/
theorem lu_wang_source_hSource_1263 :
    ∃ A B C : ℝ, A ≤ 121355 / 100000 ∧ B ≤ 28084 / 100000 ∧ 1 ≤ C ∧
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ∀ N : ℕ,
        C * Real.exp ((A + 1 / 1000000) * a + (B + 1 / 1000000) * b) ≤ (N : ℝ) →
        RamseyArrows a b N := by
  obtain ⟨-, -, hA, hB⟩ := tangent_763_bounds
  obtain ⟨C, hC, h⟩ := lu_wang_tangent_source_bound
  exact ⟨_, _, C, hA, hB, hC, fun a b ha hb N hN => h a b (by omega) (by omega) N hN⟩

theorem exp_1263_z_bound :
    0 < luWangSource (763 / 2000) - 763 / 2000 * deriv luWangSource (763 / 2000) ∧
      luWangSource (763 / 2000) - 763 / 2000 * deriv luWangSource (763 / 2000) <
        deriv luWangSource (763 / 2000) ∧
      deriv luWangSource (763 / 2000) ≤ 121355 / 100000 ∧
      luWangSource (763 / 2000) - 763 / 2000 * deriv luWangSource (763 / 2000) ≤ 28084 / 100000 ∧
      (297 / 1000 : ℝ) < Real.exp (-deriv luWangSource (763 / 2000) - 1 / 100000) ∧
      (-Real.log (29699 / 100000) + (luWangSource (763 / 2000) - 763 / 2000 * deriv luWangSource (763 / 2000)) +
          1 / 100000 - 1 / 2 * Real.log (44999 / 100000)) / (1 + 1 / 2) < 1263 / 1000 := by
  obtain ⟨h1, h2, h3, h4⟩ := tangent_763_bounds
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · have := exp_lower
    have hmono : Real.exp (-(121356 / 100000)) ≤
        Real.exp (-deriv luWangSource (763 / 2000) - 1 / 100000) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  · have := log_29699
    have := log_44999
    rw [div_lt_iff₀ (by norm_num)]
    linarith

end DiagRamsey
