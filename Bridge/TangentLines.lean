import Bridge.Tangent

/-! # Tangent lines of the symmetric Lu–Wang source (P0.6 item 2, turibius-of-mogrovejo)

For `u ∈ (0,1)` write `A = F'(u)` and `B = F(u) - u F'(u)` (so `B ≤ A`, Lu–Wang's `tangent_intercept_order`). Both
lines `A + B s` and `B + A s` lie above `F̂(s) = symmetricProfile luWangSource 1 s` for every `s > 0`. On `(0,1]` this
is the tangent of the concave `F`. On `[1,∞)`, `F̂(s) = s F(1/s) ≤ A + B s`, and `B ≤ A` orders the two lines.
`line_at` turns kernel interval enclosures of `A, B` at a rational point of a known piece into rational lines
`(c, d)` with `F̂(s) ≤ c + d s`, in both orientations. These are the `LineOK` hypotheses of
`lean/Lemmas/DiagRamsey_V5Assemble.lean`. -/

set_option maxRecDepth 100000

namespace LuWangBridge

open Set DiagRamsey RamseyRefinement RamseyRefinement.IntervalExpr RamseyRefinement.FixedPointInterval
  RamseyRefinement.ShapeCertificate RamseyCurrent
open RamseyCurrent.CurrentSourceGeometry (rationalData)

theorem symm_le_lines {u : ℝ} (h0 : 0 < u) (h1 : u < 1) {s : ℝ} (hs : 0 < s) :
    DiagRamsey.symmetricProfile luWangSource 1 s ≤
        deriv luWangSource u + (luWangSource u - u * deriv luWangSource u) * s ∧
      DiagRamsey.symmetricProfile luWangSource 1 s ≤
        (luWangSource u - u * deriv luWangSource u) + deriv luWangSource u * s := by
  have hAB : luWangSource u - u * deriv luWangSource u ≤ deriv luWangSource u := by
    rw [deriv_source h0 h1, source_eq ⟨h0.le, h1.le⟩]
    exact CurrentSourceGeometry.tangent_intercept_order ⟨h0, h1.le⟩
  have hconc : ConcaveOn ℝ (Ioc (0 : ℝ) 1) luWangSource :=
    lu_wang_source_concave.subset Ioc_subset_Icc_self (convex_Ioc 0 1)
  have hA : HasDerivAt luWangSource (deriv luWangSource u) u := by
    rw [deriv_source h0 h1]; exact hasDerivAt_source h0 h1
  have tan : ∀ x ∈ Ioc (0 : ℝ) 1, luWangSource x ≤ luWangSource u + (x - u) * deriv luWangSource u :=
    fun x hx => RamseyLean.concaveOn_le_tangentLine (D := fun _ => deriv luWangSource u) hconc hx ⟨h0, h1.le⟩ hA
  set A := deriv luWangSource u
  set B := luWangSource u - u * A
  simp only [DiagRamsey.symmetricProfile]
  rcases le_total s 1 with h | h
  · rw [max_eq_left h, min_eq_right h, div_one, one_mul]
    have := tan s ⟨hs, h⟩
    constructor <;> nlinarith
  · rw [max_eq_right h, min_eq_left h]
    have hx : 1 / s ∈ Ioc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hs).2 h⟩
    have := mul_le_mul_of_nonneg_left (tan (1 / s) hx) hs.le
    have e : s * (luWangSource u + (1 / s - u) * A) = A + B * s := by
      simp only [B]; field_simp; ring
    rw [e] at this
    constructor <;> nlinarith

/-- Rational lines from kernel enclosures at `t = p/q` in piece `i`: with `A ≤ pa/qa` and `B ≤ pb/qb`,
`F̂(s) ≤ pa/qa + (pb/qb) s` and `F̂(s) ≤ pb/qb + (pa/qa) s` for all `s > 0`. -/
theorem line_at (i : Fin 2279) (p : ℤ) (q : ℕ) (hq : 0 < q) (h0 : 0 < (p : ℝ) / (q : ℝ)) (h1 : (p : ℝ) / (q : ℝ) < 1)
    (hk1 : rationalData.knot i.castSucc ≤ (p : ℚ) / q) (hk2 : (p : ℚ) / q ≤ rationalData.knot i.succ)
    (hsA : (exprA i p q).safe (point 0) = true) (hsB : (exprB i p q).safe (point 0) = true)
    (pa : ℤ) (qa : ℕ) (hqa : 0 < qa) (ha : ((exprA i p q).bound (point 0)).hi * qa ≤ pa * scale)
    (pb : ℤ) (qb : ℕ) (hqb : 0 < qb) (hb : ((exprB i p q).bound (point 0)).hi * qb ≤ pb * scale)
    (s : ℝ) (hs : 0 < s) :
    DiagRamsey.symmetricProfile luWangSource 1 s ≤ (pa : ℝ) / qa + (pb : ℝ) / qb * s ∧
      DiagRamsey.symmetricProfile luWangSource 1 s ≤ (pb : ℝ) / qb + (pa : ℝ) / qa * s := by
  obtain ⟨-, a2, -, b2⟩ := enclose_AB i p q rfl (mem_knots hq hk1 hk2) h0 h1 hsA hsB
  have hA := a2.trans (le_of_scaled hqa ha)
  have hB := b2.trans (le_of_scaled hqb hb)
  obtain ⟨l1, l2⟩ := symm_le_lines h0 h1 hs
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hB hs.le]
  · nlinarith [mul_le_mul_of_nonneg_right hA hs.le]

/-- Test: the 3.5 tangent point `1421/4000` (piece 873). -/
example (s : ℝ) (hs : 0 < s) :
    DiagRamsey.symmetricProfile luWangSource 1 s ≤ (1256193360 : ℤ) / ((1000000000 : ℕ) : ℝ) +
      (265138682907 : ℤ) / ((1000000000000 : ℕ) : ℝ) * s :=
  (line_at 873 1421 4000 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 1256193360 1000000000 (by norm_num) (by decide +kernel)
    265138682907 1000000000000 (by norm_num) (by decide +kernel) s hs).1

/-! ### Argument-reduced enclosures (Q30, leonard-of-port-maurice)

Lu–Wang's fixed-point `log n` encloses `log z` as `2 atanh y`, `y = (z-1)/(z+1)`, with `n` series terms and the
remainder bound `|y|^(2n+1)/(1-y²)`, without argument reduction. At `z = 0.0057` the remainder is about 15, so
`exprA`/`exprB` are loose at small `u` (and wider than 1e-25 for most `u`). `exprAS`/`exprBS` have the same real value.
They evaluate `log z` as `log (2^k z) - k log 2`, with `2^k z ∈ (1/2, 1]`, and use exp order 32 instead of 24.
`line_atS` is `line_at` with these enclosures (prototype and exact Python port: research/leonard-of-port-maurice). -/

/-- The number of `j < 64` with `2^(j+1) p ≤ q`. For `0 < p ≤ q < 2^64 p` this is the `k` with
`2^k p ≤ q < 2^(k+1) p`, so `2^k (p/q) ∈ (1/2, 1]`. Any value is sound: it only steers the evaluation. -/
def scaleExp (p : ℤ) (q : ℕ) : ℕ :=
  ((List.range 64).filter (fun j => decide (2 ^ (j + 1) * p ≤ (q : ℤ)))).length

/-- `log z`, evaluated as `log (2^k z) - k log 2`. -/
def logS (n k : ℕ) (z : Expr) : Expr :=
  .add (.log n (.mul (.rat (2 ^ k) 1) z)) (.neg (.mul (.rat k 1) (.log n (.rat 2 1))))

theorem eval_logS (n k : ℕ) (z : Expr) (x : ℝ) (hz : 0 < z.eval x) :
    (logS n k z).eval x = Real.log (z.eval x) := by
  simp only [logS, Expr.eval]
  push_cast
  try simp only [div_one]
  rw [Real.log_mul (by positivity) hz.ne', Real.log_pow]
  ring

/-- `ProfileExpr.fp` with `log z` replaced by `logS`. -/
def fpS (cs : List ℚ) (c : ℚ) (ne nl k : ℕ) (z : Expr) : Expr :=
  .add (ProfileExpr.sub (.log nl (.add ProfileExpr.one z)) (logS nl k z)) (ProfileExpr.gp cs c ne z)

/-- `ProfileExpr.f` with `log z` replaced by `logS`. -/
def fS (cs : List ℚ) (c : ℚ) (ne nl k : ℕ) (z : Expr) : Expr :=
  .add (ProfileExpr.sub (.mul (.add ProfileExpr.one z) (.log nl (.add ProfileExpr.one z)))
      (.mul z (logS nl k z)))
    (.mul (.mul z (.exp ne (.neg z))) (ProfileExpr.p cs c z))

theorem eval_fpS (cs : List ℚ) (c : ℚ) (ne nl k : ℕ) (z : Expr) (x : ℝ) (hz : 0 < z.eval x) :
    (fpS cs c ne nl k z).eval x = (ProfileExpr.fp cs c ne nl z).eval x := by
  simp only [fpS, ProfileExpr.fp, Expr.eval, ProfileExpr.eval_sub, eval_logS nl k z x hz]

theorem eval_fS (cs : List ℚ) (c : ℚ) (ne nl k : ℕ) (z : Expr) (x : ℝ) (hz : 0 < z.eval x) :
    (fS cs c ne nl k z).eval x = (ProfileExpr.f cs c ne nl z).eval x := by
  simp only [fS, ProfileExpr.f, Expr.eval, ProfileExpr.eval_sub, eval_logS nl k z x hz]

/-- `A` and `B` of the profile of piece `i` at `p/q`, argument-reduced (same values as `exprA`, `exprB`). -/
def exprAS (i : Fin 2279) (p : ℤ) (q : ℕ) : Expr :=
  fpS (rationalData.coefficients i) (p / q) 32 48 (scaleExp p q) (.rat p q)

def exprBS (i : Fin 2279) (p : ℤ) (q : ℕ) : Expr :=
  ProfileExpr.sub (fS (rationalData.coefficients i) (p / q) 32 48 (scaleExp p q) (.rat p q))
    (.mul (.rat p q) (fpS (rationalData.coefficients i) (p / q) 32 48 (scaleExp p q) (.rat p q)))

theorem enclose_ABS (i : Fin 2279) (p : ℤ) (q : ℕ) {t : ℝ} (htq : t = (p : ℝ) / (q : ℝ))
    (ht : t ∈ Icc (rationalData.knot i.castSucc : ℝ) (rationalData.knot i.succ : ℝ)) (h0 : 0 < t)
    (h1 : t < 1) (hA : (exprAS i p q).safe (point 0) = true)
    (hB : (exprBS i p q).safe (point 0) = true) :
    deriv luWangSource t ≤ (((exprAS i p q).bound (point 0)).hi : ℝ) / (scale : ℝ) ∧
    luWangSource t - t * deriv luWangSource t ≤ (((exprBS i p q).bound (point 0)).hi : ℝ) / (scale : ℝ) := by
  obtain ⟨hdA, hdB⟩ := source_at ht h0 h1
  have hz : 0 < (Expr.rat p q).eval 0 := by simp only [Expr.eval]; rw [← htq]; exact h0
  have e1 := eval_fS (rationalData.coefficients i) (p / q) 32 48 (scaleExp p q) (.rat p q) 0 hz
  have e2 := eval_fpS (rationalData.coefficients i) (p / q) 32 48 (scaleExp p q) (.rat p q) 0 hz
  have eA : (exprAS i p q).eval 0 = deriv luWangSource t := by
    rw [hdA, htq, exprAS, e2]; simp [Expr.eval]
  have eB : (exprBS i p q).eval 0 = luWangSource t - t * deriv luWangSource t := by
    rw [hdB, htq, exprBS, ProfileExpr.eval_sub]
    simp only [Expr.eval, e1, e2]
    simp [Expr.eval]
  exact ⟨(enclose eA hA).2, (enclose eB hB).2⟩

/-- `line_at` with the argument-reduced enclosures: with `A ≤ pa/qa` and `B ≤ pb/qb`,
`F̂(s) ≤ pa/qa + (pb/qb) s` and `F̂(s) ≤ pb/qb + (pa/qa) s` for all `s > 0`. -/
theorem line_atS (i : Fin 2279) (p : ℤ) (q : ℕ) (hq : 0 < q) (h0 : 0 < (p : ℝ) / (q : ℝ))
    (h1 : (p : ℝ) / (q : ℝ) < 1)
    (hk1 : rationalData.knot i.castSucc ≤ (p : ℚ) / q) (hk2 : (p : ℚ) / q ≤ rationalData.knot i.succ)
    (hsA : (exprAS i p q).safe (point 0) = true) (hsB : (exprBS i p q).safe (point 0) = true)
    (pa : ℤ) (qa : ℕ) (hqa : 0 < qa) (ha : ((exprAS i p q).bound (point 0)).hi * qa ≤ pa * scale)
    (pb : ℤ) (qb : ℕ) (hqb : 0 < qb) (hb : ((exprBS i p q).bound (point 0)).hi * qb ≤ pb * scale)
    (s : ℝ) (hs : 0 < s) :
    DiagRamsey.symmetricProfile luWangSource 1 s ≤ (pa : ℝ) / qa + (pb : ℝ) / qb * s ∧
      DiagRamsey.symmetricProfile luWangSource 1 s ≤ (pb : ℝ) / qb + (pa : ℝ) / qa * s := by
  obtain ⟨a2, b2⟩ := enclose_ABS i p q rfl (mem_knots hq hk1 hk2) h0 h1 hsA hsB
  have hA := a2.trans (le_of_scaled hqa ha)
  have hB := b2.trans (le_of_scaled hqb hb)
  obtain ⟨l1, l2⟩ := symm_le_lines h0 h1 hs
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hB hs.le]
  · nlinarith [mul_le_mul_of_nonneg_right hA hs.le]

end LuWangBridge
