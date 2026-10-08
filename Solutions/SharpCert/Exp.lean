import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kernel-checkable rational bounds for `Real.exp`

`expLo x` is a rational lower bound of `Real.exp x`, and `expLeB x z = true` certifies
`Real.exp x ≤ z`. Both are computable by kernel reduction (`decide +kernel`): Taylor
polynomial with the Lagrange-type error term of `Real.exp_bound` on `|x| ≤ 1/8`, followed by
repeated squaring, with dyadic outward rounding at precision `2^-prec`.
-/

namespace DiagRamsey.SharpCert

/-- Working precision (bits) and Taylor length. -/
def prec : ℕ := 64
def nTay : ℕ := 10
def fuel : ℕ := 40

def rdn (r : ℚ) : ℚ := (⌊r * 2 ^ prec⌋ : ℚ) / 2 ^ prec
def rup (r : ℚ) : ℚ := (⌈r * 2 ^ prec⌉ : ℚ) / 2 ^ prec

lemma rdn_le (r : ℚ) : rdn r ≤ r := by
  unfold rdn
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

lemma le_rup (r : ℚ) : r ≤ rup r := by
  unfold rup
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

lemma rdn_nonneg {r : ℚ} (h : 0 ≤ r) : 0 ≤ rdn r := by
  unfold rdn
  have : (0 : ℤ) ≤ ⌊r * 2 ^ prec⌋ := Int.floor_nonneg.mpr (by positivity)
  positivity

/-- `∑_{i<n} x^i / i!`. -/
def taySum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => taySum x n + x ^ n / (n.factorial : ℚ)

lemma taySum_cast (x : ℚ) (n : ℕ) :
    ((taySum x n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (x : ℝ) ^ m / (m.factorial : ℝ) := by
  induction n with
  | zero => simp [taySum]
  | succ n ih => rw [taySum, Finset.sum_range_succ, ← ih]; push_cast; ring

def tayErr (x : ℚ) (n : ℕ) : ℚ := |x| ^ n * ((n + 1 : ℚ) / ((n.factorial : ℚ) * n))

/-- Bounds valid for `|x| ≤ 1`. -/
def expBase (x : ℚ) : ℚ × ℚ :=
  (max 0 (rdn (taySum x nTay - tayErr x nTay)), rup (taySum x nTay + tayErr x nTay))

lemma expBase_spec {x : ℚ} (hx : |x| ≤ 1) :
    0 ≤ (expBase x).1 ∧ ((expBase x).1 : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (expBase x).2 := by
  have hxr : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have hb := Real.exp_bound hxr (n := nTay) (by norm_num [nTay])
  have herr : ((tayErr x nTay : ℚ) : ℝ) = |(x : ℝ)| ^ nTay * (nTay.succ / (nTay.factorial * nTay)) := by
    simp [tayErr]
  rw [← taySum_cast, ← herr] at hb
  have h1 := (abs_sub_le_iff.mp hb).1
  have h2 := (abs_sub_le_iff.mp hb).2
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · simp only [expBase]
    push_cast
    apply max_le (Real.exp_pos _).le
    have := rdn_le (taySum x nTay - tayErr x nTay)
    have : ((rdn (taySum x nTay - tayErr x nTay) : ℚ) : ℝ) ≤
        ((taySum x nTay : ℚ) : ℝ) - ((tayErr x nTay : ℚ) : ℝ) := by exact_mod_cast this
    linarith
  · simp only [expBase]
    have := le_rup (taySum x nTay + tayErr x nTay)
    have : ((taySum x nTay : ℚ) : ℝ) + ((tayErr x nTay : ℚ) : ℝ) ≤
        ((rup (taySum x nTay + tayErr x nTay) : ℚ) : ℝ) := by exact_mod_cast this
    linarith

/-- Halve until `|x| ≤ 1/8`, then square back. `none` if the fuel runs out. -/
def expB : ℕ → ℚ → Option (ℚ × ℚ)
  | 0, x => if |x| ≤ 1 / 8 then some (expBase x) else none
  | f + 1, x =>
    if |x| ≤ 1 / 8 then some (expBase x) else
      match expB f (x / 2) with
      | some lh => some (rdn (lh.1 ^ 2), rup (lh.2 ^ 2))
      | none => none

lemma expB_spec : ∀ (f : ℕ) (x : ℚ) (l h : ℚ), expB f x = some (l, h) →
    0 ≤ l ∧ (l : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ h := by
  intro f
  induction f with
  | zero =>
    intro x l h hx
    simp only [expB] at hx
    split_ifs at hx with h8
    · cases hx; exact expBase_spec (h8.trans (by norm_num))
  | succ f ih =>
    intro x l h hx
    simp only [expB] at hx
    split_ifs at hx with h8
    · cases hx; exact expBase_spec (h8.trans (by norm_num))
    · rcases hrec : expB f (x / 2) with _ | ⟨l', h'⟩
      · rw [hrec] at hx; cases hx
      · rw [hrec] at hx
        simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        obtain ⟨hl0, hl, hh⟩ := ih _ _ _ hrec
        have hsq : Real.exp (x : ℝ) = Real.exp ((x / 2 : ℚ) : ℝ) ^ 2 := by
          rw [sq, ← Real.exp_add]; push_cast; ring_nf
        refine ⟨rdn_nonneg (by positivity), ?_, ?_⟩
        · have h0 : rdn (l' ^ (2 : ℕ)) ≤ l' ^ (2 : ℕ) := rdn_le _
          have h1 : ((rdn (l' ^ (2 : ℕ)) : ℚ) : ℝ) ≤ ((l' : ℝ)) ^ (2 : ℕ) := by
            exact_mod_cast h0
          rw [hsq]
          have hl0' : (0 : ℝ) ≤ l' := by exact_mod_cast hl0
          nlinarith [pow_le_pow_left₀ hl0' hl 2]
        · have h0 : h' ^ (2 : ℕ) ≤ rup (h' ^ (2 : ℕ)) := le_rup _
          have h1 : ((h' : ℝ)) ^ (2 : ℕ) ≤ ((rup (h' ^ (2 : ℕ)) : ℚ) : ℝ) := by
            exact_mod_cast h0
          rw [hsq]
          nlinarith [pow_le_pow_left₀ (Real.exp_pos _).le hh 2]

/-- A rational lower bound of `exp x`. -/
def expLo (x : ℚ) : ℚ :=
  match expB fuel (rdn x) with
  | some lh => lh.1
  | none => 0

lemma expLo_le (x : ℚ) : (expLo x : ℝ) ≤ Real.exp x := by
  unfold expLo
  rcases hb : expB fuel (rdn x) with _ | ⟨l, h⟩
  · simp [(Real.exp_pos _).le]
  · obtain ⟨-, hl, -⟩ := expB_spec _ _ _ _ hb
    have : ((rdn x : ℚ) : ℝ) ≤ x := by exact_mod_cast rdn_le x
    exact hl.trans (Real.exp_le_exp.mpr this)

/-- `expLeB x z = true` certifies `exp x ≤ z`. -/
def expLeB (x z : ℚ) : Bool :=
  match expB fuel (rup x) with
  | some lh => decide (lh.2 ≤ z)
  | none => false

lemma exp_le_of_expLeB {x z : ℚ} (hb : expLeB x z = true) : Real.exp x ≤ z := by
  unfold expLeB at hb
  rcases he : expB fuel (rup x) with _ | ⟨l, h⟩
  · rw [he] at hb; cases hb
  · rw [he] at hb
    obtain ⟨-, -, hh⟩ := expB_spec _ _ _ _ he
    have hx : (x : ℝ) ≤ ((rup x : ℚ) : ℝ) := by exact_mod_cast le_rup x
    have hz : (h : ℝ) ≤ z := by exact_mod_cast of_decide_eq_true hb
    exact (Real.exp_le_exp.mpr hx).trans (hh.trans hz)

/-- `0 < y`, `y ≤ expLo t` certifies `log y ≤ t`. -/
lemma log_le_of_le_expLo {y t : ℚ} (hy : 0 < y) (h : y ≤ expLo t) : Real.log y ≤ t := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have : (y : ℝ) ≤ Real.exp t := (by exact_mod_cast h : (y : ℝ) ≤ expLo t).trans (expLo_le t)
  rw [Real.log_le_iff_le_exp hy']
  exact this

/-- `0 < y`, `expLeB t y` certifies `t ≤ log y`. -/
lemma le_log_of_expLeB {y t : ℚ} (hy : 0 < y) (h : expLeB t y = true) : (t : ℝ) ≤ Real.log y := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  rw [Real.le_log_iff_exp_le hy']
  exact exp_le_of_expLeB h

end DiagRamsey.SharpCert
