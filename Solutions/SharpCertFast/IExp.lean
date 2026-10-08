import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
namespace DiagRamsey.SharpCert.IExp
open Real Finset

/-- fixed-point scale -/
def S : ℕ := 2 ^ 64

/-- floor Taylor terms of `S * (m/D)^n / n!` -/
def tLo (m D : ℕ) : ℕ → ℕ
  | 0 => S
  | n + 1 => tLo m D n * m / (D * (n + 1))

def sLo (m D : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sLo m D n + tLo m D n

lemma tLo_le (m D : ℕ) (hD : 0 < D) : ∀ n, (tLo m D n : ℝ) ≤ S * ((m : ℝ) / D) ^ n / n.factorial
  | 0 => by simp [tLo]
  | n + 1 => by
    have ih := tLo_le m D hD n
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have hD0 : (D : ℝ) ≠ 0 := hD'.ne'
    calc (tLo m D (n + 1) : ℝ) ≤ (tLo m D n * m : ℕ) / ((D * (n + 1) : ℕ) : ℝ) := Nat.cast_div_le
      _ = (tLo m D n : ℝ) * ((m : ℝ) / D / (n + 1)) := by push_cast; field_simp
      _ ≤ (S * ((m : ℝ) ^ n / (D : ℝ) ^ n) / n.factorial) * ((m : ℝ) / D / (n + 1)) := by
          rw [← div_pow]; exact mul_le_mul_of_nonneg_right ih (by positivity)
      _ = S * ((m : ℝ) / D) ^ (n + 1) / (n + 1).factorial := by
          rw [Nat.factorial_succ, div_pow]; push_cast; field_simp; ring

lemma sLo_le (m D : ℕ) (hD : 0 < D) (n : ℕ) : (sLo m D n : ℝ) ≤ S * Real.exp ((m : ℝ) / D) := by
  have h : ∀ n, (sLo m D n : ℝ) ≤ S * ∑ i ∈ range n, ((m : ℝ) / D) ^ i / i.factorial := by
    intro n
    induction n with
    | zero => simp [sLo]
    | succ n ih =>
      rw [sLo, sum_range_succ]; push_cast
      have := tLo_le m D hD n
      rw [mul_div_assoc] at this
      rw [mul_add]; linarith
  refine (h n).trans ?_
  have hS : (0 : ℝ) ≤ S := by positivity
  exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) n) hS

/-- square-back with floor -/
def sqLo : ℕ → ℕ → ℕ
  | 0, v => v
  | k + 1, v => sqLo k (v * v / S)

lemma sqLo_le : ∀ (k v : ℕ) (y : ℝ), (v : ℝ) ≤ S * Real.exp y →
    (sqLo k v : ℝ) ≤ S * Real.exp (2 ^ k * y)
  | 0, v, y, h => by simpa [sqLo] using h
  | k + 1, v, y, h => by
    have hS : (0 : ℝ) < S := by unfold S; positivity
    have h2 : ((v * v / S : ℕ) : ℝ) ≤ S * Real.exp (2 * y) := by
      calc ((v * v / S : ℕ) : ℝ) ≤ ((v * v : ℕ) : ℝ) / (S : ℝ) := Nat.cast_div_le
        _ ≤ (S * Real.exp y) * (S * Real.exp y) / S := by
            push_cast; gcongr
        _ = S * Real.exp (2 * y) := by
            rw [show (2 : ℝ) * y = y + y by ring, Real.exp_add]; field_simp
    have := sqLo_le k _ (2 * y) h2
    rw [pow_succ, mul_assoc]; exact this

lemma div_le_div_add_one (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((a / b : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := a) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  have : (a : ℝ) < (a / b : ℕ) * b + b := by exact_mod_cast h
  nlinarith

/-- ceiling-ish Taylor terms, `≥ S * (m/D)^n / n!` -/
def tHi (m D : ℕ) : ℕ → ℕ
  | 0 => S
  | n + 1 => tHi m D n * m / (D * (n + 1)) + 1

def sHi (m D : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sHi m D n + tHi m D n

lemma le_tHi (m D : ℕ) (hD : 0 < D) : ∀ n, S * ((m : ℝ) / D) ^ n / n.factorial ≤ (tHi m D n : ℝ)
  | 0 => by simp [tHi]
  | n + 1 => by
    have ih := le_tHi m D hD n
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have hD0 : (D : ℝ) ≠ 0 := hD'.ne'
    have hpos : 0 < D * (n + 1) := by positivity
    calc S * ((m : ℝ) / D) ^ (n + 1) / (n + 1).factorial
        = (S * ((m : ℝ) / D) ^ n / n.factorial) * ((m : ℝ) / D / (n + 1)) := by
          rw [Nat.factorial_succ, div_pow, div_pow]; push_cast; field_simp; ring
      _ ≤ (tHi m D n : ℝ) * ((m : ℝ) / D / (n + 1)) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = ((tHi m D n * m : ℕ) : ℝ) / ((D * (n + 1) : ℕ) : ℝ) := by push_cast; field_simp
      _ ≤ _ := by rw [tHi, Nat.cast_add, Nat.cast_one]; exact div_le_div_add_one _ _ hpos

lemma le_sHi (m D : ℕ) (hD : 0 < D) (n : ℕ) :
    S * ∑ i ∈ range n, ((m : ℝ) / D) ^ i / i.factorial ≤ (sHi m D n : ℝ) := by
  induction n with
  | zero => simp [sHi]
  | succ n ih =>
    rw [sHi, sum_range_succ]; push_cast
    have := le_tHi m D hD n
    rw [mul_div_assoc] at this
    rw [mul_add]; linarith

/-- Taylor upper bound with the `Real.exp_bound` tail, valid for `m ≤ D`. -/
def uHi (m D N : ℕ) : ℕ := sHi m D N + tHi m D N * (N + 1) / N + 1

lemma le_uHi (m D N : ℕ) (hD : 0 < D) (hmD : m ≤ D) (hN : 0 < N) :
    S * Real.exp ((m : ℝ) / D) ≤ (uHi m D N : ℝ) := by
  set x : ℝ := (m : ℝ) / D
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hx0 : 0 ≤ x := by positivity
  have hx1 : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0, div_le_one hD']; exact_mod_cast hmD
  have hb := Real.exp_bound hx1 hN
  have hS : (0 : ℝ) < S := by unfold S; positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : Real.exp x ≤ ∑ i ∈ range N, x ^ i / i.factorial +
      x ^ N / N.factorial * ((N + 1) / N) := by
    have := (abs_le.mp hb).2
    rw [abs_of_nonneg hx0] at this
    have e : x ^ N * ((N.succ : ℝ) / (N.factorial * N)) = x ^ N / N.factorial * ((N + 1) / N) := by
      push_cast; field_simp
    linarith
  have h2 := le_sHi m D hD N
  have h3 := le_tHi m D hD N
  have h4 : (tHi m D N : ℝ) * ((N + 1) / N) ≤ ((tHi m D N * (N + 1) / N : ℕ) : ℝ) + 1 := by
    have := div_le_div_add_one (tHi m D N * (N + 1)) N hN
    push_cast at this ⊢; rw [mul_div_assoc] at this; exact this
  have h5 : S * (x ^ N / N.factorial * ((N + 1) / N)) ≤ (tHi m D N : ℝ) * ((N + 1) / N) := by
    have key : (S : ℝ) * (x ^ N / N.factorial * ((N + 1) / N)) = (S * x ^ N / N.factorial) * ((N + 1) / N) := by
      ring
    rw [key]; exact mul_le_mul_of_nonneg_right h3 (by positivity)
  unfold uHi; push_cast
  nlinarith

/-- square-back with floor + 1 -/
def sqHi : ℕ → ℕ → ℕ
  | 0, v => v
  | k + 1, v => sqHi k (v * v / S + 1)

lemma le_sqHi : ∀ (k v : ℕ) (y : ℝ), S * Real.exp y ≤ (v : ℝ) →
    S * Real.exp (2 ^ k * y) ≤ (sqHi k v : ℝ)
  | 0, v, y, h => by simpa [sqHi] using h
  | k + 1, v, y, h => by
    have hS : (0 : ℝ) < S := by unfold S; positivity
    have h2 : S * Real.exp (2 * y) ≤ ((v * v / S + 1 : ℕ) : ℝ) := by
      have hSpos : 0 < S := by unfold S; positivity
      calc S * Real.exp (2 * y) = (S * Real.exp y) * (S * Real.exp y) / S := by
            rw [show (2 : ℝ) * y = y + y by ring, Real.exp_add]; field_simp
        _ ≤ ((v * v : ℕ) : ℝ) / (S : ℝ) := by
            push_cast; gcongr
        _ ≤ _ := by rw [Nat.cast_add, Nat.cast_one]; exact div_le_div_add_one _ _ hSpos
    have := le_sqHi k _ (2 * y) h2
    rw [pow_succ, mul_assoc]; exact this

/-! ## Fixed-point interface: `exp (a / 2^64)` for `a : ℕ`. -/

def nT : ℕ := 10

/-- halving count: `a < 2^(61 + kOf a)`, so `a / 2^(64 + kOf a) < 1/8`. -/
def kOf (a : ℕ) : ℕ := Nat.log2 (a / 2 ^ 61) + 1

def loNat (a : ℕ) : ℕ := sqLo (kOf a) (sLo a (2 ^ (64 + kOf a)) nT)

def hiNat (a : ℕ) : Option ℕ :=
  if a ≤ 2 ^ (64 + kOf a) then some (sqHi (kOf a) (uHi a (2 ^ (64 + kOf a)) nT)) else none

lemma scale_eq (a k : ℕ) : (2 : ℝ) ^ k * ((a : ℝ) / ((2 ^ (64 + k) : ℕ) : ℝ)) = (a : ℝ) / 2 ^ 64 := by
  push_cast; rw [pow_add]; field_simp

lemma loNat_le (a : ℕ) : (loNat a : ℝ) ≤ S * Real.exp ((a : ℝ) / 2 ^ 64) := by
  have h := sqLo_le (kOf a) _ _ (sLo_le a (2 ^ (64 + kOf a)) (by positivity) nT)
  rw [scale_eq] at h; exact h

lemma le_hiNat {a U : ℕ} (h : hiNat a = some U) : S * Real.exp ((a : ℝ) / 2 ^ 64) ≤ (U : ℝ) := by
  unfold hiNat at h
  split_ifs at h with ha
  cases h
  have := le_sqHi (kOf a) _ _ (le_uHi a (2 ^ (64 + kOf a)) nT (by positivity) ha (by norm_num [nT]))
  rw [scale_eq] at this; exact this

lemma S_pos : (0 : ℝ) < S := by unfold S; positivity

/-- A rational lower bound of `exp x`. -/
def expLo (x : ℚ) : ℚ :=
  let m := ⌊x * 2 ^ 64⌋
  if 0 ≤ m then ((loNat m.toNat : ℕ) : ℚ) / (S : ℚ)
  else match hiNat (-m).toNat with
    | some U => ((S * S / U : ℕ) : ℚ) / (S : ℚ)
    | none => 0

/-- `expLeB x z = true` certifies `exp x ≤ z`. -/
def expLeB (x z : ℚ) : Bool :=
  let m := ⌈x * 2 ^ 64⌉
  if 0 ≤ m then
    match hiNat m.toNat with
    | some U => decide (((U : ℕ) : ℚ) / (S : ℚ) ≤ z)
    | none => false
  else
    let L := loNat (-m).toNat
    if L = 0 then false else decide (((S * S / L + 1 : ℕ) : ℚ) / (S : ℚ) ≤ z)

lemma floor_div_le (x : ℚ) : ((⌊x * 2 ^ 64⌋ : ℤ) : ℝ) / 2 ^ 64 ≤ x := by
  have h : ((⌊x * 2 ^ 64⌋ : ℤ) : ℚ) ≤ x * 2 ^ 64 := Int.floor_le _
  have h' : ((⌊x * 2 ^ 64⌋ : ℤ) : ℝ) ≤ (x : ℝ) * 2 ^ 64 := by exact_mod_cast h
  rw [div_le_iff₀ (by positivity)]; exact h'

lemma le_ceil_div (x : ℚ) : (x : ℝ) ≤ ((⌈x * 2 ^ 64⌉ : ℤ) : ℝ) / 2 ^ 64 := by
  have h : x * 2 ^ 64 ≤ ((⌈x * 2 ^ 64⌉ : ℤ) : ℚ) := Int.le_ceil _
  have h' : (x : ℝ) * 2 ^ 64 ≤ ((⌈x * 2 ^ 64⌉ : ℤ) : ℝ) := by exact_mod_cast h
  rw [le_div_iff₀ (by positivity)]; exact h'

lemma toNat_cast {m : ℤ} (h : 0 ≤ m) : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
  have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg h
  exact_mod_cast this

lemma expLo_le (x : ℚ) : (expLo x : ℝ) ≤ Real.exp x := by
  have hS := S_pos
  have hfl := floor_div_le x
  set m := ⌊x * 2 ^ 64⌋ with hm
  unfold expLo
  simp only [← hm]
  split_ifs with h0
  · have h1 := loNat_le m.toNat
    rw [toNat_cast h0] at h1
    push_cast
    rw [div_le_iff₀ hS]
    calc (loNat m.toNat : ℝ) ≤ S * Real.exp ((m : ℝ) / 2 ^ 64) := h1
      _ ≤ S * Real.exp x := by gcongr
      _ = Real.exp x * S := by ring
  · rcases hU : hiNat (-m).toNat with _ | U
    · simp [(Real.exp_pos _).le]
    · have h1 := le_hiNat hU
      rw [toNat_cast (by omega)] at h1
      push_cast at h1
      have hUpos : (0 : ℝ) < U := lt_of_lt_of_le (by positivity) h1
      push_cast
      rw [div_le_iff₀ hS]
      calc (((S * S / U : ℕ) : ℝ)) ≤ ((S * S : ℕ) : ℝ) / (U : ℝ) := Nat.cast_div_le
        _ ≤ (S : ℝ) * S / (S * Real.exp (-(m : ℝ) / 2 ^ 64)) := by
            push_cast; gcongr
        _ = S * Real.exp ((m : ℝ) / 2 ^ 64) := by
            rw [neg_div, Real.exp_neg]; field_simp
        _ ≤ S * Real.exp x := by gcongr
        _ = Real.exp x * S := by ring

lemma exp_le_of_expLeB {x z : ℚ} (hb : expLeB x z = true) : Real.exp x ≤ z := by
  have hS := S_pos
  have hce := le_ceil_div x
  set m := ⌈x * 2 ^ 64⌉ with hm
  unfold expLeB at hb
  simp only [← hm] at hb
  split_ifs at hb with h0 hL
  · rcases hU : hiNat m.toNat with _ | U
    · rw [hU] at hb; cases hb
    · rw [hU] at hb
      have hz : ((U : ℚ) / (S : ℚ) : ℝ) ≤ z := by exact_mod_cast of_decide_eq_true hb
      have h1 := le_hiNat hU
      rw [toNat_cast h0] at h1
      push_cast at hz
      rw [div_le_iff₀ hS] at hz
      have : Real.exp x * S ≤ z * S := by
        calc Real.exp x * S ≤ S * Real.exp ((m : ℝ) / 2 ^ 64) := by
              rw [mul_comm]; gcongr
          _ ≤ U := h1
          _ ≤ _ := by linarith
      exact le_of_mul_le_mul_right this hS
  · have hz := of_decide_eq_true hb
    have hz' : (((S * S / loNat (-m).toNat + 1 : ℕ) : ℚ) / (S : ℚ) : ℝ) ≤ z := by exact_mod_cast hz
    have h1 := loNat_le (-m).toNat
    rw [toNat_cast (by omega)] at h1
    push_cast at h1 hz'
    set L := loNat (-m).toNat
    have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
    rw [div_le_iff₀ hS] at hz'
    have key : Real.exp x * S ≤ ((S * S : ℕ) : ℝ) / L := by
      calc Real.exp x * S ≤ S * Real.exp ((m : ℝ) / 2 ^ 64) := by rw [mul_comm]; gcongr
        _ = (S : ℝ) * S / (S * Real.exp (-(m : ℝ) / 2 ^ 64)) := by
            rw [neg_div, Real.exp_neg]; field_simp
        _ ≤ (S : ℝ) * S / L := by gcongr
        _ = _ := by push_cast; ring
    have h2 := div_le_div_add_one (S * S) L (Nat.pos_of_ne_zero hL)
    have : Real.exp x * S ≤ z * S := by push_cast at h2 key ⊢; linarith
    exact le_of_mul_le_mul_right this hS

lemma log_le_of_le_expLo {y t : ℚ} (hy : 0 < y) (h : y ≤ expLo t) : Real.log y ≤ t := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have : (y : ℝ) ≤ Real.exp t := (by exact_mod_cast h : (y : ℝ) ≤ expLo t).trans (expLo_le t)
  rw [Real.log_le_iff_le_exp hy']
  exact this

lemma le_log_of_expLeB {y t : ℚ} (hy : 0 < y) (h : expLeB t y = true) : (t : ℝ) ≤ Real.log y := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  rw [Real.le_log_iff_exp_le hy']
  exact exp_le_of_expLeB h

end DiagRamsey.SharpCert.IExp
