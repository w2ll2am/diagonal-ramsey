import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Fin.Basic

/-!
# Piecewise-affine inequalities from finitely many points (P0.6 infrastructure)

Every inequality of an exported v5 bank compares piecewise-affine functions on an interval: profiles, leaf
lines, route values, reflected profiles `r L(1/r)` and source tangents. `AffineBetween bp h` says that `h` is affine
on every segment `[bp i, bp (i+1)]` of a strictly increasing breakpoint list `bp : Fin (n+1) → ℝ`. Then
* `nonneg_of_breakpoints`: `h ≥ 0` at the breakpoints implies `h ≥ 0` on `[bp 0, bp n]`;
* closure: affine functions, sums, scalar multiples and differences are `AffineBetween` any list.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey.PL

/-- `h` is affine on each segment `[bp i, bp (i+1)]`. -/
def AffineBetween {n : ℕ} (bp : Fin (n + 1) → ℝ) (h : ℝ → ℝ) : Prop :=
  ∀ i : Fin n, ∀ r : ℝ, bp i.castSucc ≤ r → r ≤ bp i.succ →
    h r * (bp i.succ - bp i.castSucc) = (bp i.succ - r) * h (bp i.castSucc) + (r - bp i.castSucc) * h (bp i.succ)

lemma affineBetween_affine {n : ℕ} (bp : Fin (n + 1) → ℝ) (a b : ℝ) :
    AffineBetween bp (fun r => a + b * r) := by
  intro i r _ _; ring

lemma AffineBetween.add {n : ℕ} {bp : Fin (n + 1) → ℝ} {f g : ℝ → ℝ} (hf : AffineBetween bp f)
    (hg : AffineBetween bp g) : AffineBetween bp (fun r => f r + g r) := by
  intro i r h1 h2
  have := hf i r h1 h2; have := hg i r h1 h2
  simp only; linarith

lemma AffineBetween.smul {n : ℕ} {bp : Fin (n + 1) → ℝ} {f : ℝ → ℝ} (c : ℝ) (hf : AffineBetween bp f) :
    AffineBetween bp (fun r => c * f r) := by
  intro i r h1 h2
  have := hf i r h1 h2
  simp only
  linear_combination c * this

lemma AffineBetween.sub {n : ℕ} {bp : Fin (n + 1) → ℝ} {f g : ℝ → ℝ} (hf : AffineBetween bp f)
    (hg : AffineBetween bp g) : AffineBetween bp (fun r => f r - g r) := by
  intro i r h1 h2
  have := hf i r h1 h2; have := hg i r h1 h2
  simp only; linarith

/-- Nonnegativity on a segment from its endpoints. -/
lemma nonneg_segment {a b ha hb r hr : ℝ} (hab : a < b) (h1 : a ≤ r) (h2 : r ≤ b)
    (haff : hr * (b - a) = (b - r) * ha + (r - a) * hb) (h0a : 0 ≤ ha) (h0b : 0 ≤ hb) : 0 ≤ hr := by
  have hpos : 0 < b - a := sub_pos.mpr hab
  have : 0 ≤ hr * (b - a) := by rw [haff]; positivity
  exact nonneg_of_mul_nonneg_left this hpos

/-- The main lemma: nonnegative at the breakpoints and affine between them ⇒ nonnegative on `[bp 0, bp n]`. -/
lemma nonneg_of_breakpoints {n : ℕ} (bp : Fin (n + 1) → ℝ) (hmono : StrictMono bp) (h : ℝ → ℝ)
    (haff : AffineBetween bp h) (hpts : ∀ i, 0 ≤ h (bp i)) :
    ∀ r : ℝ, bp 0 ≤ r → r ≤ bp (Fin.last n) → 0 ≤ h r := by
  intro r h0 hn
  -- the last breakpoint `≤ r`
  induction n with
  | zero =>
    have : r = bp 0 := le_antisymm (by simpa using hn) h0
    rw [this]; exact hpts 0
  | succ n ih =>
    by_cases hr : r ≤ bp (Fin.last n).castSucc
    · -- restrict to the first `n+1` breakpoints
      have := ih (fun i => bp i.castSucc) (hmono.comp Fin.strictMono_castSucc)
        (fun i r h1 h2 => haff i.castSucc r h1 h2) (fun i => hpts _) (by simpa using h0) hr
      exact this
    · push_neg at hr
      exact nonneg_segment (hmono (Fin.castSucc_lt_succ (i := Fin.last n))) hr.le hn
        (haff (Fin.last n) r hr.le hn) (hpts _) (hpts _)

lemma affineBetween_sum {n : ℕ} {bp : Fin (n + 1) → ℝ} {ι : Type} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ j ∈ S, AffineBetween bp (f j)) : AffineBetween bp (fun r => ∑ j ∈ S, f j r) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro i r _ _; simp
  | insert j S hj ih =>
    intro i r h1 h2
    simp only [Finset.sum_insert hj]
    have a := hf j (Finset.mem_insert_self _ _) i r h1 h2
    have b := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)) i r h1 h2
    simp only at b
    linarith

/-- The piecewise-linear interpolant of `(x k, y k)` (clamp form; equals `y 0` left of `x 0`). -/
noncomputable def plEval {N : ℕ} (x y : Fin (N + 1) → ℝ) (r : ℝ) : ℝ :=
  y 0 + ∑ i : Fin N, (y i.succ - y i.castSucc) / (x i.succ - x i.castSucc) *
    max 0 (min r (x i.succ) - x i.castSucc)

/-- No knot of `x` strictly inside any segment of `bp`. -/
def NoKnotInside {N n : ℕ} (x : Fin (N + 1) → ℝ) (bp : Fin (n + 1) → ℝ) : Prop :=
  ∀ (i : Fin n) (k : Fin (N + 1)), x k ≤ bp i.castSucc ∨ bp i.succ ≤ x k

lemma clamp_affine {N n : ℕ} (x : Fin (N + 1) → ℝ) (hx : StrictMono x) (bp : Fin (n + 1) → ℝ)
    (hbp : StrictMono bp) (hno : NoKnotInside x bp) (j : Fin N) :
    AffineBetween bp (fun r => max 0 (min r (x j.succ) - x j.castSucc)) := by
  intro i r h1 h2
  have hab : bp i.castSucc < bp i.succ := hbp (Fin.castSucc_lt_succ (i := i))
  have hj : x j.castSucc < x j.succ := hx (Fin.castSucc_lt_succ (i := j))
  rcases hno i j.castSucc with hA | hA <;> rcases hno i j.succ with hB | hB
  · -- both knots left of the segment: constant `x_{j+1} - x_j`
    have e : ∀ t, bp i.castSucc ≤ t → max 0 (min t (x j.succ) - x j.castSucc) = x j.succ - x j.castSucc := by
      intro t ht; rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    simp only
    rw [e r h1, e _ le_rfl, e _ hab.le]; ring
  · -- `x_j ≤ a`, `b ≤ x_{j+1}`: affine `t - x_j`
    have e : ∀ t, bp i.castSucc ≤ t → t ≤ bp i.succ →
        max 0 (min t (x j.succ) - x j.castSucc) = t - x j.castSucc := by
      intro t ht1 ht2; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    simp only
    rw [e r h1 h2, e _ le_rfl hab.le, e _ hab.le le_rfl]; ring
  · exfalso; linarith
  · -- both knots right of the segment: `0`
    have e : ∀ t, t ≤ bp i.succ → max 0 (min t (x j.succ) - x j.castSucc) = 0 := by
      intro t ht; rw [max_eq_left (by linarith [min_le_left t (x j.succ)])]
    simp only
    rw [e r h2, e _ hab.le, e _ le_rfl]; ring

lemma plEval_affine {N n : ℕ} (x y : Fin (N + 1) → ℝ) (hx : StrictMono x) (bp : Fin (n + 1) → ℝ)
    (hbp : StrictMono bp) (hno : NoKnotInside x bp) : AffineBetween bp (plEval x y) := by
  have h := (affineBetween_affine bp (y 0) 0).add (affineBetween_sum (bp := bp) Finset.univ
    (fun i r => (y i.succ - y i.castSucc) / (x i.succ - x i.castSucc) * max 0 (min r (x i.succ) - x i.castSucc))
    (fun i _ => (clamp_affine x hx bp hbp hno i).smul _))
  intro i r h1 h2
  have := h i r h1 h2
  simp only [zero_mul, add_zero] at this
  exact this

/-- No knot of `x` strictly inside any reflected segment `(1/bp_{i+1}, 1/bp_i)`. -/
def NoKnotInsideRefl {N n : ℕ} (x : Fin (N + 1) → ℝ) (bp : Fin (n + 1) → ℝ) : Prop :=
  ∀ (i : Fin n) (k : Fin (N + 1)), x k ≤ 1 / bp i.succ ∨ 1 / bp i.castSucc ≤ x k

lemma plEval_refl_affine {N n : ℕ} (x y : Fin (N + 1) → ℝ) (hx : StrictMono x) (bp : Fin (n + 1) → ℝ)
    (hbp : StrictMono bp) (hpos : 0 < bp 0) (hno : NoKnotInsideRefl x bp) :
    AffineBetween bp (fun r => r * plEval x y (1 / r)) := by
  intro i r h1 h2
  have hab : bp i.castSucc < bp i.succ := hbp (Fin.castSucc_lt_succ (i := i))
  have ha0 : 0 < bp i.castSucc := lt_of_lt_of_le hpos (hbp.monotone (Fin.zero_le _))
  have hr0 : 0 < r := lt_of_lt_of_le ha0 h1
  have hb0 : 0 < bp i.succ := lt_of_lt_of_le ha0 hab.le
  -- each clamp term, multiplied by `r`, is affine on the segment
  have hterm : ∀ j : Fin N, ∀ t, bp i.castSucc ≤ t → t ≤ bp i.succ →
      t * max 0 (min (1 / t) (x j.succ) - x j.castSucc) =
        if x j.succ ≤ 1 / bp i.succ then t * (x j.succ - x j.castSucc)
        else if x j.castSucc ≤ 1 / bp i.succ then 1 - x j.castSucc * t else 0 := by
    intro j t ht1 ht2
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht1
    have hj : x j.castSucc < x j.succ := hx (Fin.castSucc_lt_succ (i := j))
    have hinv1 : 1 / bp i.succ ≤ 1 / t := one_div_le_one_div_of_le ht0 ht2
    have hinv2 : 1 / t ≤ 1 / bp i.castSucc := one_div_le_one_div_of_le ha0 ht1
    split_ifs with hA hB
    · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    · -- x_j ≤ 1/b < x_{j+1}, so 1/a ≤ x_{j+1}
      have hB' : 1 / bp i.castSucc ≤ x j.succ := (hno i j.succ).resolve_left hA
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      field_simp
    · -- both knots right of 1/a
      have hA' : 1 / bp i.castSucc ≤ x j.castSucc := (hno i j.castSucc).resolve_left hB
      rw [max_eq_left (by linarith [min_le_left (1 / t) (x j.succ)])]; ring
  have hexp : ∀ t, bp i.castSucc ≤ t → t ≤ bp i.succ →
      t * plEval x y (1 / t) = t * y 0 + ∑ j : Fin N, (y j.succ - y j.castSucc) / (x j.succ - x j.castSucc) *
        (if x j.succ ≤ 1 / bp i.succ then t * (x j.succ - x j.castSucc)
          else if x j.castSucc ≤ 1 / bp i.succ then 1 - x j.castSucc * t else 0) := by
    intro t ht1 ht2
    unfold plEval
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← hterm j t ht1 ht2]; ring
  -- the right side is affine in t
  have haff : AffineBetween (fun k : Fin 2 => if k = 0 then bp i.castSucc else bp i.succ)
      (fun t => t * y 0 + ∑ j : Fin N, (y j.succ - y j.castSucc) / (x j.succ - x j.castSucc) *
        (if x j.succ ≤ 1 / bp i.succ then t * (x j.succ - x j.castSucc)
          else if x j.castSucc ≤ 1 / bp i.succ then 1 - x j.castSucc * t else 0)) := by
    apply AffineBetween.add
    · intro k t _ _; ring
    · apply affineBetween_sum
      intro j _
      apply AffineBetween.smul
      split_ifs <;> (intro k t _ _; ring)
  have := haff 0 r (by simpa using h1) (by simpa using h2)
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.isValue, if_pos, one_ne_zero, if_false] at this
  simp only
  rw [hexp r h1 h2, hexp _ le_rfl hab.le, hexp _ hab.le le_rfl]
  convert this using 2 <;> simp

end DiagRamsey.PL
