import Mathlib.Data.Rat.Defs

/-! Canonical `"num/den"` rendering of rationals, a `List Char` form of it that the kernel can
compare cheaply against string literals, and the `kernel_rfl` tactic.

`kernel_rfl` closes a goal `a = b` with the term `Eq.refl a` without asking the elaborator to
check `a ≡ b`; the definitional equality is checked only by the kernel when the declaration is
added (exactly as for `decide +kernel`), so a false goal is rejected with a kernel error. -/

namespace LuWangBridge

/-- Decimal rendering `"num/den"` of a rational. -/
def fmt (q : ℚ) : String := q.num.repr ++ "/" ++ Nat.repr q.den

/-- `fmt` as a character list: optional `-`, digits of `|num|`, `/`, digits of `den`. -/
def fmtL (q : ℚ) : List Char :=
  (if q.num < 0 then [Char.ofNat 45] else []) ++ Nat.toDigits 10 q.num.natAbs ++
    Char.ofNat 47 :: Nat.toDigits 10 q.den

/-- `fmt` built directly with `String.ofList`. -/
def fmtS (q : ℚ) : String := String.ofList (fmtL q)

theorem fmtS_eq (q : ℚ) : fmtS q = fmt q := by
  unfold fmtS fmtL fmt
  rcases h : q.num with m | m
  · simp [Int.repr, Nat.repr, String.ofList_append, String.append_assoc]
  · simp [Int.repr, Nat.repr, String.ofList_append, Int.negSucc_lt_zero, String.append_assoc]

theorem fmtS_eq_fmt : fmtS = fmt := funext fmtS_eq

open Lean Elab Tactic Meta in
/-- Close `a = b` by `Eq.refl a`, leaving the definitional check to the kernel. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  match (← g.getType).eq? with
  | some (_, a, _) => g.assign (← mkEqRefl a)
  | none => throwError "kernel_rfl: goal is not an equation"

end LuWangBridge
