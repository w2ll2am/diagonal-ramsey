import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Finite quantities of the nested moment potential (diagonal Ramsey project).

A red/blue colouring is a simple graph `G` (red edges = edges of `G`). For a row set `X` and a column `y`,
`redDens G X y` is the proportion of rows of `X` red-adjacent to `y` (the column degree `g_y`). The nested moment
potential at shift `c` with exponents `w, r, s` is
`Φ_c(X, Y) = |X|^w * |Y| * (E_{y ∈ Y} (g_y - c)_+^s)^(r/s)`, all powers real (`Real.rpow`).
Empty `X` or `Y` give potential `0` (for `w ≠ 0`; `0/0 = 0` in Lean).
-/

namespace DiagRamsey

variable {V : Type*}

/-- Number of vertices of `S` red-adjacent to `y`. -/
def redDeg (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (y : V) : ℕ :=
  (S.filter (fun u => G.Adj u y)).card

/-- Red density from the row set `S` to the column `y`: `redDeg G S y / |S|` (zero if `S` is empty). -/
noncomputable def redDens (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (y : V) : ℝ :=
  (redDeg G S y : ℝ) / (S.card : ℝ)

/-- The blue neighbourhood `B_v` of `v` inside `X`: vertices of `X` other than `v` not red-adjacent to `v`. -/
def blueNbrs (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V] (X : Finset V) (v : V) : Finset V :=
  X.filter (fun u => u ≠ v ∧ ¬ G.Adj u v)

/-- The red neighbourhood `R_v` of `v` inside `X`. -/
def redNbrs (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (v : V) : Finset V :=
  X.filter (fun u => G.Adj u v)

/-- Normalised clipped column moment `E_{y ∈ Y} (redDens G X y - c)_+^s` (zero if `Y` is empty). -/
noncomputable def clippedMoment (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) (c s : ℝ) : ℝ :=
  (∑ y ∈ Y, (max (redDens G X y - c) 0) ^ s) / (Y.card : ℝ)

/-- The nested moment potential `Φ_c(X, Y) = |X|^w * |Y| * (clippedMoment G X Y c s)^(r/s)`. -/
noncomputable def nestedPot (G : SimpleGraph V) [DecidableRel G.Adj] (w r s c : ℝ) (X Y : Finset V) : ℝ :=
  (X.card : ℝ) ^ w * (Y.card : ℝ) * (clippedMoment G X Y c s) ^ (r / s)

end DiagRamsey
