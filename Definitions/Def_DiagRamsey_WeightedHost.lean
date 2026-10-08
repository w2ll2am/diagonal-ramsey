import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Weighted finite hosts and the nested column-moment potential (diagonal Ramsey project).

A red/blue colouring of the complete graph on a finite vertex type `V` is a simple graph `G` on `V`:
an edge `uv` (`u ≠ v`) is red when `G.Adj u v` and blue otherwise, i.e. blue edges are the edges of `Gᶜ`.
All densities are normalised counts; an average over an empty set is `0` (Lean's `x / 0 = 0`).
Decidability of adjacency is classical throughout.
-/

namespace DiagRamsey

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `S` contains a red clique on exactly `n` vertices. -/
def HasRedClique (G : SimpleGraph V) (S : Finset V) (n : ℕ) : Prop :=
  ∃ T : Finset V, T ⊆ S ∧ G.IsNClique n T

/-- `S` contains a blue clique on exactly `n` vertices (blue edges are the edges of `Gᶜ`). -/
def HasBlueClique (G : SimpleGraph V) (S : Finset V) (n : ℕ) : Prop :=
  ∃ T : Finset V, T ⊆ S ∧ Gᶜ.IsNClique n T

/-- Red density `d_R(X,Y) = e_R(X,Y) / (|X| |Y|)` between finite vertex sets. -/
noncomputable def redDensity (G : SimpleGraph V) (X Y : Finset V) : ℝ :=
  (((X ×ˢ Y).filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ) / ((X.card : ℝ) * (Y.card : ℝ))

/-- Column density `g_y = |{v ∈ X : vy red}| / |X|`. -/
noncomputable def colDensity (G : SimpleGraph V) (X : Finset V) (y : V) : ℝ :=
  ((X.filter (fun v => G.Adj v y)).card : ℝ) / (X.card : ℝ)

/-- Row density `π_v = |{y ∈ Y : vy red}| / |Y|`. -/
noncomputable def rowDensity (G : SimpleGraph V) (v : V) (Y : Finset V) : ℝ :=
  ((Y.filter (fun y => G.Adj v y)).card : ℝ) / (Y.card : ℝ)

/-- The blue neighbourhood `B_v = {u ∈ X : u ≠ v, uv blue}` of `v` inside `X`. -/
noncomputable def blueNbhd (G : SimpleGraph V) (X : Finset V) (v : V) : Finset V :=
  X.filter (fun u => u ≠ v ∧ ¬ G.Adj u v)

/-- The red neighbourhood of `v` inside `S`: `{u ∈ S : uv red}`. For `v ∈ X` the set `redNbhd G X v`
is the red row reservoir `R_v = X \ ({v} ∪ B_v)`, and `redNbhd G Y v` is the retained column set `Y_v`. -/
noncomputable def redNbhd (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V :=
  S.filter (fun u => G.Adj v u)

/-- The neighbourhood of `v` inside `X` in an auxiliary graph `B` (used for an arbitrary "blue graph" on the
rows): `{u ∈ X : B.Adj v u}`. -/
noncomputable def graphNbhd (B : SimpleGraph V) (X : Finset V) (v : V) : Finset V :=
  X.filter (fun u => B.Adj v u)

/-- The degree fraction `q_v = |{u ∈ X : B.Adj v u}| / |X|` in an auxiliary graph `B`. -/
noncomputable def graphFrac (B : SimpleGraph V) (X : Finset V) (v : V) : ℝ :=
  ((graphNbhd B X v).card : ℝ) / (X.card : ℝ)

/-- The nested column-moment norm `H = (E_{y ∈ Y} (g_y - c)_+^s)^(1/s)`, with `g_y = colDensity G X y`. -/
noncomputable def momentNorm (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) : ℝ :=
  ((∑ y ∈ Y, (max (colDensity G X y - c) 0) ^ s) / (Y.card : ℝ)) ^ (1 / s)

/-- The weighted nested potential `Φ_c(X,Y) = |X|^w |Y| H^r`, with `H = momentNorm G X Y c s`.
It is `0` when `X` or `Y` is empty (for `w > 0`). -/
noncomputable def potential (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) : ℝ :=
  (X.card : ℝ) ^ w * (Y.card : ℝ) * (momentNorm G X Y c s) ^ r

/-- `(X,Y)` is separately row- and column-maximal for `Φ_c` at fixed `c, w, r, s`: no nonempty subset of `X`
(with `Y` fixed) and no nonempty subset of `Y` (with `X` fixed) has larger potential. -/
def RowColMaximal (G : SimpleGraph V) (X Y : Finset V) (c w r s : ℝ) : Prop :=
  (∀ X' : Finset V, X' ⊆ X → X'.Nonempty → potential G X' Y c w r s ≤ potential G X Y c w r s) ∧
  (∀ Y' : Finset V, Y' ⊆ Y → Y'.Nonempty → potential G X Y' c w r s ≤ potential G X Y c w r s)

/-- The column `s`-moment sum `∑_{y ∈ Y} (g_y - c)_+^s` (so `momentNorm^s = colMomentSum / |Y|`). -/
noncomputable def colMomentSum (G : SimpleGraph V) (X Y : Finset V) (c s : ℝ) : ℝ :=
  ∑ y ∈ Y, (max (colDensity G X y - c) 0) ^ s

/-- Sharp blue failure of row `i` (inequality (B) of the sharp envelope, division-free form), for an auxiliary
blue graph `B` on the rows, `q_i = graphFrac B X i` and `b_i(y) = colDensity G (graphNbhd B X i) y`:
`∑_y (b_i(y) - c)_+^s < (μ / q_i)^(w β) ∑_y (g_y - c)_+^s`. -/
def SharpBlueFailure (G B : SimpleGraph V) (X Y : Finset V) (c μ w β s : ℝ) (i : V) : Prop :=
  colMomentSum G (graphNbhd B X i) Y c s < (μ / graphFrac B X i) ^ (w * β) * colMomentSum G X Y c s

/-- Sharp shifted-red failure of row `i` (inequality (R) of the sharp envelope with `a_i = 1 - q_i`,
division-free form): with `q = q_i`, `g_y = colDensity G X y`, `b_y = colDensity G (graphNbhd B X i) y`,
`∑_{y ∈ Y, iy red} ((1-q)(g_y - c) - q (b_y - g_y))_+^s < (1-q)^(s - w β) x^β π_i^(1-β) ∑_y (g_y - c)_+^s`. -/
def SharpRedFailure (G B : SimpleGraph V) (X Y : Finset V) (c w β s x : ℝ) (i : V) : Prop :=
  ∑ y ∈ Y.filter (fun y => G.Adj i y),
      (max ((1 - graphFrac B X i) * (colDensity G X y - c) -
        graphFrac B X i * (colDensity G (graphNbhd B X i) y - colDensity G X y)) 0) ^ s <
    (1 - graphFrac B X i) ^ (s - w * β) * x ^ β * (rowDensity G i Y) ^ (1 - β) * colMomentSum G X Y c s

/-- The proper-subset host stopping hypothesis (as `RamseyCurrent.FiniteHostStopping`): for every integer
`a ≥ 1`, every proper vertex subset `Z ⊊ V` with `|Z| ≥ C xhat^(-a) yhat^(-ell)` contains a red `K_a` or a
blue `K_ell`. -/
def HostStopping (G : SimpleGraph V) (C xhat yhat : ℝ) (ell : ℕ) : Prop :=
  ∀ a : ℕ, 0 < a → ∀ Z : Finset V, Z ≠ Finset.univ →
    C * xhat ^ (-(a : ℝ)) * yhat ^ (-(ell : ℝ)) ≤ (Z.card : ℝ) →
    HasRedClique G Z a ∨ HasBlueClique G Z ell

end DiagRamsey
