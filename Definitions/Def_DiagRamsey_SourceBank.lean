import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_DiagRamsey_Cert

/-!
# Source banks with retained routes (data)

Data for `statements/DiagRamsey_source_bank_minimal_host_routes.md`: sharp controls, profile nodes (leaves and
retained routes) and their outputs. A bank has `m` source pairs `(A i, B i)` and `n` profile nodes; terminal indices
of controls are in `Fin m`, route calls are in `Fin n`.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

/-- A sharp control `γ = (p, μ, w, β, x; σ; ξ, y₀, ν)` with terminal index `σ` in a bank of size `m`. -/
structure SharpControl (m : ℕ) where
  p : ℝ
  μ : ℝ
  w : ℝ
  β : ℝ
  x : ℝ
  σ : Fin m
  ξ : ℝ
  y₀ : ℝ
  ν : ℝ

/-- The hypotheses on a control, given the bank pairs `(A, B)`: `0 < p < 1`, `0 < μ < 1`, `w > 0`, `0 < β < 1`,
`0 < x < min (p, (1 - μ)^w)`, nonempty feasible set, `CERT < 0`, `0 < ξ < min (x, e^{-A σ})`, `0 < y₀ < e^{-B σ}`,
`0 < ν < μ`. -/
def SharpControl.Valid {m : ℕ} (A B : Fin m → ℝ) (γ : SharpControl m) : Prop :=
  0 < γ.p ∧ γ.p < 1 ∧ 0 < γ.μ ∧ γ.μ < 1 ∧ 0 < γ.w ∧ 0 < γ.β ∧ γ.β < 1 ∧
    0 < γ.x ∧ γ.x < γ.p ∧ γ.x < (1 - γ.μ) ^ γ.w ∧
    (certFeasible γ.p γ.μ γ.w γ.β γ.x).Nonempty ∧ cert γ.p γ.μ γ.w γ.β γ.x < 0 ∧
    0 < γ.ξ ∧ γ.ξ < γ.x ∧ γ.ξ < Real.exp (-A γ.σ) ∧
    0 < γ.y₀ ∧ γ.y₀ < Real.exp (-B γ.σ) ∧ 0 < γ.ν ∧ γ.ν < γ.μ

/-- `A_γ = -log ξ`. -/
noncomputable def SharpControl.Aγ {m : ℕ} (γ : SharpControl m) : ℝ := -Real.log γ.ξ

/-- `B_γ = -log y₀`. -/
noncomputable def SharpControl.Bγ {m : ℕ} (γ : SharpControl m) : ℝ := -Real.log γ.y₀

/-- `b_γ = -log ν`. -/
noncomputable def SharpControl.bγ {m : ℕ} (γ : SharpControl m) : ℝ := -Real.log γ.ν

/-- The leaf line `L_γ(r) = (A_γ + r (B_γ + w b_γ)) / (1 + w)`. -/
noncomputable def SharpControl.leafLine {m : ℕ} (γ : SharpControl m) (r : ℝ) : ℝ :=
  (γ.Aγ + r * (γ.Bγ + γ.w * γ.bγ)) / (1 + γ.w)

/-- Retained-route data: output density `p`, terminal control `γ`, knots `u 0 = θ < u 1 < ⋯ < u M = ω`, slope
`d j` and called node `c j` on the cell `J_j = [u j, u (j+1)]`, start value `g₀ = g(θ)` and margin `ε`. -/
structure RouteNode (n m : ℕ) where
  p : ℝ
  γ : SharpControl m
  M : ℕ
  u : Fin (M + 1) → ℝ
  d : Fin M → ℝ
  c : Fin M → Fin n
  g₀ : ℝ
  ε : ℝ

/-- `θ = u 0`. -/
def RouteNode.θ {n m : ℕ} (R : RouteNode n m) : ℝ := R.u 0

/-- `ω = u M`. -/
def RouteNode.ω {n m : ℕ} (R : RouteNode n m) : ℝ := R.u (Fin.last R.M)

/-- The continuous piecewise-affine `g` with `g(θ) = g₀` and slope `d j` on `J_j` (for `s ∈ [θ, ω]`). -/
noncomputable def RouteNode.g {n m : ℕ} (R : RouteNode n m) (s : ℝ) : ℝ :=
  R.g₀ + ∑ j : Fin R.M, R.d j * max 0 (min s (R.u j.succ) - R.u j.castSucc)

/-- The route output
`L_v(r) = ε + max (g r) ((A + r B + w (θ b + g r - g θ)) / (1 + w))` with `A, B, b, w` from the terminal control. -/
noncomputable def RouteNode.out {n m : ℕ} (R : RouteNode n m) (r : ℝ) : ℝ :=
  R.ε + max (R.g r) ((R.γ.Aγ + r * R.γ.Bγ + R.γ.w * (R.θ * R.γ.bγ + R.g r - R.g₀)) / (1 + R.γ.w))

/-- A profile node: a leaf (control `γ`, interval `[α, ω]`) or a retained route. -/
inductive BankNode (n m : ℕ)
  | leaf (γ : SharpControl m) (α ω : ℝ)
  | route (R : RouteNode n m)

/-- The density `p_v` of a node. -/
def BankNode.dens {n m : ℕ} : BankNode n m → ℝ
  | .leaf γ _ _ => γ.p
  | .route R => R.p

/-- The left end of `I_v`. -/
def BankNode.lo {n m : ℕ} : BankNode n m → ℝ
  | .leaf _ α _ => α
  | .route R => R.θ

/-- The right end of `I_v`. -/
def BankNode.hi {n m : ℕ} : BankNode n m → ℝ
  | .leaf _ _ ω => ω
  | .route R => R.ω

/-- The output `L_v`. -/
noncomputable def BankNode.out {n m : ℕ} : BankNode n m → ℝ → ℝ
  | .leaf γ _ _ => γ.leafLine
  | .route R => R.out

/-- The hypotheses on node `v` of the list `nodes`. A leaf: valid control, `0 < α ≤ ω`. A route: valid terminal
control with `p_γ < p_v < 1`, `M ≥ 1`, `θ > 0`, strictly increasing knots, `g₀ > 0`, `ε > 0`, and for every cell `j`:
the called node is earlier in the list, `J_j ⊆ I_{c j}`, `d j > -log (1 - p_{c j})` and `g > L_{c j}` on `J_j`. -/
def BankNode.Valid {n m : ℕ} (A B : Fin m → ℝ) (nodes : Fin n → BankNode n m) (v : Fin n) : Prop :=
  match nodes v with
  | .leaf γ α ω => γ.Valid A B ∧ 0 < α ∧ α ≤ ω
  | .route R =>
      R.γ.Valid A B ∧ R.γ.p < R.p ∧ R.p < 1 ∧ 0 < R.M ∧ 0 < R.θ ∧ StrictMono R.u ∧ 0 < R.g₀ ∧ 0 < R.ε ∧
        ∀ j : Fin R.M, R.c j < v ∧
          (nodes (R.c j)).lo ≤ R.u j.castSucc ∧ R.u j.succ ≤ (nodes (R.c j)).hi ∧
          -Real.log (1 - (nodes (R.c j)).dens) < R.d j ∧
          ∀ s : ℝ, R.u j.castSucc ≤ s → s ≤ R.u j.succ → (nodes (R.c j)).out s < R.g s

end DiagRamsey
