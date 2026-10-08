import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Definitions.Def_DiagRamsey_Basic
import Definitions.Def_DiagRamsey_LuWangSource
import Definitions.Def_DiagRamsey_SourceBank

/-!
# Integer-target RAW / CLOSED / SOURCE banks (data)

Data for `statements/DiagRamsey_joint_integer_target_bank.md`. A host is a graph `G` on `Fin N` (red edges = edges of
`G`, blue = edges of `Gᶜ`). Children of RAW pieces range over `ι = Fin nR ⊕ Fin nC` (RAW or CLOSED profiles);
donors of CLOSED pieces are RAW (`Fin nR`). Controls and their leaf lines are those of `Def_DiagRamsey_SourceBank`.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Classical in
/-- The red edge density `|E(G)| / C(N, 2)` of a host on `Fin N` (real division, so `0` when `N < 2`). -/
noncomputable def redEdgeDensity {N : ℕ} (G : SimpleGraph (Fin N)) : ℝ :=
  (G.edgeFinset.card : ℝ) / (N.choose 2 : ℝ)

/-- `G ⊇ (k, b)`: a red `K_k` or a blue `K_b`. -/
def HostContains {N : ℕ} (G : SimpleGraph (Fin N)) (k b : ℕ) : Prop :=
  (∃ S : Finset (Fin N), G.IsNClique k S) ∨ (∃ S : Finset (Fin N), Gᶜ.IsNClique b S)

/-- A profile `(p_P, I_P = [lo, hi], L_P)`. -/
structure BankProfile where
  p : ℝ
  lo : ℝ
  hi : ℝ
  L : ℝ → ℝ

/-- `0 < p < 1`, `0 < lo ≤ hi`, and `L > 0` on `I_P`. -/
def BankProfile.Valid (P : BankProfile) : Prop :=
  0 < P.p ∧ P.p < 1 ∧ 0 < P.lo ∧ P.lo ≤ P.hi ∧ ∀ r : ℝ, P.lo ≤ r → r ≤ P.hi → 0 < P.L r

/-- The assertion `(ASSERT_P)` with constant `C`: for all positive integers `k, b` with `b/k ∈ I_P` and every host
`G` on `Fin N`, `d_R(G) ≥ p_P` and `N ≥ C e^{k L_P(b/k)}` imply `G ⊇ (k, b)`. -/
def BankProfile.Assert (P : BankProfile) (C : ℝ) : Prop :=
  ∀ k b : ℕ, 0 < k → 0 < b → P.lo ≤ (b : ℝ) / k → (b : ℝ) / k ≤ P.hi →
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)), P.p ≤ redEdgeDensity G →
      C * Real.exp (k * P.L ((b : ℝ) / k)) ≤ (N : ℝ) → HostContains G k b

/-- Retained-route data of a RAW piece: terminal control `γ`, knots `u 0 = θ < ⋯ < u M = ω`, slopes `d j` and
children `c j` on the cells `[u j, u (j+1)]`, start value `g₀`. -/
structure RoutePiece (ι : Type) (m : ℕ) where
  γ : SharpControl m
  M : ℕ
  u : Fin (M + 1) → ℝ
  d : Fin M → ℝ
  c : Fin M → ι
  g₀ : ℝ

/-- `θ = u 0`. -/
def RoutePiece.θ {ι : Type} {m : ℕ} (R : RoutePiece ι m) : ℝ := R.u 0

/-- `ω = u M`. -/
def RoutePiece.ω {ι : Type} {m : ℕ} (R : RoutePiece ι m) : ℝ := R.u (Fin.last R.M)

/-- The continuous piecewise-affine `g` with `g(θ) = g₀` and slope `d j` on cell `j` (for `s ∈ [θ, ω]`). -/
noncomputable def RoutePiece.g {ι : Type} {m : ℕ} (R : RoutePiece ι m) (s : ℝ) : ℝ :=
  R.g₀ + ∑ j : Fin R.M, R.d j * max 0 (min s (R.u j.succ) - R.u j.castSucc)

/-- The route value `max (g r) ((A + r B + w (θ b + g r - g₀)) / (1 + w))`, with `A, B, b, w` from `γ`. -/
noncomputable def RoutePiece.value {ι : Type} {m : ℕ} (R : RoutePiece ι m) (r : ℝ) : ℝ :=
  max (R.g r) ((R.γ.Aγ + r * R.γ.Bγ + R.γ.w * (R.θ * R.γ.bγ + R.g r - R.g₀)) / (1 + R.γ.w))

/-- A RAW piece: a leaf, a retained route, or a proper complementary pair of children. -/
inductive RawPiece (ι : Type) (m : ℕ)
  | leaf (γ : SharpControl m)
  | route (R : RoutePiece ι m)
  | compl (PR PB : ι)

/-- The hypotheses on a RAW piece on `J = [lo, hi]` with margin `ε` of the RAW profile `P`; `prof` gives the
children's profiles. -/
def RawPiece.Valid {ι : Type} {m : ℕ} (A B : Fin m → ℝ) (prof : ι → BankProfile) (P : BankProfile)
    (lo hi ε : ℝ) : RawPiece ι m → Prop
  | .leaf γ => γ.Valid A B ∧ γ.p = P.p ∧ ∀ r : ℝ, lo ≤ r → r ≤ hi → ε + γ.leafLine r ≤ P.L r
  | .route R =>
      R.γ.Valid A B ∧ R.γ.p < P.p ∧ 0 < R.M ∧ 0 < R.θ ∧ StrictMono R.u ∧ 0 < R.g₀ ∧ R.θ ≤ lo ∧ hi ≤ R.ω ∧
        (∀ j : Fin R.M, (prof (R.c j)).lo ≤ R.u j.castSucc ∧ R.u j.succ ≤ (prof (R.c j)).hi ∧
          -Real.log (1 - (prof (R.c j)).p) < R.d j ∧
          ∀ s : ℝ, R.u j.castSucc ≤ s → s ≤ R.u j.succ → (prof (R.c j)).L s < R.g s) ∧
        ∀ r : ℝ, lo ≤ r → r ≤ hi → ε + R.value r ≤ P.L r
  | .compl PR PB =>
      (prof PR).p + (prof PB).p ≤ 1 ∧ (prof PR).lo ≤ lo ∧ hi ≤ (prof PR).hi ∧
        ∀ r : ℝ, lo ≤ r → r ≤ hi → (prof PB).lo ≤ 1 / r ∧ 1 / r ≤ (prof PB).hi ∧
          ε * (1 + r) + max ((prof PR).L r) (r * (prof PB).L (1 / r)) ≤ P.L r

/-- A CLOSED piece; donors are RAW profiles (`Fin nR`). -/
inductive ClosedPiece (nR : ℕ)
  | rawDensity (R : Fin nR)
  | complRaw (R S : Fin nR)
  | ratioMono (R : Fin nR) (c c' : ℝ)
  | complRatioMono (R S : Fin nR) (c c' : ℝ)

/-- The hypotheses on a CLOSED piece on `J = [lo, hi]` of the CLOSED profile `Q` (all non-strict). -/
def ClosedPiece.Valid {nR : ℕ} (raw : Fin nR → BankProfile) (Q : BankProfile) (lo hi : ℝ) :
    ClosedPiece nR → Prop
  | .rawDensity R =>
      (raw R).p ≤ Q.p ∧ (raw R).lo ≤ lo ∧ hi ≤ (raw R).hi ∧ ∀ r : ℝ, lo ≤ r → r ≤ hi → (raw R).L r ≤ Q.L r
  | .complRaw R S =>
      (raw R).p + (raw S).p ≤ 1 ∧ (raw R).lo ≤ lo ∧ hi ≤ (raw R).hi ∧
        ∀ r : ℝ, lo ≤ r → r ≤ hi → (raw S).lo ≤ 1 / r ∧ 1 / r ≤ (raw S).hi ∧
          max ((raw R).L r) (r * (raw S).L (1 / r)) ≤ Q.L r
  | .ratioMono R c c' =>
      (raw R).p ≤ Q.p ∧ hi ≤ c ∧ c < c' ∧ (raw R).lo ≤ c ∧ c' ≤ (raw R).hi ∧
        ∀ r : ℝ, lo ≤ r → r ≤ hi → ∀ r' : ℝ, c ≤ r' → r' ≤ c' → (raw R).L r' ≤ Q.L r
  | .complRatioMono R S c c' =>
      (raw R).p + (raw S).p ≤ 1 ∧ hi ≤ c ∧ c < c' ∧ (raw R).lo ≤ c ∧ c' ≤ (raw R).hi ∧
        (∀ r' : ℝ, c ≤ r' → r' ≤ c' → (raw S).lo ≤ 1 / r' ∧ 1 / r' ≤ (raw S).hi) ∧
        ∀ r : ℝ, lo ≤ r → r ≤ hi → ∀ r' : ℝ, c ≤ r' → r' ≤ c' →
          max ((raw R).L r') (r' * (raw S).L (1 / r')) ≤ Q.L r

/-- A SOURCE cell: grounded (original-source tangent cell) or a pair of profiles. -/
inductive SourceCell (ι : Type)
  | grounded
  | pair (PR PB : ι)

/-- The hypotheses on a SOURCE cell `J = [lo, hi]` of the bank pair `(A, B)` with margin `η`. -/
def SourceCell.Valid {ι : Type} (prof : ι → BankProfile) (A B η lo hi : ℝ) : SourceCell ι → Prop
  | .grounded =>
      ∀ t : ℝ, 0 < t → lo ≤ t → t ≤ hi → symmetricProfile luWangSource 1 t ≤ A + B * t - η * (1 + t)
  | .pair PR PB =>
      (prof PR).p + (prof PB).p ≤ 1 ∧ (prof PR).lo ≤ lo ∧ hi ≤ (prof PR).hi ∧
        ∀ t : ℝ, lo ≤ t → t ≤ hi → (prof PB).lo ≤ 1 / t ∧ 1 / t ≤ (prof PB).hi ∧
          max ((prof PR).L t) (t * (prof PB).L (1 / t)) ≤ A + B * t - η * (1 + t)

end DiagRamsey
