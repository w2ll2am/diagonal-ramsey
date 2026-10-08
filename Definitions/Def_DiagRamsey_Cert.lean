import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
The sharp scalar certificate `CERT(p, μ, w, β, x)` of the sharp row-moment envelope.

For a degree `q ∈ (0, μ]` put
* `A(q) = (1-q)/q · log(p (1-q)^w / x)`,
* `B(q) = w log(μ/q)`,  `U(q) = exp(β B(q))`,
* `M(q) = B(q)` if `A(q) ≤ B(q)`, and otherwise
  `M(q) = p A(q) + (1-p)/β · log((U(q) - p exp(β A(q))) / (1-p))`.

The feasible set `F` consists of the `q ∈ (0, μ]` with `A(q) ≤ B(q)` (non-binding), together with the binding
`q` (`A(q) > B(q)`) at which the logarithm's argument is positive, `p exp(β A(q)) < U(q)`.

`CERT = ∫_0^1 sup_{q ∈ F} [q M(q) + w q (1 + log t)] dt`.

Lean conventions: `cert` is the interval integral of `certIntegrand`, the real `sSup` of the values over `F`.
If `F` is empty that `sSup` is `0` (the mathematical convention would be `-∞`), and a non-integrable integrand has
integral `0`; so `cert … < 0` can only hold when `F` is nonempty and the integrand is integrable.
-/

namespace DiagRamsey

/-- `A(q) = (1-q)/q · log(p (1-q)^w / x)`. -/
noncomputable def certA (p w x q : ℝ) : ℝ :=
  (1 - q) / q * Real.log (p * (1 - q) ^ w / x)

/-- `B(q) = w log(μ/q)`. -/
noncomputable def certB (μ w q : ℝ) : ℝ :=
  w * Real.log (μ / q)

/-- `U(q) = exp(β B(q)) = (μ/q)^(wβ)`. -/
noncomputable def certU (μ w β q : ℝ) : ℝ :=
  Real.exp (β * certB μ w q)

/-- The two-branch envelope `M(q)`. -/
noncomputable def certM (p μ w β x q : ℝ) : ℝ :=
  if certA p w x q ≤ certB μ w q then certB μ w q
  else p * certA p w x q +
    (1 - p) / β * Real.log ((certU μ w β q - p * Real.exp (β * certA p w x q)) / (1 - p))

/-- The feasible degree set `F ⊆ (0, μ]`. -/
def certFeasible (p μ w β x : ℝ) : Set ℝ :=
  {q | 0 < q ∧ q ≤ μ ∧
    (certA p w x q ≤ certB μ w q ∨
      (certB μ w q < certA p w x q ∧ p * Real.exp (β * certA p w x q) < certU μ w β q))}

/-- The pointwise relaxation `sup_{q ∈ F} [q M(q) + w q (1 + log t)]` (real `sSup`). -/
noncomputable def certIntegrand (p μ w β x t : ℝ) : ℝ :=
  sSup ((fun q => q * certM p μ w β x q + w * q * (1 + Real.log t)) '' certFeasible p μ w β x)

/-- `CERT(p, μ, w, β, x) = ∫_0^1 certIntegrand dt`. -/
noncomputable def cert (p μ w β x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, certIntegrand p μ w β x t

end DiagRamsey
