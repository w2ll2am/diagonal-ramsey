import Lemmas.DiagRamsey_closure_of_envelope
import Lemmas.DiagRamsey_sharp_envelope

/-! The closure theorem: `positive_weight_finite_host_closure_of_envelope` applied to the verified sharp envelope
`positive_weight_sharp_envelope_proof` (`Lemmas/DiagRamsey_sharp_envelope.lean`). Axioms:
`[propext, Classical.choice, Quot.sound]`. -/

namespace DiagRamsey

theorem positive_weight_finite_host_closure (p μ w β x ξ y₀ ν xhat yhat : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx0 : 0 < x) (hxp : x < p) (hxμ : x < (1 - μ) ^ w)
    (hF : (certFeasible p μ w β x).Nonempty) (hcert : cert p μ w β x < 0)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hy0 : 0 < y₀) (hy1 : y₀ < 1) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hxh0 : 0 < xhat) (hxh1 : xhat < 1) (hyh0 : 0 < yhat) (hyh1 : yhat < 1)
    (hξx : ξ < x) (hξxh : ξ < xhat) (hyy : y₀ < yhat) (hνμ : ν < μ) :
    ∃ L₀ : ℕ, ∀ C : ℝ, 1 ≤ C → ∀ ℓ : ℕ, L₀ ≤ ℓ →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        HostStopping G C xhat yhat ℓ →
        ∀ k t : ℕ, 0 < k → 0 < t → ∀ X Y : Finset V,
          X.Nonempty → Y.Nonempty → Disjoint X Y →
          p ≤ redDensity G X Y →
          C ^ (w + 1) * ξ ^ (-(k : ℝ)) * y₀ ^ (-(ℓ : ℝ)) * ν ^ (-(w * (t : ℝ))) ≤
            (X.card : ℝ) ^ w * (Y.card : ℝ) →
          HasRedClique G (X ∪ Y) k ∨ HasBlueClique G X t ∨ HasBlueClique G Y ℓ :=
  positive_weight_finite_host_closure_of_envelope p μ w β x ξ y₀ ν xhat yhat hp0 hp1 hμ0 hμ1 hw hβ0 hβ1 hx0 hxp hxμ hF hcert hξ0 hξ1 hy0 hy1 hν0 hν1 hxh0 hxh1 hyh0 hyh1 hξx hξxh hyy hνμ positive_weight_sharp_envelope_proof

end DiagRamsey

open DiagRamsey in
theorem solution_positive_weight_finite_host_closure (p μ w β x ξ y₀ ν xhat yhat : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hw : 0 < w) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hx0 : 0 < x) (hxp : x < p) (hxμ : x < (1 - μ) ^ w)
    (hF : (certFeasible p μ w β x).Nonempty) (hcert : cert p μ w β x < 0)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hy0 : 0 < y₀) (hy1 : y₀ < 1) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hxh0 : 0 < xhat) (hxh1 : xhat < 1) (hyh0 : 0 < yhat) (hyh1 : yhat < 1)
    (hξx : ξ < x) (hξxh : ξ < xhat) (hyy : y₀ < yhat) (hνμ : ν < μ) :
    ∃ L₀ : ℕ, ∀ C : ℝ, 1 ≤ C → ∀ ℓ : ℕ, L₀ ≤ ℓ →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        HostStopping G C xhat yhat ℓ →
        ∀ k t : ℕ, 0 < k → 0 < t → ∀ X Y : Finset V,
          X.Nonempty → Y.Nonempty → Disjoint X Y →
          p ≤ redDensity G X Y →
          C ^ (w + 1) * ξ ^ (-(k : ℝ)) * y₀ ^ (-(ℓ : ℝ)) * ν ^ (-(w * (t : ℝ))) ≤
            (X.card : ℝ) ^ w * (Y.card : ℝ) →
          HasRedClique G (X ∪ Y) k ∨ HasBlueClique G X t ∨ HasBlueClique G Y ℓ :=
  DiagRamsey.positive_weight_finite_host_closure p μ w β x ξ y₀ ν xhat yhat hp0 hp1 hμ0 hμ1 hw hβ0 hβ1 hx0 hxp hxμ hF hcert hξ0 hξ1 hy0 hy1 hν0 hν1 hxh0 hxh1 hyh0 hyh1 hξx hξxh hyy hνμ
