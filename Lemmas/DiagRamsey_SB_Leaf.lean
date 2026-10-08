import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_DiagRamsey_Basic
import Definitions.Def_DiagRamsey_WeightedHost
import Definitions.Def_DiagRamsey_Cert
import Definitions.Def_DiagRamsey_SourceBank
import Solutions.Sol_DiagRamsey_positive_weight_finite_host_closure
import Solutions.Sol_DiagRamsey_weighted_host_lower_bound
import Lemmas.DiagRamsey_balanced_cut
import Lemmas.DiagRamsey_diagonal_wrapper

/-!
# Source banks: the proper-host premise, relative validity, leaf nodes

For `statements/DiagRamsey_source_bank_minimal_host_routes.md` (proof `proofs/…_routes.md` §1–2).

* `Prem A B C V`: on every graph on `V`, every *proper* subset `Z` with `|Z| ≥ C e^{A i a + B i b}` has a red `K_a`
  or a blue `K_b` (all bank indices `i`). Quantifying over all graphs makes it invariant under colour exchange.
* `RelValid A B p lo hi L`: the relative validity of a profile node, with constants `D ≥ 1`, `K` independent of `C`.
* `leaf_relValid`: leaf nodes are relatively valid with `D = 3`.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

/-- The proper-host premise `𝒫_V(C)`. -/
def Prem {m : ℕ} (A B : Fin m → ℝ) (C : ℝ) (V : Type) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) (i : Fin m) (a b : ℕ), 0 < a → 0 < b → ∀ Z : Finset V, Z ≠ Finset.univ →
    C * Real.exp (A i * a + B i * b) ≤ (Z.card : ℝ) → HasRedClique G Z a ∨ HasBlueClique G Z b

/-- Ordered red pairs of `W`. -/
noncomputable def redPairs {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (W : Finset V) : ℕ :=
  (W.offDiag.filter (fun e : V × V => G.Adj e.1 e.2)).card

/-- Relative validity of a profile node `(p, [lo, hi], L)`. -/
def RelValid {m : ℕ} (A B : Fin m → ℝ) (p lo hi : ℝ) (L : ℝ → ℝ) : Prop :=
  ∃ D : ℝ, 1 ≤ D ∧ ∃ K : ℕ, ∀ C : ℝ, 1 ≤ C → ∀ (V : Type) [Fintype V] [DecidableEq V], Prem A B C V →
    ∀ (G : SimpleGraph V) (W : Finset V) (k : ℕ) (r : ℝ), K ≤ k → lo ≤ r → r ≤ hi →
      p * ((W.card : ℝ) * ((W.card : ℝ) - 1)) ≤ (redPairs G W : ℝ) →
      D * C * Real.exp (k * L r) ≤ (W.card : ℝ) → HasRedClique G W k ∨ HasBlueClique G W ⌊r * k⌋₊

/-- The premise gives host stopping for every terminal index. -/
lemma hostStopping_of_prem {m : ℕ} {A B : Fin m → ℝ} {C : ℝ} {V : Type} [Fintype V] [DecidableEq V]
    (hP : Prem A B C V) (G : SimpleGraph V) (σ : Fin m) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    HostStopping G C (Real.exp (-A σ)) (Real.exp (-B σ)) ℓ := by
  intro a ha Z hZ hsize
  refine hP G σ a ℓ ha hℓ Z hZ (le_trans (le_of_eq ?_) hsize)
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    Real.log_exp, mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- The finite-host closure in the form used by leaves and route terminals: a cut `(X, Y)` of red density
`≥ p` inside a host with the premise, with the volume condition in logarithmic form. -/
lemma fh_of_prem {m : ℕ} {A B : Fin m → ℝ} (γ : SharpControl m) (hγ : γ.Valid A B)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i) :
    ∃ L₀ : ℕ, ∀ C : ℝ, 1 ≤ C → ∀ (V : Type) [Fintype V] [DecidableEq V], Prem A B C V →
      ∀ (G : SimpleGraph V) (k ℓ t : ℕ), 0 < k → 0 < t → L₀ ≤ ℓ → 0 < ℓ → ∀ X Y : Finset V,
        X.Nonempty → Y.Nonempty → Disjoint X Y → γ.p ≤ redDensity G X Y →
        (γ.w + 1) * Real.log C + (k * γ.Aγ + ℓ * γ.Bγ + γ.w * t * γ.bγ) ≤
          γ.w * Real.log X.card + Real.log Y.card →
        HasRedClique G (X ∪ Y) k ∨ HasBlueClique G X t ∨ HasBlueClique G Y ℓ := by
  obtain ⟨hp0, hp1, hμ0, hμ1, hw, hβ0, hβ1, hx0, hxp, hxμ, hF, hcert, hξ0, hξx, hξA, hy0, hyB, hν0, hνμ⟩ := hγ
  have hξ1 : γ.ξ < 1 := lt_trans hξA (Real.exp_lt_one_iff.mpr (by linarith [hA γ.σ]))
  have hy1 : γ.y₀ < 1 := lt_trans hyB (Real.exp_lt_one_iff.mpr (by linarith [hB γ.σ]))
  obtain ⟨L₀, hL₀⟩ := positive_weight_finite_host_closure γ.p γ.μ γ.w γ.β γ.x γ.ξ γ.y₀ γ.ν
    (Real.exp (-A γ.σ)) (Real.exp (-B γ.σ)) hp0 hp1 hμ0 hμ1 hw hβ0 hβ1 hx0 hxp hxμ hF hcert hξ0 hξ1 hy0 hy1
    hν0 (by linarith) (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by linarith [hA γ.σ])) (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (by linarith [hB γ.σ])) hξx hξA hyB hνμ
  refine ⟨L₀, fun C hC V _ _ hP G k ℓ t hk ht hL hℓ X Y hX hY hXY hd hvol => ?_⟩
  have hC0 : 0 < C := by linarith
  have hXc : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hYc : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  refine hL₀ C hC ℓ hL V G (hostStopping_of_prem hP G γ.σ ℓ hℓ) k t hk ht X Y hX hY hXY hd ?_
  rw [← Real.exp_log (mul_pos (Real.rpow_pos_of_pos hXc _) hYc), Real.log_mul
    (Real.rpow_pos_of_pos hXc _).ne' hYc.ne', Real.log_rpow hXc]
  rw [Real.rpow_def_of_pos hC0, Real.rpow_def_of_pos hξ0, Real.rpow_def_of_pos hy0,
    Real.rpow_def_of_pos hν0, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [SharpControl.Aγ, SharpControl.Bγ, SharpControl.bγ] at hvol
  nlinarith

/-- Leaf nodes are relatively valid, with `D = 3`. -/
theorem leaf_relValid {m : ℕ} {A B : Fin m → ℝ} (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (γ : SharpControl m) (hγ : γ.Valid A B) (α ω : ℝ) (hα : 0 < α) :
    RelValid A B γ.p α ω γ.leafLine := by
  obtain ⟨L₀, hL₀⟩ := fh_of_prem γ hγ hA hB
  have hγ' := hγ
  obtain ⟨hp0, hp1, hμ0, hμ1, hw, -, -, hx0, hxp, -, -, -, hξ0, hξx, hξA, hy0, hyB, hν0, hνμ⟩ := hγ'
  have hAγ : 0 < γ.Aγ := by
    have := Real.log_lt_log hξ0 hξA; rw [Real.log_exp] at this
    simp only [SharpControl.Aγ]; linarith [hA γ.σ]
  have hBγ : 0 < γ.Bγ := by
    have := Real.log_lt_log hy0 hyB; rw [Real.log_exp] at this
    simp only [SharpControl.Bγ]; linarith [hB γ.σ]
  have hbγ : 0 < γ.bγ := by
    simp only [SharpControl.bγ]; linarith [Real.log_neg hν0 (by linarith : γ.ν < 1)]
  -- K with ⌊α k⌋ ≥ max L₀ 1
  obtain ⟨K, hK⟩ := exists_nat_ge (((L₀ : ℝ) + 1) / α)
  refine ⟨3, by norm_num, K, fun C hC V _ _ hP G W k r hk hr1 _ hdens hsize => ?_⟩
  have hC0 : 0 < C := by linarith
  have hkα : (L₀ : ℝ) + 1 ≤ α * k := by
    have h1 : ((L₀ : ℝ) + 1) / α ≤ k := hK.trans (by exact_mod_cast hk)
    rw [div_le_iff₀ hα] at h1; linarith
  have hr0 : 0 < r := lt_of_lt_of_le hα hr1
  set ℓ := ⌊r * k⌋₊ with hℓdef
  have hℓ1 : (L₀ : ℝ) + 1 ≤ r * k := by nlinarith [show (0 : ℝ) ≤ k by positivity]
  have hℓL : L₀ ≤ ℓ := by
    rw [hℓdef]; apply Nat.le_floor; push_cast; linarith
  have hℓ0 : 0 < ℓ := by
    rw [hℓdef]; apply Nat.floor_pos.mpr; linarith
  have hℓr : (ℓ : ℝ) ≤ r * k := Nat.floor_le (by positivity)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hkα; linarith [show (0 : ℝ) ≤ L₀ by positivity]
    · exact h
  -- the cut
  set E : ℝ := k * γ.leafLine r with hE
  have hE0 : 0 ≤ E := by
    rw [hE, SharpControl.leafLine]; positivity
  have hW3 : (3 : ℝ) ≤ W.card := by
    have : 1 ≤ C * Real.exp E := one_le_mul_of_one_le_of_one_le hC (Real.one_le_exp hE0)
    nlinarith
  have hW2 : 2 ≤ W.card := by exact_mod_cast (show (2 : ℝ) ≤ W.card by linarith)
  obtain ⟨X, hXW, hX3, hY3, hcross⟩ := density_balanced_cut G W hW2 γ.p (by unfold redPairs at hdens; exact hdens)
  set Y := W \ X with hYdef
  have hXne : X.Nonempty := by rw [← Finset.card_pos]; omega
  have hYne : Y.Nonempty := by rw [← Finset.card_pos]; omega
  have hXc : (0 : ℝ) < X.card := by exact_mod_cast hXne.card_pos
  have hYc : (0 : ℝ) < Y.card := by exact_mod_cast hYne.card_pos
  have hdens' : γ.p ≤ redDensity G X Y := by
    unfold redDensity; rw [le_div_iff₀ (mul_pos hXc hYc)]; exact hcross
  have hX : C * Real.exp E ≤ X.card := by
    have : (W.card : ℝ) ≤ 3 * X.card := by exact_mod_cast hX3
    linarith
  have hY : C * Real.exp E ≤ Y.card := by
    have : (W.card : ℝ) ≤ 3 * Y.card := by exact_mod_cast hY3
    linarith
  have hlX : Real.log C + E ≤ Real.log X.card := by
    rw [← Real.log_exp E, ← Real.log_mul hC0.ne' (Real.exp_pos _).ne']
    exact Real.log_le_log (by positivity) hX
  have hlY : Real.log C + E ≤ Real.log Y.card := by
    rw [← Real.log_exp E, ← Real.log_mul hC0.ne' (Real.exp_pos _).ne']
    exact Real.log_le_log (by positivity) hY
  have hvol : (γ.w + 1) * Real.log C + (k * γ.Aγ + ℓ * γ.Bγ + γ.w * ℓ * γ.bγ) ≤
      γ.w * Real.log X.card + Real.log Y.card := by
    have hEq : (1 + γ.w) * E = k * γ.Aγ + r * k * (γ.Bγ + γ.w * γ.bγ) := by
      rw [hE, SharpControl.leafLine]; field_simp
    have h1 : (ℓ : ℝ) * (γ.Bγ + γ.w * γ.bγ) ≤ r * k * (γ.Bγ + γ.w * γ.bγ) :=
      mul_le_mul_of_nonneg_right hℓr (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hlX hw.le]
  rcases hL₀ C hC V hP G k ℓ ℓ hk0 hℓ0 hℓL hℓ0 X Y hXne hYne Finset.disjoint_sdiff hdens' hvol with
    ⟨S, hS, h⟩ | ⟨S, hS, h⟩ | ⟨S, hS, h⟩
  · exact Or.inl ⟨S, hS.trans (Finset.union_subset hXW Finset.sdiff_subset), h⟩
  · exact Or.inr ⟨S, hS.trans hXW, h⟩
  · exact Or.inr ⟨S, hS.trans Finset.sdiff_subset, h⟩

end DiagRamsey
