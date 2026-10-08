import Lemmas.DiagRamsey_JB_Transfer
import Lemmas.DiagRamsey_SB_Route
import Lemmas.DiagRamsey_SB_Bank
import Lemmas.DiagRamsey_closure_basic

/-!
# Joint banks: assertions on sub-hosts, the minimal-host premise, grounding, RAW pieces

`proofs/DiagRamsey_joint_integer_target_bank.md` §0 (Lemmas 0–2) and §1 (grounding).

* `AssertOn P C G W`, `SourceOn`, `AllOn`: the bank assertions on a sub-host `W ⊆ V` (ordered-pair density).
* `JPrem C V`: every bank assertion holds on every proper sub-host, for every graph on `V`. Since all graphs are
  quantified, this covers both colour namings. It gives the source premise `Prem` and validity of every child on
  proper sub-hosts with `D = 1`.
* `allOn_of_induced`: assertions on the host `↥Z` transfer to the sub-host `Z ⊆ V`.
* `ground`: for `k < K`, `C ≥ C_prof` gives the assertion at every ratio `b/k ≤ M`.
* `raw_leaf_ok`, `raw_route_ok`, `raw_compl_ok`: the RAW pieces on the whole host (Lemmas 1–2).

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

section defs
variable {V : Type} [Fintype V] [DecidableEq V]

/-- `(ASSERT_P)` on the sub-host `W`. -/
def AssertOn (P : BankProfile) (C : ℝ) (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ k b : ℕ, 0 < k → 0 < b → P.lo ≤ (b : ℝ) / k → (b : ℝ) / k ≤ P.hi →
    P.p * ((W.card : ℝ) * ((W.card : ℝ) - 1)) ≤ (redPairs G W : ℝ) →
    C * Real.exp (k * P.L ((b : ℝ) / k)) ≤ (W.card : ℝ) → HasRedClique G W k ∨ HasBlueClique G W b

/-- `(SOURCE)` on the sub-host `W`. -/
def SourceOn (A B C : ℝ) (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ k b : ℕ, 0 < k → 0 < b → C * Real.exp (A * k + B * b) ≤ (W.card : ℝ) →
    HasRedClique G W k ∨ HasBlueClique G W b

/-- All bank assertions on `W`. -/
def AllOn {m nR nC : ℕ} (raw : Fin nR → BankProfile) (closed : Fin nC → BankProfile) (A B : Fin m → ℝ)
    (C : ℝ) (G : SimpleGraph V) (W : Finset V) : Prop :=
  (∀ i, AssertOn (raw i) C G W) ∧ (∀ i, AssertOn (closed i) C G W) ∧ ∀ h, SourceOn (A h) (B h) C G W

end defs

/-- The minimal-host premise `𝒫_V(C)`. -/
def JPrem {m nR nC : ℕ} (raw : Fin nR → BankProfile) (closed : Fin nC → BankProfile) (A B : Fin m → ℝ)
    (C : ℝ) (V : Type) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) (Z : Finset V), Z ≠ Finset.univ → AllOn raw closed A B C G Z

section lemmas
variable {m nR nC : ℕ} {raw : Fin nR → BankProfile} {closed : Fin nC → BankProfile} {A B : Fin m → ℝ}

lemma prem_of_jprem {C : ℝ} {V : Type} [Fintype V] [DecidableEq V] (h : JPrem raw closed A B C V) :
    Prem A B C V :=
  fun G i a b ha hb Z hZ hsz => (h G Z hZ).2.2 i a b ha hb hsz

lemma assertOn_child {C : ℝ} {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {Z : Finset V}
    (h : AllOn raw closed A B C G Z) (c : Fin nR ⊕ Fin nC) : AssertOn (Sum.elim raw closed c) C G Z := by
  rcases c with i | i
  · exact h.1 i
  · exact h.2.1 i

lemma allOn_of_induced {C : ℝ} {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Z : Finset V)
    (h : AllOn raw closed A B C (induced G Z) Finset.univ) : AllOn raw closed A B C G Z := by
  have hc := card_univ_coe Z
  have hr := redPairs_induced G Z
  have tr : ∀ (P : BankProfile), AssertOn P C (induced G Z) Finset.univ → AssertOn P C G Z := by
    intro P hP k b hk hb h1 h2 hd hs
    rcases hP k b hk hb h1 h2 (by rw [hc, hr]; exact hd) (by rw [hc]; exact hs) with h | h
    · exact Or.inl (red_of_induced h)
    · exact Or.inr (blue_of_induced h)
  refine ⟨fun i => tr _ (h.1 i), fun i => tr _ (h.2.1 i), fun j k b hk hb hs => ?_⟩
  rcases h.2.2 j k b hk hb (by rw [hc]; exact hs) with h | h
  · exact Or.inl (red_of_induced h)
  · exact Or.inr (blue_of_induced h)

end lemmas

/-- Erdős–Szekeres in the form used for grounding. -/
lemma arrows_choose' (k b : ℕ) (hk : 0 < k) (hb : 0 < b) :
    RamseyArrows k b ((k - 1 + (b - 1)).choose (k - 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have := ClosureEnv.arrows_choose (a + c) a c rfl
  simpa using this

/-- A clique in `univ` from an arrowing number below `|V|`. -/
lemma clique_of_arrows {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k b n : ℕ}
    (hR : RamseyArrows k b n) (hn : (n : ℝ) ≤ (Finset.univ : Finset V).card) :
    HasRedClique G Finset.univ k ∨ HasBlueClique G Finset.univ b := by
  have hR' := ClosureEnv.arrows_mono hR (show n ≤ (Finset.univ : Finset V).card by exact_mod_cast hn)
  rcases arrows_on_finset hR' G Finset.univ rfl with ⟨S, hS, h⟩ | ⟨S, hS, h⟩
  · exact Or.inl ⟨S, hS, h⟩
  · exact Or.inr ⟨S, hS, h⟩

/-- The grounding constant `C_prof(K, BB) = 1 + ∑_{k < K} ∑_{b < BB} R-bound(k, b)`. -/
noncomputable def cProf (K BB : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range K, ∑ b ∈ Finset.range BB, (((k - 1 + (b - 1)).choose (k - 1) : ℕ) : ℝ)

lemma cProf_ge (K BB : ℕ) {k b : ℕ} (hk : k < K) (hb : b < BB) :
    (((k - 1 + (b - 1)).choose (k - 1) : ℕ) : ℝ) ≤ cProf K BB := by
  unfold cProf
  have h1 := Finset.single_le_sum (f := fun b' => (((k - 1 + (b' - 1)).choose (k - 1) : ℕ) : ℝ))
    (fun _ _ => by positivity) (Finset.mem_range.mpr hb)
  have h2 := Finset.single_le_sum
    (f := fun k' => ∑ b' ∈ Finset.range BB, (((k' - 1 + (b' - 1)).choose (k' - 1) : ℕ) : ℝ))
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_range.mpr hk)
  linarith

lemma cProf_one (K BB : ℕ) : 1 ≤ cProf K BB := by
  unfold cProf
  have : 0 ≤ ∑ k ∈ Finset.range K, ∑ b ∈ Finset.range BB, (((k - 1 + (b - 1)).choose (k - 1) : ℕ) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  linarith

/-- Grounding: small `k` with `b ≤ M k`, any density. -/
lemma ground {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {K BB : ℕ} {C : ℝ}
    (hC : cProf K BB ≤ C) {k b : ℕ} (hk0 : 0 < k) (hb0 : 0 < b) (hk : k < K) (hb : b < BB) {x : ℝ} (hx : 0 ≤ x)
    (hsize : C * Real.exp x ≤ (Finset.univ : Finset V).card) :
    HasRedClique G Finset.univ k ∨ HasBlueClique G Finset.univ b := by
  refine clique_of_arrows G (arrows_choose' k b hk0 hb0) ?_
  have h1 := cProf_ge K BB hk hb
  have h2 : C ≤ C * Real.exp x := le_mul_of_one_le_right (by linarith [cProf_one K BB]) (Real.one_le_exp hx)
  linarith

end DiagRamsey
