import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_DiagRamsey_Basic
import Solutions.Sol_DiagRamsey_majority_colour_balanced_cut

/-!
# Diagonal wrapper (shared)

* `arrows_on_finset`: `N → (a,b)` transfers to every `N`-vertex subset of any finite graph.
* `arrows_of_balanced_key`: to prove `N → (k, k)` it suffices to treat a colouring `G'` (either colour renamed red)
  with a balanced cut `X, Xᶜ` (both of size at least `N/3`) of red cross density at least `1/2`.
* `eventually_ramsey_le_of_arrows`: an arrow bound `C e^{z k} ≤ N → N → (k,k)` for all large `k`, with
  `z < z'`, gives `R(k,k) ≤ e^{z' k}` eventually (the gap absorbs `C` and the ceiling).

Factored from `Sol_DiagRamsey_diagonal_exp_1263_conditional` (turibius-of-mogrovejo), for every diagonal bound.
-/

namespace DiagRamsey

/-- `RamseyArrows a b m` transfers to every `m`-vertex subset of any finite graph. -/
lemma arrows_on_finset {V : Type*} [Fintype V] [DecidableEq V] {a b m : ℕ} (hR : RamseyArrows a b m)
    (G : SimpleGraph V) (Z : Finset V) (hZ : Z.card = m) :
    (∃ S ⊆ Z, G.IsNClique a S) ∨ (∃ S ⊆ Z, Gᶜ.IsNClique b S) := by
  classical
  let eqv : {x // x ∈ Z} ≃ Fin m := Fintype.equivFinOfCardEq (by simp [hZ])
  let f : Fin m ↪ V := ⟨fun i => (eqv.symm i).1, fun i j h => eqv.symm.injective (Subtype.ext h)⟩
  have hsub : ∀ S : Finset (Fin m), S.map f ⊆ Z := by
    intro S x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    exact (eqv.symm i).2
  rcases hR (G.comap f) with ⟨S, hS⟩ | ⟨S, hS⟩
  · exact Or.inl ⟨S.map f, hsub S, (hS.map (f := f)).mono (SimpleGraph.map_comap_le f G)⟩
  · refine Or.inr ⟨S.map f, hsub S, ?_⟩
    have hle : (G.comap f)ᶜ ≤ Gᶜ.comap f := by
      intro u v huv
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj] at huv ⊢
      exact ⟨fun h => huv.1 (f.injective h), huv.2⟩
    exact ((hS.mono hle).map (f := f)).mono (SimpleGraph.map_comap_le f Gᶜ)

open Classical in
lemma arrows_of_balanced_key (k N : ℕ) (hN : 2 ≤ N)
    (key : ∀ (G' : SimpleGraph (Fin N)) (X : Finset (Fin N)),
      N ≤ 3 * X.card → N ≤ 3 * Xᶜ.card →
      (1 / 2 : ℝ) * ((X.card : ℝ) * (Xᶜ.card : ℝ)) ≤
        (((X ×ˢ Xᶜ).filter (fun e : Fin N × Fin N => G'.Adj e.1 e.2)).card : ℝ) →
      (∃ S : Finset (Fin N), G'.IsNClique k S) ∨ (∃ S : Finset (Fin N), G'ᶜ.IsNClique k S)) :
    RamseyArrows k k N := by
  intro G
  obtain ⟨b, -, X, hX1, hX2, hcount⟩ := majority_colour_balanced_cut N hN
    (fun u v => decide (G.Adj u v)) (fun u v => by simp [G.adj_comm])
  have hcount' : ∀ G' : SimpleGraph (Fin N), (∀ u ∈ X, ∀ v ∈ Xᶜ, (decide (G.Adj u v) = b ↔ G'.Adj u v)) →
      (1 / 2 : ℝ) * ((X.card : ℝ) * (Xᶜ.card : ℝ)) ≤
        (((X ×ˢ Xᶜ).filter (fun e : Fin N × Fin N => G'.Adj e.1 e.2)).card : ℝ) := by
    intro G' hiff
    have heq : (X ×ˢ Xᶜ).filter (fun e : Fin N × Fin N => decide (G.Adj e.1 e.2) = b) =
        (X ×ˢ Xᶜ).filter (fun e : Fin N × Fin N => G'.Adj e.1 e.2) := by
      apply Finset.filter_congr
      intro e he
      rw [Finset.mem_product] at he
      exact hiff e.1 he.1 e.2 he.2
    rw [heq] at hcount
    have : ((X.card * Xᶜ.card : ℕ) : ℝ) ≤ ((2 * ((X ×ˢ Xᶜ).filter
        (fun e : Fin N × Fin N => G'.Adj e.1 e.2)).card : ℕ) : ℝ) := by exact_mod_cast hcount
    push_cast at this
    linarith
  cases b with
  | true =>
    exact key G X hX1 hX2 (hcount' G (fun u _ v _ => by simp))
  | false =>
    have hne : ∀ u ∈ X, ∀ v ∈ Xᶜ, u ≠ v := by
      intro u hu v hv huv
      rw [Finset.mem_compl] at hv
      exact hv (huv ▸ hu)
    rcases key Gᶜ X hX1 hX2 (hcount' Gᶜ (fun u hu v hv => by
        simp [SimpleGraph.compl_adj, hne u hu v hv])) with ⟨S, hS⟩ | ⟨S, hS⟩
    · exact Or.inr ⟨S, hS⟩
    · exact Or.inl ⟨S, by simpa using hS⟩

lemma eventually_ramsey_le_of_arrows (z z' C : ℝ) (hzz : z < z') (hz0 : 0 ≤ z) (hC : 0 < C) (K : ℕ)
    (harr : ∀ k : ℕ, K ≤ k → ∀ N : ℕ, C * Real.exp (z * k) ≤ (N : ℝ) → RamseyArrows k k N) :
    ∀ᶠ k : ℕ in Filter.atTop, (ramseyNumber k k : ℝ) ≤ Real.exp (z' * k) := by
  set δ : ℝ := z' - z with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨K', hK'⟩ := exists_nat_ge ((C + 1) / δ)
  filter_upwards [Filter.eventually_ge_atTop (max K K')] with k hk
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hkK' : (K' : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_right _ _) hk
  have hkpos : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hezk : 1 ≤ Real.exp (z * k) := Real.one_le_exp (mul_nonneg hz0 hkpos)
  have hfinal : C * Real.exp (z * k) + 1 ≤ Real.exp (z' * k) := by
    have h1 : C + 1 ≤ δ * k := by
      have := (div_le_iff₀ hδ).mp hK'
      nlinarith
    have h2 : δ * k + 1 ≤ Real.exp (δ * k) := by linarith [Real.add_one_le_exp (δ * k)]
    have h3 : Real.exp (z' * k) = Real.exp (z * k) * Real.exp (δ * k) := by
      rw [← Real.exp_add]; congr 1; rw [hδdef]; ring
    rw [h3]
    nlinarith
  set N : ℕ := ⌈C * Real.exp (z * k)⌉₊ with hNdef
  have hR : ramseyNumber k k ≤ N := Nat.sInf_le (harr k hkK N (Nat.le_ceil _))
  calc (ramseyNumber k k : ℝ) ≤ N := by exact_mod_cast hR
    _ ≤ C * Real.exp (z * k) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ Real.exp (z' * k) := hfinal

end DiagRamsey
