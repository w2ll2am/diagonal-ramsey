import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_DiagRamsey_WeightedHost

/-!
# Retained routes (shared combinatorial core)

The finite proof of `SHARP_RETAINED_ROUTE_INTERFACE` (hildegard-of-bingen) in integer-target form:

* `retained_rows`: from a cut `(X₀, Y)` of red density `≥ p`, the rows with at least `π |Y|` red neighbours in
  `Y` form `X ⊆ X₀` with `(p - π)|X₀| ≤ (1 - π)|X|`, and every nonempty `Z ⊆ X` has `d_R(Z, Y) ≥ π`.
* `exists_blue_pivot`: a vertex set of ordered red-pair density `< q` has a vertex whose blue neighbourhood in it
  has more than `(1 - q)(|Z| - 1)` vertices.
* `retained_route_induction`: the induction on the blue target `t` with size thresholds `M t`, base cases
  `t ≤ n₀` (the terminal), leaf calls at density `q t`, and blue pivots.

Author: turibius-of-mogrovejo. No numerical content; every route of every bank is an instance.
-/

namespace DiagRamsey

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_filter_product_eq_sum (G : SimpleGraph V) (X Y : Finset V) :
    ((X ×ˢ Y).filter (fun e : V × V => G.Adj e.1 e.2)).card = ∑ v ∈ X, (Y.filter (fun y => G.Adj v y)).card := by
  rw [card_filter, sum_product]
  apply sum_congr rfl
  intro v _
  rw [card_filter]

/-- Retained rows. -/
lemma retained_rows (G : SimpleGraph V) (X₀ Y : Finset V) (p π : ℝ) (hπ1 : π < 1) (hY : Y.Nonempty)
    (hcross : p * ((X₀.card : ℝ) * (Y.card : ℝ)) ≤
      (((X₀ ×ˢ Y).filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ)) :
    (p - π) * (X₀.card : ℝ) ≤ (1 - π) * ((X₀.filter (fun v => π * (Y.card : ℝ) ≤
        ((Y.filter (fun y => G.Adj v y)).card : ℝ))).card : ℝ) ∧
      ∀ Z ⊆ X₀.filter (fun v => π * (Y.card : ℝ) ≤ ((Y.filter (fun y => G.Adj v y)).card : ℝ)),
        π * ((Z.card : ℝ) * (Y.card : ℝ)) ≤
          (((Z ×ˢ Y).filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ) := by
  set P : V → Prop := fun v => π * (Y.card : ℝ) ≤ ((Y.filter (fun y => G.Adj v y)).card : ℝ) with hP
  set X := X₀.filter P with hX
  set deg : V → ℝ := fun v => ((Y.filter (fun y => G.Adj v y)).card : ℝ) with hdeg
  have hsum : (((X₀ ×ˢ Y).filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ) = ∑ v ∈ X₀, deg v := by
    rw [card_filter_product_eq_sum]; push_cast; rfl
  refine ⟨?_, ?_⟩
  · rw [hsum] at hcross
    have hsplit : ∑ v ∈ X₀, deg v = ∑ v ∈ X, deg v + ∑ v ∈ X₀.filter (fun v => ¬ P v), deg v := by
      rw [hX, sum_filter_add_sum_filter_not]
    have h1 : ∑ v ∈ X, deg v ≤ ∑ v ∈ X, (Y.card : ℝ) := by
      apply sum_le_sum; intro v _
      simp only [hdeg]; exact_mod_cast card_filter_le _ _
    have h2 : ∑ v ∈ X₀.filter (fun v => ¬ P v), deg v ≤ ∑ v ∈ X₀.filter (fun v => ¬ P v), π * (Y.card : ℝ) := by
      apply sum_le_sum; intro v hv
      simp only [mem_filter, hP, not_le] at hv; exact hv.2.le
    rw [sum_const, nsmul_eq_mul] at h1; rw [sum_const, nsmul_eq_mul] at h2
    have hcnt : ((X₀.filter (fun v => ¬ P v)).card : ℝ) = (X₀.card : ℝ) - (X.card : ℝ) := by
      have := card_filter_add_card_filter_not (s := X₀) P
      rw [hX]; rw [← this]; push_cast; ring
    rw [hcnt] at h2
    have hYp : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
    have : (p - π) * (X₀.card : ℝ) * Y.card ≤ (1 - π) * (X.card : ℝ) * Y.card := by nlinarith
    exact le_of_mul_le_mul_right this hYp
  · intro Z hZ
    rw [card_filter_product_eq_sum]; push_cast
    rw [mul_comm (Z.card : ℝ), ← mul_assoc, mul_comm, ← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum; intro v hv
    have := (mem_filter.mp (hZ hv)).2
    linarith

/-- Blue pivot: a set of ordered red-pair density `< q` has a vertex with a large blue neighbourhood. -/
lemma exists_blue_pivot (G : SimpleGraph V) (Z : Finset V) (q : ℝ) (hZ : Z.Nonempty)
    (hlow : ((Z.offDiag.filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ) <
      q * ((Z.card : ℝ) * ((Z.card : ℝ) - 1))) :
    ∃ v ∈ Z, (1 - q) * ((Z.card : ℝ) - 1) < ((Z.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card : ℝ) := by
  have hoff : Z.offDiag.filter (fun e : V × V => G.Adj e.1 e.2) = (Z ×ˢ Z).filter (fun e : V × V => G.Adj e.1 e.2) := by
    ext ⟨u, v⟩
    simp only [mem_filter, mem_offDiag, mem_product]
    constructor
    · rintro ⟨⟨hu, hv, -⟩, h⟩; exact ⟨⟨hu, hv⟩, h⟩
    · rintro ⟨⟨hu, hv⟩, h⟩; exact ⟨⟨hu, hv, G.ne_of_adj h⟩, h⟩
  rw [hoff, card_filter_product_eq_sum] at hlow
  push_cast at hlow
  by_contra hcon
  push_neg at hcon
  have hdeg : ∀ v ∈ Z, ((Z.filter (fun u => G.Adj v u)).card : ℝ) + ((Z.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card : ℝ)
      = (Z.card : ℝ) - 1 := by
    intro v hv
    have h1 : (Z.filter (fun u => G.Adj v u)).card + (Z.filter (fun u => ¬ G.Adj v u)).card = Z.card :=
      card_filter_add_card_filter_not _
    have h2 : Z.filter (fun u => ¬ G.Adj v u) = insert v (Z.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)) := by
      ext u
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hu, h⟩
        by_cases huv : u = v
        · exact Or.inl huv
        · exact Or.inr ⟨hu, huv, h⟩
      · rintro (rfl | ⟨hu, -, h⟩)
        · exact ⟨hv, G.irrefl⟩
        · exact ⟨hu, h⟩
    have h3 : (Z.filter (fun u => ¬ G.Adj v u)).card = (Z.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card + 1 := by
      rw [h2, card_insert_of_notMem]; simp
    have : ((Z.filter (fun u => G.Adj v u)).card : ℝ) + ((Z.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card : ℝ) + 1
        = Z.card := by exact_mod_cast (by omega : (Z.filter (fun u => G.Adj v u)).card +
          (Z.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card + 1 = Z.card)
    linarith
  have hred : ∀ v ∈ Z, q * ((Z.card : ℝ) - 1) ≤ ((Z.filter (fun u => G.Adj v u)).card : ℝ) := by
    intro v hv; have := hdeg v hv; have := hcon v hv; linarith
  have : ∑ v ∈ Z, q * ((Z.card : ℝ) - 1) ≤ ∑ v ∈ Z, ((Z.filter (fun u => G.Adj v u)).card : ℝ) :=
    sum_le_sum hred
  rw [sum_const, nsmul_eq_mul] at this
  linarith

/-- The `(k, ℓ, t)`-good conclusion of a retained route. -/
def RouteGood (G : SimpleGraph V) (Z Y : Finset V) (k ℓ t : ℕ) : Prop :=
  HasRedClique G (Z ∪ Y) k ∨ HasBlueClique G Z t ∨ HasBlueClique G Y ℓ

/-- Retained-route induction on the blue target `t`. -/
theorem retained_route_induction (G : SimpleGraph V) (X Y : Finset V) (k ℓ n₀ T : ℕ) (M q : ℕ → ℝ)
    (hM : ∀ t, 0 < M t)
    (hbase : ∀ t, 0 < t → t ≤ n₀ → ∀ Z ⊆ X, Z.Nonempty → M t ≤ (Z.card : ℝ) → RouteGood G Z Y k ℓ t)
    (hleaf : ∀ t, n₀ < t → t ≤ T → ∀ Z ⊆ X, M t ≤ (Z.card : ℝ) →
      q t * ((Z.card : ℝ) * ((Z.card : ℝ) - 1)) ≤ ((Z.offDiag.filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ) →
      HasRedClique G Z k ∨ HasBlueClique G Z t)
    (hpivot : ∀ t, n₀ < t → t ≤ T → ∀ Z ⊆ X, M t ≤ (Z.card : ℝ) → M (t - 1) ≤ (1 - q t) * ((Z.card : ℝ) - 1)) :
    ∀ t, t ≤ T → ∀ Z ⊆ X, M t ≤ (Z.card : ℝ) → RouteGood G Z Y k ℓ t := by
  intro t
  induction t with
  | zero =>
    intro _ Z _ _
    exact Or.inr (Or.inl ⟨∅, empty_subset _, by simp [SimpleGraph.isNClique_empty]⟩)
  | succ t ih =>
    intro hT Z hZX hZ
    have hZne : Z.Nonempty := by
      rw [← card_pos]; have := hM (t + 1); exact_mod_cast (show (0 : ℝ) < Z.card by linarith)
    by_cases ht : t + 1 ≤ n₀
    · exact hbase (t + 1) (Nat.succ_pos t) ht Z hZX hZne hZ
    push_neg at ht
    by_cases hd : q (t + 1) * ((Z.card : ℝ) * ((Z.card : ℝ) - 1)) ≤
        ((Z.offDiag.filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ)
    · rcases hleaf (t + 1) ht hT Z hZX hZ hd with ⟨S, hS, h⟩ | h
      · exact Or.inl ⟨S, hS.trans subset_union_left, h⟩
      · exact Or.inr (Or.inl h)
    push_neg at hd
    obtain ⟨v, hv, hbig⟩ := exists_blue_pivot G Z (q (t + 1)) hZne hd
    set B := Z.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) with hB
    have hBZ : B ⊆ Z := filter_subset _ _
    have hpv := hpivot (t + 1) ht hT Z hZX hZ
    simp only [Nat.add_sub_cancel] at hpv
    rcases ih (by omega) B (hBZ.trans hZX) (by linarith) with ⟨S, hS, h⟩ | ⟨S, hS, h⟩ | h
    · exact Or.inl ⟨S, hS.trans (union_subset_union hBZ subset_rfl), h⟩
    · refine Or.inr (Or.inl ⟨insert v S, insert_subset hv (hS.trans hBZ), ?_⟩)
      have hvS : v ∉ S := fun hvS => by
        have := (mem_filter.mp (hS hvS)).2.1; exact this rfl
      rw [show t + 1 = t + 1 from rfl]
      refine h.insert ?_
      intro u hu
      have hu' := (mem_filter.mp (hS hu)).2
      rw [SimpleGraph.compl_adj]
      exact ⟨fun h => hu'.1 h.symm, hu'.2⟩
    · exact Or.inr (Or.inr h)

end DiagRamsey
