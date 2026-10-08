import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Density-averaging balanced cut (shared: majority cut for 1.263, density cut for 1.26031).
The permutation-averaging lemmas `MajorityCut.*` were factored out of `Sol_DiagRamsey_majority_colour_balanced_cut`, which imports this module. -/

namespace DiagRamsey

open Finset

namespace MajorityCut

/-- Two-point transitivity of the symmetric group. -/
lemma exists_perm_pair {N : ℕ} {u v u' v' : Fin N} (h : u ≠ v) (h' : u' ≠ v') :
    ∃ τ : Equiv.Perm (Fin N), τ u' = u ∧ τ v' = v := by
  set ρ := Equiv.swap u' u with hρ
  have h1 : ρ u' = u := Equiv.swap_apply_left _ _
  have h2 : ρ v' ≠ u := by
    intro hh
    exact h' (ρ.injective (hh.trans h1.symm)).symm
  refine ⟨Equiv.swap (ρ v') v * ρ, ?_, ?_⟩
  · rw [Equiv.Perm.coe_mul, Function.comp_apply, h1]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) h
  · rw [Equiv.Perm.coe_mul, Function.comp_apply]
    exact Equiv.swap_apply_left _ _

/-- `σ` puts the first vertex of `e` among the first `m` positions and the second one outside. -/
def Separates {N : ℕ} (m : ℕ) (σ : Equiv.Perm (Fin N)) (e : Fin N × Fin N) : Prop :=
  (σ e.1).val < m ∧ ¬ (σ e.2).val < m

instance {N : ℕ} (m : ℕ) (σ : Equiv.Perm (Fin N)) : DecidablePred (Separates m σ) := by
  intro e; unfold Separates; infer_instance

/-- Number of permutations separating `e`. -/
def K {N : ℕ} (m : ℕ) (e : Fin N × Fin N) : ℕ :=
  (univ.filter (fun σ : Equiv.Perm (Fin N) => Separates m σ e)).card

lemma K_const {N : ℕ} (m : ℕ) {e e' : Fin N × Fin N} (he : e.1 ≠ e.2) (he' : e'.1 ≠ e'.2) :
    K m e = K m e' := by
  obtain ⟨τ, h1, h2⟩ := exists_perm_pair he he'
  unfold K
  apply card_equiv (Equiv.mulRight τ)
  intro σ
  simp [Separates, Equiv.Perm.mul_apply, h1, h2]

lemma sum_card_sep {N : ℕ} (m : ℕ) (S : Finset (Fin N × Fin N)) (hS : ∀ e ∈ S, e.1 ≠ e.2)
    (e0 : Fin N × Fin N) (he0 : e0.1 ≠ e0.2) :
    ∑ σ : Equiv.Perm (Fin N), (S.filter (Separates m σ)).card = S.card * K m e0 := by
  simp_rw [card_filter]
  rw [sum_comm]
  rw [sum_congr rfl (g := fun _ => K m e0)]
  · simp
  · intro e he
    rw [← K_const m (hS e he) he0, K, card_filter]

lemma card_sep_offDiag {N : ℕ} (m : ℕ) (hm : m ≤ N) (σ : Equiv.Perm (Fin N)) :
    ((univ.filter (fun e : Fin N × Fin N => e.1 ≠ e.2)).filter (Separates m σ)).card = m * (N - m) := by
  set X : Finset (Fin N) := univ.filter (fun i => (σ i).val < m) with hX
  have hset : (univ.filter (fun e : Fin N × Fin N => e.1 ≠ e.2)).filter (Separates m σ) = X ×ˢ Xᶜ := by
    ext e
    simp only [mem_filter, mem_univ, true_and, Separates, mem_product, mem_compl, hX]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, h2⟩
      intro hh; rw [hh] at h1; exact h2 h1
  have hXc : X.card = m := by
    have : X.card = (univ.filter (fun j : Fin N => j.val < m)).card := by
      apply card_equiv σ
      intro i; simp [hX]
    rw [this]
    have h := Fin.card_filter_val_lt (n := N) (m := m)
    simpa [min_eq_right hm] using h
  rw [hset, card_product, card_compl, Fintype.card_fin, hXc]

/-- Averaging over permutations: a set `R` of off-diagonal ordered pairs with `|R| ≥ q N (N-1)` has a balanced
cut `X, Xᶜ` (both of size at least `N/3`) carrying at least `q |X| |Xᶜ|` pairs of `R`. -/
lemma fin_cut (N : ℕ) (hN : 2 ≤ N) (R : Finset (Fin N × Fin N)) (hR : ∀ e ∈ R, e.1 ≠ e.2) (q : ℝ)
    (hq : q * ((N : ℝ) * ((N : ℝ) - 1)) ≤ (R.card : ℝ)) :
    ∃ X : Finset (Fin N), N ≤ 3 * X.card ∧ N ≤ 3 * Xᶜ.card ∧
      q * ((X.card : ℝ) * (Xᶜ.card : ℝ)) ≤ (((X ×ˢ Xᶜ).filter (fun e => e ∈ R)).card : ℝ) := by
  set D : Finset (Fin N × Fin N) := univ.filter (fun e => e.1 ≠ e.2) with hD
  have hDcard : D.card = N * (N - 1) := by
    have : D = (univ : Finset (Fin N)).offDiag := by
      ext e; simp [hD, mem_offDiag]
    rw [this, offDiag_card, card_univ, Fintype.card_fin, Nat.mul_sub_one]
  set m := N / 2 with hm
  have hmN : m ≤ N := Nat.div_le_self N 2
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set e0 : Fin N × Fin N := (⟨0, by omega⟩, ⟨1, by omega⟩) with he0
  have hDD : ∀ e ∈ D, e.1 ≠ e.2 := by
    intro e he; simp only [hD, mem_filter, mem_univ, true_and] at he; exact he
  have sumR := sum_card_sep m R hR e0 h01
  have sumD := sum_card_sep m D hDD e0 h01
  have hD' : ∀ σ : Equiv.Perm (Fin N), (D.filter (Separates m σ)).card = m * (N - m) := by
    intro σ; rw [hD]; exact card_sep_offDiag m hmN σ
  simp_rw [hD'] at sumD
  -- real averaging
  have hK : (0 : ℝ) ≤ (K m e0 : ℝ) := Nat.cast_nonneg _
  have hNN : ((N * (N - 1) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ N)]; simp
  have hle : ∑ _σ : Equiv.Perm (Fin N), q * ((m * (N - m) : ℕ) : ℝ) ≤
      ∑ σ : Equiv.Perm (Fin N), ((R.filter (Separates m σ)).card : ℝ) := by
    rw [← Finset.mul_sum]
    have h1 : ∑ _σ : Equiv.Perm (Fin N), ((m * (N - m) : ℕ) : ℝ) = (D.card : ℝ) * (K m e0 : ℝ) := by
      rw [← Nat.cast_sum, sumD, Nat.cast_mul]
    have h2 : ∑ σ : Equiv.Perm (Fin N), ((R.filter (Separates m σ)).card : ℝ) = (R.card : ℝ) * (K m e0 : ℝ) := by
      rw [← Nat.cast_sum, sumR, Nat.cast_mul]
    rw [h1, h2, hDcard, hNN, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hq hK
  obtain ⟨σ, -, hσ⟩ := exists_le_of_sum_le (s := (univ : Finset (Equiv.Perm (Fin N))))
    univ_nonempty hle
  set X : Finset (Fin N) := univ.filter (fun i => (σ i).val < m) with hX
  have hXc : X.card = m := by
    have : X.card = (univ.filter (fun j : Fin N => j.val < m)).card := by
      apply card_equiv σ
      intro i; simp [hX]
    rw [this]
    have h := Fin.card_filter_val_lt (n := N) (m := m)
    simpa [min_eq_right hmN] using h
  have hXcc : Xᶜ.card = N - m := by rw [card_compl, Fintype.card_fin, hXc]
  have hcross : (X ×ˢ Xᶜ).filter (fun e : Fin N × Fin N => e ∈ R) = R.filter (Separates m σ) := by
    ext e
    simp only [hX, mem_filter, mem_product, mem_compl, mem_univ, true_and, Separates]
    tauto
  refine ⟨X, ?_, ?_, ?_⟩
  · rw [hXc]; omega
  · rw [hXcc]; omega
  · rw [hXc, hXcc, hcross]
    have : ((m * (N - m) : ℕ) : ℝ) = (m : ℝ) * ((N - m : ℕ) : ℝ) := Nat.cast_mul _ _
    rw [← this]; exact hσ

end MajorityCut

open Classical in
/-- Density-averaging balanced cut inside a vertex set `Z` of any finite graph: if the ordered red pairs of `Z`
number at least `q |Z| (|Z|-1)`, then `Z` splits as `X ⊔ (Z \ X)`, both parts of size at least `|Z|/3`, with at
least `q |X| |Z \ X|` red cross pairs. -/
theorem density_balanced_cut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Z : Finset V)
    (hZ : 2 ≤ Z.card) (q : ℝ)
    (hq : q * ((Z.card : ℝ) * ((Z.card : ℝ) - 1)) ≤
      ((Z.offDiag.filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ)) :
    ∃ X ⊆ Z, Z.card ≤ 3 * X.card ∧ Z.card ≤ 3 * (Z \ X).card ∧
      q * ((X.card : ℝ) * ((Z \ X).card : ℝ)) ≤
        (((X ×ˢ (Z \ X)).filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ) := by
  classical
  set N := Z.card with hNdef
  let eqv : {x // x ∈ Z} ≃ Fin N := Fintype.equivFinOfCardEq (by simp [hNdef])
  let f : Fin N ↪ V := ⟨fun i => (eqv.symm i).1, fun i j h => eqv.symm.injective (Subtype.ext h)⟩
  have hfZ : ∀ i, f i ∈ Z := fun i => (eqv.symm i).2
  have hZmap : Z = univ.map f := by
    ext v
    simp only [mem_map, mem_univ, true_and]
    constructor
    · intro hv; exact ⟨eqv ⟨v, hv⟩, by show ((eqv.symm (eqv ⟨v, hv⟩)) : V) = v; simp⟩
    · rintro ⟨i, rfl⟩; exact hfZ i
  let ff : Fin N × Fin N ↪ V × V := ⟨fun e => (f e.1, f e.2), fun a b h => by
    simp only [Prod.mk.injEq] at h; exact Prod.ext (f.injective h.1) (f.injective h.2)⟩
  set R : Finset (Fin N × Fin N) := univ.filter (fun e => e.1 ≠ e.2 ∧ G.Adj (f e.1) (f e.2)) with hRdef
  have hRmap : R.map ff = Z.offDiag.filter (fun e : V × V => G.Adj e.1 e.2) := by
    ext ⟨u, v⟩
    simp only [hRdef, mem_map, mem_filter, mem_univ, true_and, mem_offDiag, ff, Function.Embedding.coeFn_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨i, j⟩, ⟨hij, hadj⟩, rfl, rfl⟩
      exact ⟨⟨hfZ i, hfZ j, fun h => hij (f.injective h)⟩, hadj⟩
    · rintro ⟨⟨hu, hv, huv⟩, hadj⟩
      rw [hZmap] at hu hv
      obtain ⟨i, -, rfl⟩ := mem_map.mp hu
      obtain ⟨j, -, rfl⟩ := mem_map.mp hv
      exact ⟨(i, j), ⟨fun h => huv (congrArg f h), hadj⟩, rfl, rfl⟩
  have hRcard : (R.card : ℝ) = ((Z.offDiag.filter (fun e : V × V => G.Adj e.1 e.2)).card : ℝ) := by
    rw [← hRmap, card_map]
  have hR : ∀ e ∈ R, e.1 ≠ e.2 := by
    intro e he; simp only [hRdef, mem_filter, mem_univ, true_and] at he; exact he.1
  obtain ⟨X, hX1, hX2, hX3⟩ := MajorityCut.fin_cut N hZ R hR q (by rw [hRcard]; exact hq)
  have hXZ : Z \ X.map f = Xᶜ.map f := by
    ext v
    simp only [mem_sdiff, mem_map, mem_compl]
    constructor
    · rintro ⟨hv, hn⟩
      rw [hZmap] at hv
      obtain ⟨i, -, rfl⟩ := mem_map.mp hv
      exact ⟨i, fun hi => hn ⟨i, hi, rfl⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨hfZ i, ?_⟩
      rintro ⟨j, hj, hji⟩
      exact hi (f.injective hji ▸ hj)
  refine ⟨X.map f, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, -, rfl⟩ := mem_map.mp hv
    exact hfZ i
  · rw [card_map]; exact hX1
  · rw [hXZ, card_map]; exact hX2
  · rw [hXZ, card_map, card_map]
    have hcr : ((X.map f) ×ˢ (Xᶜ.map f)).filter (fun e : V × V => G.Adj e.1 e.2) =
        ((X ×ˢ Xᶜ).filter (fun e => e ∈ R)).map ff := by
      ext ⟨u, v⟩
      simp only [mem_filter, mem_product, mem_map, mem_compl, hRdef, mem_univ, true_and, ff,
        Function.Embedding.coeFn_mk, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, hadj⟩
        exact ⟨(i, j), ⟨⟨hi, hj⟩, fun h => hj ((show i = j from h) ▸ hi), hadj⟩, rfl, rfl⟩
      · rintro ⟨⟨i, j⟩, ⟨⟨hi, hj⟩, -, hadj⟩, rfl, rfl⟩
        exact ⟨⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, hadj⟩
    rw [hcr, card_map]; exact hX3

end DiagRamsey
