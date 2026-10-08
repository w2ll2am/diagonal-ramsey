import Lemmas.DiagRamsey_SB_Route
import Lemmas.DiagRamsey_closure_basic
import Definitions.Def_DiagRamsey_LuWangSource

/-!
# Source banks: every node is relatively valid; helpers for the host-order induction

* `BankNode.dens_pos`, `dens_lt_one`: node densities lie in `(0, 1)`.
* `nodes_relValid`: by induction along the node list (calls go to earlier nodes), every node is relatively valid
  (`leaf_relValid`, `route_relValid`).
* `redPairs_add_compl`: red and blue ordered pairs of `W` add up to `|W| (|W| - 1)`.
* `symmetricProfile_hom`: `F̂(a, b) = a F̂(1, b/a)` for `a > 0`.
* `pow_le_exp`: `x^K ≤ K! c^{-K} e^{c x}`, for the Erdős–Szekeres small cases.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

section nodes
variable {m n : ℕ} {A B : Fin m → ℝ} {nodes : Fin n → BankNode n m}

lemma BankNode.dens_mem (hnodes : ∀ v, BankNode.Valid A B nodes v) (v : Fin n) :
    0 < (nodes v).dens ∧ (nodes v).dens < 1 := by
  have h := hnodes v
  unfold BankNode.Valid at h
  rcases hv : nodes v with ⟨γ, α, ω⟩ | R
  · rw [hv] at h
    exact ⟨h.1.1, h.1.2.1⟩
  · rw [hv] at h
    exact ⟨lt_trans h.1.1 h.2.1, h.2.2.1⟩

theorem nodes_relValid (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (hnodes : ∀ v, BankNode.Valid A B nodes v) :
    ∀ v, RelValid A B (nodes v).dens (nodes v).lo (nodes v).hi (nodes v).out := by
  suffices H : ∀ N : ℕ, ∀ v : Fin n, v.val < N →
      RelValid A B (nodes v).dens (nodes v).lo (nodes v).hi (nodes v).out from
    fun v => H (v.val + 1) v (Nat.lt_succ_self _)
  intro N
  induction N with
  | zero => intro v hv; omega
  | succ N ih =>
    intro v hvN
    have h := hnodes v
    unfold BankNode.Valid at h
    rcases hv : nodes v with ⟨γ, α, ω⟩ | R
    · rw [hv] at h
      exact leaf_relValid hA hB γ h.1 α ω h.2.1
    · rw [hv] at h
      obtain ⟨hγ, hpγ, hp1, hM, hθ, hmono, hg0, hε, hcells⟩ := h
      refine route_relValid hA hB R hγ hpγ hp1 hM hθ hmono hg0 hε
        (fun j => (nodes (R.c j)).dens) (fun j => (nodes (R.c j)).lo) (fun j => (nodes (R.c j)).hi)
        (fun j => (nodes (R.c j)).out) (fun j => ih (R.c j) ?_) (fun j => (hcells j).2.1)
        (fun j => (hcells j).2.2.1) (fun j => (BankNode.dens_mem hnodes (R.c j)).1)
        (fun j => (BankNode.dens_mem hnodes (R.c j)).2) (fun j => (hcells j).2.2.2.1)
        (fun j s h1 h2 => (hcells j).2.2.2.2 s h1 h2)
      have := (hcells j).1
      have : (R.c j).val < v.val := this
      omega

end nodes

/-- Red and blue ordered pairs of `W` add up to `|W| (|W| - 1)`. -/
lemma redPairs_add_compl {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (W : Finset V) :
    (redPairs G W : ℝ) + (redPairs Gᶜ W : ℝ) = (W.card : ℝ) * ((W.card : ℝ) - 1) := by
  have h1 : redPairs Gᶜ W = (W.offDiag.filter (fun e : V × V => ¬ G.Adj e.1 e.2)).card := by
    unfold redPairs
    congr 1
    ext ⟨x, y⟩
    simp only [mem_filter, mem_offDiag, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨h, -, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨h, h.2.2, h2⟩
  have h0 : redPairs G W = (W.offDiag.filter (fun e : V × V => G.Adj e.1 e.2)).card := by
    unfold redPairs; congr 1
  rw [h1, h0]
  have h2 := card_filter_add_card_filter_not (s := W.offDiag) (fun e : V × V => G.Adj e.1 e.2)
  have h3 : (W.offDiag.card : ℝ) = (W.card : ℝ) * ((W.card : ℝ) - 1) := by
    rw [offDiag_card]
    rcases Nat.eq_zero_or_pos W.card with h | h
    · rw [h]; simp
    · push_cast [Nat.cast_sub (Nat.le_mul_self W.card)]; ring
  rw [← h3]; exact_mod_cast h2

/-- Homogeneity of the symmetric profile. -/
lemma symmetricProfile_hom (F : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) :
    symmetricProfile F a b = a * symmetricProfile F 1 (b / a) := by
  unfold symmetricProfile
  have hmax : max a b = a * max 1 (b / a) := by
    rw [mul_max_of_nonneg _ _ ha.le, mul_one, mul_div_cancel₀ _ ha.ne']
  have hmin : min a b = a * min 1 (b / a) := by
    rw [mul_min_of_nonneg _ _ ha.le, mul_one, mul_div_cancel₀ _ ha.ne']
  rw [hmax, hmin, mul_div_mul_left _ _ ha.ne', mul_assoc]

/-- `x^K ≤ K! c^{-K} e^{c x}` for `x ≥ 0`, `c > 0`. -/
lemma pow_le_exp {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (K : ℕ) :
    x ^ K ≤ (K.factorial : ℝ) / c ^ K * Real.exp (c * x) := by
  have h := Real.pow_div_factorial_le_exp (c * x) (mul_nonneg hc.le hx) K
  have hf : (0 : ℝ) < K.factorial := by exact_mod_cast K.factorial_pos
  have hcK : (0 : ℝ) < c ^ K := pow_pos hc K
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
  nlinarith [h]

end DiagRamsey
