import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Choose.Cast
import Lemmas.DiagRamsey_SB_Leaf
import Definitions.Def_DiagRamsey_JointBank

/-!
# Joint banks: transfer between a sub-host `Z ⊆ V` and the host `↥Z`, and between edge and pair densities

* `transfer`: for `Z : Finset V`, the induced graph `G' = G.comap Subtype.val` on `↥Z` has
  `|univ| = |Z|`, `redPairs G' univ = redPairs G Z`, and its cliques map into `Z`, in both colours.
* `redPairs_univ_eq`: on a host, `redPairs G univ = 2 |E(G)|`, so `p ≤ d_R(G)` gives `p n (n-1) ≤ redPairs`.

Author: turibius-of-mogrovejo.
-/

namespace DiagRamsey

open Finset Classical

section transfer
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The induced graph on `↥Z`. -/
def induced (G : SimpleGraph V) (Z : Finset V) : SimpleGraph Z := G.comap (Function.Embedding.subtype _)

lemma card_univ_coe (Z : Finset V) : (Finset.univ : Finset Z).card = Z.card := by
  simp

lemma redPairs_induced (G : SimpleGraph V) (Z : Finset V) :
    redPairs (induced G Z) Finset.univ = redPairs G Z := by
  unfold redPairs
  apply Finset.card_bij (fun e _ => ((e.1 : V), (e.2 : V)))
  · rintro ⟨x, y⟩ h
    simp only [mem_filter, mem_offDiag, mem_univ, true_and, induced, SimpleGraph.comap_adj,
      Function.Embedding.coe_subtype] at h ⊢
    exact ⟨⟨x.2, y.2, fun hxy => h.1 (Subtype.ext hxy)⟩, h.2⟩
  · rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ h
    simp only [Prod.mk.injEq] at h
    ext <;> simp [Subtype.ext h.1, Subtype.ext h.2]
  · rintro ⟨x, y⟩ h
    simp only [mem_filter, mem_offDiag] at h
    refine ⟨(⟨x, h.1.1⟩, ⟨y, h.1.2.1⟩), ?_, rfl⟩
    simp only [mem_filter, mem_offDiag, mem_univ, true_and, induced, SimpleGraph.comap_adj,
      Function.Embedding.coe_subtype]
    exact ⟨fun hxy => h.1.2.2 (congrArg Subtype.val hxy), h.2⟩

lemma red_of_induced {G : SimpleGraph V} {Z : Finset V} {k : ℕ}
    (h : HasRedClique (induced G Z) Finset.univ k) : HasRedClique G Z k := by
  obtain ⟨S, -, hS⟩ := h
  refine ⟨S.map (Function.Embedding.subtype _), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.mp hx
    exact y.2
  · refine ⟨?_, by rw [card_map]; exact hS.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨y', hy', rfl⟩ := mem_map.mp (Finset.mem_coe.mp hy)
    have hne : x' ≠ y' := fun h => hxy (by rw [h])
    have := hS.isClique (Finset.mem_coe.mpr hx') (Finset.mem_coe.mpr hy') hne
    simpa [induced] using this

lemma induced_compl (G : SimpleGraph V) (Z : Finset V) : (induced G Z)ᶜ = induced Gᶜ Z := by
  ext x y
  simp only [induced, SimpleGraph.compl_adj, SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (Subtype.ext h), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (congrArg Subtype.val h), h2⟩

lemma blue_of_induced {G : SimpleGraph V} {Z : Finset V} {b : ℕ}
    (h : HasBlueClique (induced G Z) Finset.univ b) : HasBlueClique G Z b := by
  obtain ⟨S, -, hS⟩ := h
  rw [induced_compl] at hS
  exact red_of_induced (G := Gᶜ) ⟨S, subset_univ _, hS⟩

end transfer

section density

lemma redPairs_univ_eq {N : ℕ} (G : SimpleGraph (Fin N)) :
    (redPairs G Finset.univ : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
  have h1 : redPairs G Finset.univ = Fintype.card G.Dart := by
    unfold redPairs
    rw [← Finset.card_univ (α := G.Dart)]
    refine Finset.card_bij (fun e he => ⟨(e.1, e.2), (mem_filter.mp he).2⟩) (fun _ _ => mem_univ _) ?_ ?_
    · intro a _ b _ h
      have := congrArg SimpleGraph.Dart.toProd h
      simpa using this
    · intro d _
      refine ⟨(d.fst, d.snd), ?_, rfl⟩
      simp only [mem_filter, mem_offDiag, mem_univ, true_and]
      exact ⟨d.adj.ne, d.adj⟩
  rw [h1, G.dart_card_eq_twice_card_edges]; push_cast; ring

/-- Edge density to ordered pairs. -/
lemma pairs_of_density {N : ℕ} (G : SimpleGraph (Fin N)) {p : ℝ} (hp : 0 < p)
    (h : p ≤ redEdgeDensity G) :
    p * (((Finset.univ : Finset (Fin N)).card : ℝ) * (((Finset.univ : Finset (Fin N)).card : ℝ) - 1)) ≤
      (redPairs G Finset.univ : ℝ) := by
  rw [redPairs_univ_eq, Finset.card_univ, Fintype.card_fin]
  unfold redEdgeDensity at h
  rw [Nat.cast_choose_two] at h
  rcases lt_or_ge N 2 with hN | hN
  · exfalso
    interval_cases N <;> simp at h <;> linarith
  · have hpos : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 1) / 2 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 1) := by nlinarith
      linarith
    rw [le_div_iff₀ hpos] at h
    linarith

end density

end DiagRamsey
