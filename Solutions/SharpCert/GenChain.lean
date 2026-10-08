import Solutions.SharpCert.Gen

/-!
# Chain property of data-backed cells from their indices

Author: rupert-of-salzburg. `chainOk` over all 8192 cells of a certificate, decided directly by the kernel,
needs too much memory on a 15 GB machine. Here it follows from the (cheap, `ℕ`-only) fact that the cell
indices are `lo, lo + 1, …, lo + n - 1`.
-/

namespace DiagRamsey.SharpCert

lemma chainOk_of_ks (g : Glob) (K : ℕ) : ∀ (D : List CellD) (lo n : ℕ),
    D.map (·.k) = List.range' lo n →
    chainOk (gridPt g K lo) (D.map (mkCellD g K)) (gridPt g K (lo + n)) = true := by
  intro D
  induction D with
  | nil =>
    intro lo n h
    cases n with
    | zero => simp [chainOk]
    | succ n => simp [List.range'_succ] at h
  | cons d D ih =>
    intro lo n h
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.map_cons, List.range'_succ, List.cons.injEq] at h
      obtain ⟨hk, hD⟩ := h
      simp only [List.map_cons, chainOk, mkCellD, hk, decide_true, Bool.true_and]
      rw [show lo + (n + 1) = lo + 1 + n by omega]
      exact ih (lo + 1) n hD

/-- Concatenation step for the per-block checks (a flat `simp only` over 256 blocks exceeds the recursion
depth; isidore-the-farmer's fix, `research/isidore-the-farmer/NOTES.md`). -/
theorem all_app_ok (g : Glob) (K : ℕ) (pts : List Pt) {l1 l2 : List CellD}
    (h1 : (l1.map (mkCellD g K)).all (cellFull g pts) = true)
    (h2 : (l2.map (mkCellD g K)).all (cellFull g pts) = true) :
    ((l1 ++ l2).map (mkCellD g K)).all (cellFull g pts) = true := by
  rw [List.map_append, List.all_append, h1, h2]; rfl

theorem cert_neg_of_data_ks (g : Glob) (K : ℕ) (pts : List Pt) (D : List CellD)
    (hg : g.ok = true) (hks : D.map (·.k) = List.range' 0 K)
    (h0 : gridPt g K 0 = g.q0) (hK : gridPt g K K = g.mu)
    (hall : (D.map (mkCellD g K)).all (cellFull g pts) = true)
    {P0 : Pt} {rest : List Pt} (hpts0 : pts = P0 :: rest)
    (hP0 : P0.lam = 0) (hpts : ptsOk (P0 :: rest) = true) (hneg : intUB g (P0 :: rest) < 0) :
    (certFeasible (g.p : ℝ) g.mu g.w g.beta g.x).Nonempty ∧
      cert (g.p : ℝ) g.mu g.w g.beta g.x < 0 := by
  have hch := chainOk_of_ks g K D 0 K hks
  rw [h0, zero_add, hK] at hch
  exact cert_neg_of_data g K pts D hg hch hall hpts0 hP0 hpts hneg

end DiagRamsey.SharpCert
