import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
Basic definitions for the diagonal Ramsey project.

A red/blue colouring of the edges of the complete graph on `N` vertices is a simple graph `G` on `Fin N`
(red edges = edges of `G`, blue edges = edges of the complement `Gᶜ`).
-/

namespace DiagRamsey

/-- Every red/blue colouring of the edges of `K_N` has a red `k`-clique or a blue `l`-clique. -/
def RamseyArrows (k l N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ S : Finset (Fin N), G.IsNClique k S) ∨ (∃ S : Finset (Fin N), Gᶜ.IsNClique l S)

/-- The Ramsey number `R(k, l)`: the least `N` such that `RamseyArrows k l N`. (By Ramsey's theorem the set is
nonempty for all `k, l`; `sInf ∅ = 0` is never reached.) -/
noncomputable def ramseyNumber (k l : ℕ) : ℕ :=
  sInf {N : ℕ | RamseyArrows k l N}

end DiagRamsey
