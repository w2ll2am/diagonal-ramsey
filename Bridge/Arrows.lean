import RamseyCurrent.ImportedDefinitions
import Definitions.Def_DiagRamsey_Basic

/-! The project's `RamseyArrows` / `ramseyNumber` against RamseyLean's `ramseyNumber` (used by Lu--Wang). -/

namespace LuWangBridge

theorem arrows_iff (a b N : ℕ) : DiagRamsey.RamseyArrows a b N ↔ RamseyLean.ramseyNumber a b ≤ N :=
  (RamseyCurrent.ImportedDefinitions.ramseyNumber_le_iff_coloring a b N).symm

theorem ramseyNumber_eq (a b : ℕ) : DiagRamsey.ramseyNumber a b = RamseyLean.ramseyNumber a b := by
  have hmem : RamseyLean.ramseyNumber a b ∈ {N : ℕ | DiagRamsey.RamseyArrows a b N} :=
    (arrows_iff _ _ _).2 le_rfl
  apply le_antisymm (Nat.sInf_le hmem)
  exact (arrows_iff _ _ _).1 (Nat.sInf_mem ⟨_, hmem⟩)

end LuWangBridge
