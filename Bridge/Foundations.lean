import RamseyCurrent.CurrentSourceAdmissible
import Bridge.Source
import Bridge.Arrows
import Bridge.Concave

/-! B3: the project's two source-foundation statements, verbatim, from Lu--Wang's
`RamseyCurrent.CurrentSourceAdmissible.finiteSource` and `CurrentSourceGeometry.concave_closed`. -/

namespace LuWangBridge

open Set

theorem ratio_mem {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    min (a : ℝ) b / max (a : ℝ) b ∈ Icc (0 : ℝ) 1 := by
  have hm : (0 : ℝ) < max (a : ℝ) b := lt_max_of_lt_left (by exact_mod_cast ha)
  exact ⟨div_nonneg (le_min (by positivity) (by positivity)) hm.le, (div_le_one hm).2 min_le_max⟩

theorem symmetricProfile_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    DiagRamsey.symmetricProfile DiagRamsey.luWangSource a b =
      RamseyCurrent.symmetricProfile RamseyCurrent.CurrentSourceGeometry.F a b := by
  simp only [DiagRamsey.symmetricProfile, RamseyCurrent.symmetricProfile, source_eq (ratio_mem ha hb)]

end LuWangBridge

namespace DiagRamsey

theorem lu_wang_uniform_source_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ a b : ℕ, 0 < a → 0 < b → ∀ N : ℕ,
      C * Real.exp (symmetricProfile luWangSource (a : ℝ) (b : ℝ) + ε * ((a : ℝ) + (b : ℝ))) ≤ (N : ℝ) →
      RamseyArrows a b N := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := RamseyCurrent.CurrentSourceAdmissible.finiteSource ε hε
  refine ⟨C, hC, fun a b ha hb N hN => ?_⟩
  rw [LuWangBridge.arrows_iff]
  refine (h a b ha hb).trans (Nat.ceil_le.2 ?_)
  rwa [← LuWangBridge.symmetricProfile_eq ha hb]

end DiagRamsey
