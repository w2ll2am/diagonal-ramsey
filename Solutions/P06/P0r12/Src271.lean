import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D347
import Solutions.P06.P0r12.D348

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem src2710_h : (FQ.lt FQ.zero (A (⟨2710, by decide⟩ : Fin 2713)) && FQ.lt FQ.zero (B (⟨2710, by decide⟩ : Fin 2713)) && SourceF.check pd lines (A (⟨2710, by decide⟩ : Fin 2713)) (B (⟨2710, by decide⟩ : Fin 2713)) s2710) = true := by decide +kernel

theorem src2711_h : (FQ.lt FQ.zero (A (⟨2711, by decide⟩ : Fin 2713)) && FQ.lt FQ.zero (B (⟨2711, by decide⟩ : Fin 2713)) && SourceF.check pd lines (A (⟨2711, by decide⟩ : Fin 2713)) (B (⟨2711, by decide⟩ : Fin 2713)) s2711) = true := by decide +kernel

theorem src2712_h : (FQ.lt FQ.zero (A (⟨2712, by decide⟩ : Fin 2713)) && FQ.lt FQ.zero (B (⟨2712, by decide⟩ : Fin 2713)) && SourceF.check pd lines (A (⟨2712, by decide⟩ : Fin 2713)) (B (⟨2712, by decide⟩ : Fin 2713)) s2712) = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
