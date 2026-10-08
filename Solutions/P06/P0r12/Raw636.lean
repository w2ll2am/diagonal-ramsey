import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1900_9_ok : RawF.check ctl A B pd i0 (raw (⟨1900, by decide⟩ : Fin 1902)) rp1900_9 = true := by decide +kernel

theorem raw1900_h : ((raw (⟨1900, by decide⟩ : Fin 1902)).ok (rawMin (⟨1900, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1900, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1900.map (fun x => (x.lo, x.hi))) ((raw (⟨1900, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1901_0_ok : RawF.check ctl A B pd i0 (raw (⟨1901, by decide⟩ : Fin 1902)) rp1901_0 = true := by decide +kernel

theorem rp1901_1_ok : RawF.check ctl A B pd i0 (raw (⟨1901, by decide⟩ : Fin 1902)) rp1901_1 = true := by decide +kernel

theorem raw1901_h : ((raw (⟨1901, by decide⟩ : Fin 1902)).ok (rawMin (⟨1901, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1901, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1901.map (fun x => (x.lo, x.hi))) ((raw (⟨1901, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
