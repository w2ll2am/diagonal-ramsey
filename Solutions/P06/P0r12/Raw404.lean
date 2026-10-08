import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D37

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1123_0_ok : RawF.check ctl A B pd i0 (raw (⟨1123, by decide⟩ : Fin 1902)) rp1123_0 = true := by decide +kernel

theorem rp1123_1_ok : RawF.check ctl A B pd i0 (raw (⟨1123, by decide⟩ : Fin 1902)) rp1123_1 = true := by decide +kernel

theorem rp1123_2_ok : RawF.check ctl A B pd i0 (raw (⟨1123, by decide⟩ : Fin 1902)) rp1123_2 = true := by decide +kernel

theorem rp1123_3_ok : RawF.check ctl A B pd i0 (raw (⟨1123, by decide⟩ : Fin 1902)) rp1123_3 = true := by decide +kernel

theorem raw1123_h : ((raw (⟨1123, by decide⟩ : Fin 1902)).ok (rawMin (⟨1123, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1123, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1123.map (fun x => (x.lo, x.hi))) ((raw (⟨1123, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1124_0_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_0 = true := by decide +kernel

theorem rp1124_1_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_1 = true := by decide +kernel

theorem rp1124_2_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_2 = true := by decide +kernel

theorem rp1124_3_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_3 = true := by decide +kernel

theorem rp1124_4_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_4 = true := by decide +kernel

theorem rp1124_5_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_5 = true := by decide +kernel

theorem rp1124_6_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_6 = true := by decide +kernel

theorem rp1124_7_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_7 = true := by decide +kernel

theorem rp1124_8_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_8 = true := by decide +kernel

theorem rp1124_9_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_9 = true := by decide +kernel

theorem rp1124_10_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_10 = true := by decide +kernel

theorem rp1124_11_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_11 = true := by decide +kernel

theorem rp1124_12_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_12 = true := by decide +kernel

theorem rp1124_13_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_13 = true := by decide +kernel

theorem rp1124_14_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_14 = true := by decide +kernel

theorem rp1124_15_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_15 = true := by decide +kernel

theorem rp1124_16_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_16 = true := by decide +kernel

theorem rp1124_17_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_17 = true := by decide +kernel

theorem rp1124_18_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_18 = true := by decide +kernel

theorem rp1124_19_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_19 = true := by decide +kernel

theorem rp1124_20_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_20 = true := by decide +kernel

theorem rp1124_21_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_21 = true := by decide +kernel

theorem rp1124_22_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_22 = true := by decide +kernel

theorem rp1124_23_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_23 = true := by decide +kernel

theorem rp1124_24_ok : RawF.check ctl A B pd i0 (raw (⟨1124, by decide⟩ : Fin 1902)) rp1124_24 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
