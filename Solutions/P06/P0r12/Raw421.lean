import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D38

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1163_5_ok : RawF.check ctl A B pd i0 (raw (⟨1163, by decide⟩ : Fin 1902)) rp1163_5 = true := by decide +kernel

theorem rp1163_6_ok : RawF.check ctl A B pd i0 (raw (⟨1163, by decide⟩ : Fin 1902)) rp1163_6 = true := by decide +kernel

theorem raw1163_h : ((raw (⟨1163, by decide⟩ : Fin 1902)).ok (rawMin (⟨1163, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1163, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1163.map (fun x => (x.lo, x.hi))) ((raw (⟨1163, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1164_0_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_0 = true := by decide +kernel

theorem rp1164_1_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_1 = true := by decide +kernel

theorem rp1164_2_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_2 = true := by decide +kernel

theorem rp1164_3_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_3 = true := by decide +kernel

theorem rp1164_4_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_4 = true := by decide +kernel

theorem rp1164_5_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_5 = true := by decide +kernel

theorem rp1164_6_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_6 = true := by decide +kernel

theorem rp1164_7_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_7 = true := by decide +kernel

theorem rp1164_8_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_8 = true := by decide +kernel

theorem rp1164_9_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_9 = true := by decide +kernel

theorem rp1164_10_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_10 = true := by decide +kernel

theorem rp1164_11_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_11 = true := by decide +kernel

theorem rp1164_12_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_12 = true := by decide +kernel

theorem rp1164_13_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_13 = true := by decide +kernel

theorem rp1164_14_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_14 = true := by decide +kernel

theorem rp1164_15_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_15 = true := by decide +kernel

theorem rp1164_16_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_16 = true := by decide +kernel

theorem rp1164_17_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_17 = true := by decide +kernel

theorem rp1164_18_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_18 = true := by decide +kernel

theorem rp1164_19_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_19 = true := by decide +kernel

theorem rp1164_20_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_20 = true := by decide +kernel

theorem rp1164_21_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_21 = true := by decide +kernel

theorem rp1164_22_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_22 = true := by decide +kernel

theorem rp1164_23_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_23 = true := by decide +kernel

theorem rp1164_24_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_24 = true := by decide +kernel

theorem rp1164_25_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_25 = true := by decide +kernel

theorem rp1164_26_ok : RawF.check ctl A B pd i0 (raw (⟨1164, by decide⟩ : Fin 1902)) rp1164_26 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
