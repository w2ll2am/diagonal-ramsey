import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D45

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1313_1_ok : RawF.check ctl A B pd i0 (raw (⟨1313, by decide⟩ : Fin 1902)) rp1313_1 = true := by decide +kernel

theorem rp1313_2_ok : RawF.check ctl A B pd i0 (raw (⟨1313, by decide⟩ : Fin 1902)) rp1313_2 = true := by decide +kernel

theorem raw1313_h : ((raw (⟨1313, by decide⟩ : Fin 1902)).ok (rawMin (⟨1313, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1313, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1313.map (fun x => (x.lo, x.hi))) ((raw (⟨1313, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1314_0_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_0 = true := by decide +kernel

theorem rp1314_1_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_1 = true := by decide +kernel

theorem rp1314_2_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_2 = true := by decide +kernel

theorem rp1314_3_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_3 = true := by decide +kernel

theorem rp1314_4_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_4 = true := by decide +kernel

theorem rp1314_5_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_5 = true := by decide +kernel

theorem rp1314_6_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_6 = true := by decide +kernel

theorem rp1314_7_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_7 = true := by decide +kernel

theorem rp1314_8_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_8 = true := by decide +kernel

theorem rp1314_9_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_9 = true := by decide +kernel

theorem rp1314_10_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_10 = true := by decide +kernel

theorem rp1314_11_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_11 = true := by decide +kernel

theorem rp1314_12_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_12 = true := by decide +kernel

theorem rp1314_13_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_13 = true := by decide +kernel

theorem rp1314_14_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_14 = true := by decide +kernel

theorem rp1314_15_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_15 = true := by decide +kernel

theorem rp1314_16_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_16 = true := by decide +kernel

theorem rp1314_17_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_17 = true := by decide +kernel

theorem rp1314_18_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_18 = true := by decide +kernel

theorem rp1314_19_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_19 = true := by decide +kernel

theorem rp1314_20_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_20 = true := by decide +kernel

theorem rp1314_21_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_21 = true := by decide +kernel

theorem rp1314_22_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_22 = true := by decide +kernel

theorem rp1314_23_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_23 = true := by decide +kernel

theorem rp1314_24_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_24 = true := by decide +kernel

theorem rp1314_25_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_25 = true := by decide +kernel

theorem rp1314_26_ok : RawF.check ctl A B pd i0 (raw (⟨1314, by decide⟩ : Fin 1902)) rp1314_26 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
