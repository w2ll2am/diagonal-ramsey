import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D44

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1300_1_ok : RawF.check ctl A B pd i0 (raw (⟨1300, by decide⟩ : Fin 1902)) rp1300_1 = true := by decide +kernel

theorem rp1300_2_ok : RawF.check ctl A B pd i0 (raw (⟨1300, by decide⟩ : Fin 1902)) rp1300_2 = true := by decide +kernel

theorem rp1300_3_ok : RawF.check ctl A B pd i0 (raw (⟨1300, by decide⟩ : Fin 1902)) rp1300_3 = true := by decide +kernel

theorem rp1300_4_ok : RawF.check ctl A B pd i0 (raw (⟨1300, by decide⟩ : Fin 1902)) rp1300_4 = true := by decide +kernel

theorem raw1300_h : ((raw (⟨1300, by decide⟩ : Fin 1902)).ok (rawMin (⟨1300, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1300, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1300.map (fun x => (x.lo, x.hi))) ((raw (⟨1300, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1301_0_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_0 = true := by decide +kernel

theorem rp1301_1_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_1 = true := by decide +kernel

theorem rp1301_2_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_2 = true := by decide +kernel

theorem rp1301_3_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_3 = true := by decide +kernel

theorem rp1301_4_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_4 = true := by decide +kernel

theorem rp1301_5_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_5 = true := by decide +kernel

theorem rp1301_6_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_6 = true := by decide +kernel

theorem rp1301_7_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_7 = true := by decide +kernel

theorem rp1301_8_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_8 = true := by decide +kernel

theorem rp1301_9_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_9 = true := by decide +kernel

theorem rp1301_10_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_10 = true := by decide +kernel

theorem rp1301_11_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_11 = true := by decide +kernel

theorem rp1301_12_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_12 = true := by decide +kernel

theorem rp1301_13_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_13 = true := by decide +kernel

theorem rp1301_14_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_14 = true := by decide +kernel

theorem rp1301_15_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_15 = true := by decide +kernel

theorem rp1301_16_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_16 = true := by decide +kernel

theorem rp1301_17_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_17 = true := by decide +kernel

theorem rp1301_18_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_18 = true := by decide +kernel

theorem rp1301_19_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_19 = true := by decide +kernel

theorem rp1301_20_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_20 = true := by decide +kernel

theorem rp1301_21_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_21 = true := by decide +kernel

theorem rp1301_22_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_22 = true := by decide +kernel

theorem rp1301_23_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_23 = true := by decide +kernel

theorem rp1301_24_ok : RawF.check ctl A B pd i0 (raw (⟨1301, by decide⟩ : Fin 1902)) rp1301_24 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
