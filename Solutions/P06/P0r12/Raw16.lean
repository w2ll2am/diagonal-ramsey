import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp55_15_ok : RawF.check ctl A B pd i0 (raw (⟨55, by decide⟩ : Fin 1902)) rp55_15 = true := by decide +kernel

theorem rp55_16_ok : RawF.check ctl A B pd i0 (raw (⟨55, by decide⟩ : Fin 1902)) rp55_16 = true := by decide +kernel

theorem rp55_17_ok : RawF.check ctl A B pd i0 (raw (⟨55, by decide⟩ : Fin 1902)) rp55_17 = true := by decide +kernel

theorem rp55_18_ok : RawF.check ctl A B pd i0 (raw (⟨55, by decide⟩ : Fin 1902)) rp55_18 = true := by decide +kernel

theorem raw55_h : ((raw (⟨55, by decide⟩ : Fin 1902)).ok (rawMin (⟨55, by decide⟩ : Fin 1902)) && chainF ((raw (⟨55, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp55.map (fun x => (x.lo, x.hi))) ((raw (⟨55, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp56_0_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_0 = true := by decide +kernel

theorem rp56_1_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_1 = true := by decide +kernel

theorem rp56_2_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_2 = true := by decide +kernel

theorem rp56_3_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_3 = true := by decide +kernel

theorem rp56_4_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_4 = true := by decide +kernel

theorem rp56_5_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_5 = true := by decide +kernel

theorem rp56_6_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_6 = true := by decide +kernel

theorem rp56_7_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_7 = true := by decide +kernel

theorem rp56_8_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_8 = true := by decide +kernel

theorem rp56_9_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_9 = true := by decide +kernel

theorem rp56_10_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_10 = true := by decide +kernel

theorem rp56_11_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_11 = true := by decide +kernel

theorem rp56_12_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_12 = true := by decide +kernel

theorem rp56_13_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_13 = true := by decide +kernel

theorem rp56_14_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_14 = true := by decide +kernel

theorem rp56_15_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_15 = true := by decide +kernel

theorem rp56_16_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_16 = true := by decide +kernel

theorem rp56_17_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_17 = true := by decide +kernel

theorem rp56_18_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_18 = true := by decide +kernel

theorem rp56_19_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_19 = true := by decide +kernel

theorem rp56_20_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_20 = true := by decide +kernel

theorem rp56_21_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_21 = true := by decide +kernel

theorem rp56_22_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_22 = true := by decide +kernel

theorem rp56_23_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_23 = true := by decide +kernel

theorem rp56_24_ok : RawF.check ctl A B pd i0 (raw (⟨56, by decide⟩ : Fin 1902)) rp56_24 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
