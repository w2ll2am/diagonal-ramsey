import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp305_0_ok : RawF.check ctl A B pd i0 (raw (⟨305, by decide⟩ : Fin 1902)) rp305_0 = true := by decide +kernel

theorem rp305_1_ok : RawF.check ctl A B pd i0 (raw (⟨305, by decide⟩ : Fin 1902)) rp305_1 = true := by decide +kernel

theorem rp305_2_ok : RawF.check ctl A B pd i0 (raw (⟨305, by decide⟩ : Fin 1902)) rp305_2 = true := by decide +kernel

theorem raw305_h : ((raw (⟨305, by decide⟩ : Fin 1902)).ok (rawMin (⟨305, by decide⟩ : Fin 1902)) && chainF ((raw (⟨305, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp305.map (fun x => (x.lo, x.hi))) ((raw (⟨305, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp306_0_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_0 = true := by decide +kernel

theorem rp306_1_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_1 = true := by decide +kernel

theorem rp306_2_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_2 = true := by decide +kernel

theorem rp306_3_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_3 = true := by decide +kernel

theorem rp306_4_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_4 = true := by decide +kernel

theorem rp306_5_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_5 = true := by decide +kernel

theorem rp306_6_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_6 = true := by decide +kernel

theorem rp306_7_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_7 = true := by decide +kernel

theorem rp306_8_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_8 = true := by decide +kernel

theorem rp306_9_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_9 = true := by decide +kernel

theorem rp306_10_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_10 = true := by decide +kernel

theorem rp306_11_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_11 = true := by decide +kernel

theorem rp306_12_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_12 = true := by decide +kernel

theorem rp306_13_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_13 = true := by decide +kernel

theorem rp306_14_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_14 = true := by decide +kernel

theorem rp306_15_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_15 = true := by decide +kernel

theorem rp306_16_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_16 = true := by decide +kernel

theorem rp306_17_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_17 = true := by decide +kernel

theorem rp306_18_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_18 = true := by decide +kernel

theorem rp306_19_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_19 = true := by decide +kernel

theorem rp306_20_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_20 = true := by decide +kernel

theorem rp306_21_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_21 = true := by decide +kernel

theorem rp306_22_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_22 = true := by decide +kernel

theorem rp306_23_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_23 = true := by decide +kernel

theorem rp306_24_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_24 = true := by decide +kernel

theorem rp306_25_ok : RawF.check ctl A B pd i0 (raw (⟨306, by decide⟩ : Fin 1902)) rp306_25 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
