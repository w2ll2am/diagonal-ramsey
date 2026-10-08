import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D8

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp502_29_ok : RawF.check ctl A B pd i0 (raw (⟨502, by decide⟩ : Fin 1902)) rp502_29 = true := by decide +kernel

theorem rp502_30_ok : RawF.check ctl A B pd i0 (raw (⟨502, by decide⟩ : Fin 1902)) rp502_30 = true := by decide +kernel

theorem rp502_31_ok : RawF.check ctl A B pd i0 (raw (⟨502, by decide⟩ : Fin 1902)) rp502_31 = true := by decide +kernel

theorem rp502_32_ok : RawF.check ctl A B pd i0 (raw (⟨502, by decide⟩ : Fin 1902)) rp502_32 = true := by decide +kernel

theorem raw502_h : ((raw (⟨502, by decide⟩ : Fin 1902)).ok (rawMin (⟨502, by decide⟩ : Fin 1902)) && chainF ((raw (⟨502, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp502.map (fun x => (x.lo, x.hi))) ((raw (⟨502, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp503_0_ok : RawF.check ctl A B pd i0 (raw (⟨503, by decide⟩ : Fin 1902)) rp503_0 = true := by decide +kernel

theorem rp503_1_ok : RawF.check ctl A B pd i0 (raw (⟨503, by decide⟩ : Fin 1902)) rp503_1 = true := by decide +kernel

theorem rp503_2_ok : RawF.check ctl A B pd i0 (raw (⟨503, by decide⟩ : Fin 1902)) rp503_2 = true := by decide +kernel

theorem raw503_h : ((raw (⟨503, by decide⟩ : Fin 1902)).ok (rawMin (⟨503, by decide⟩ : Fin 1902)) && chainF ((raw (⟨503, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp503.map (fun x => (x.lo, x.hi))) ((raw (⟨503, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp504_0_ok : RawF.check ctl A B pd i0 (raw (⟨504, by decide⟩ : Fin 1902)) rp504_0 = true := by decide +kernel

theorem raw504_h : ((raw (⟨504, by decide⟩ : Fin 1902)).ok (rawMin (⟨504, by decide⟩ : Fin 1902)) && chainF ((raw (⟨504, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp504.map (fun x => (x.lo, x.hi))) ((raw (⟨504, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp505_0_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_0 = true := by decide +kernel

theorem rp505_1_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_1 = true := by decide +kernel

theorem rp505_2_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_2 = true := by decide +kernel

theorem rp505_3_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_3 = true := by decide +kernel

theorem rp505_4_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_4 = true := by decide +kernel

theorem rp505_5_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_5 = true := by decide +kernel

theorem rp505_6_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_6 = true := by decide +kernel

theorem rp505_7_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_7 = true := by decide +kernel

theorem rp505_8_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_8 = true := by decide +kernel

theorem rp505_9_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_9 = true := by decide +kernel

theorem rp505_10_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_10 = true := by decide +kernel

theorem rp505_11_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_11 = true := by decide +kernel

theorem rp505_12_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_12 = true := by decide +kernel

theorem rp505_13_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_13 = true := by decide +kernel

theorem rp505_14_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_14 = true := by decide +kernel

theorem rp505_15_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_15 = true := by decide +kernel

theorem rp505_16_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_16 = true := by decide +kernel

theorem rp505_17_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_17 = true := by decide +kernel

theorem rp505_18_ok : RawF.check ctl A B pd i0 (raw (⟨505, by decide⟩ : Fin 1902)) rp505_18 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
