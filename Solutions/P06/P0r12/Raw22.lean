import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp64_10_ok : RawF.check ctl A B pd i0 (raw (⟨64, by decide⟩ : Fin 1902)) rp64_10 = true := by decide +kernel

theorem rp64_11_ok : RawF.check ctl A B pd i0 (raw (⟨64, by decide⟩ : Fin 1902)) rp64_11 = true := by decide +kernel

theorem rp64_12_ok : RawF.check ctl A B pd i0 (raw (⟨64, by decide⟩ : Fin 1902)) rp64_12 = true := by decide +kernel

theorem rp64_13_ok : RawF.check ctl A B pd i0 (raw (⟨64, by decide⟩ : Fin 1902)) rp64_13 = true := by decide +kernel

theorem rp64_14_ok : RawF.check ctl A B pd i0 (raw (⟨64, by decide⟩ : Fin 1902)) rp64_14 = true := by decide +kernel

theorem rp64_15_ok : RawF.check ctl A B pd i0 (raw (⟨64, by decide⟩ : Fin 1902)) rp64_15 = true := by decide +kernel

theorem raw64_h : ((raw (⟨64, by decide⟩ : Fin 1902)).ok (rawMin (⟨64, by decide⟩ : Fin 1902)) && chainF ((raw (⟨64, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp64.map (fun x => (x.lo, x.hi))) ((raw (⟨64, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp65_0_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_0 = true := by decide +kernel

theorem rp65_1_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_1 = true := by decide +kernel

theorem rp65_2_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_2 = true := by decide +kernel

theorem rp65_3_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_3 = true := by decide +kernel

theorem rp65_4_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_4 = true := by decide +kernel

theorem rp65_5_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_5 = true := by decide +kernel

theorem rp65_6_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_6 = true := by decide +kernel

theorem rp65_7_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_7 = true := by decide +kernel

theorem rp65_8_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_8 = true := by decide +kernel

theorem rp65_9_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_9 = true := by decide +kernel

theorem rp65_10_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_10 = true := by decide +kernel

theorem rp65_11_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_11 = true := by decide +kernel

theorem rp65_12_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_12 = true := by decide +kernel

theorem rp65_13_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_13 = true := by decide +kernel

theorem rp65_14_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_14 = true := by decide +kernel

theorem rp65_15_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_15 = true := by decide +kernel

theorem rp65_16_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_16 = true := by decide +kernel

theorem rp65_17_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_17 = true := by decide +kernel

theorem rp65_18_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_18 = true := by decide +kernel

theorem rp65_19_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_19 = true := by decide +kernel

theorem rp65_20_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_20 = true := by decide +kernel

theorem rp65_21_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_21 = true := by decide +kernel

theorem rp65_22_ok : RawF.check ctl A B pd i0 (raw (⟨65, by decide⟩ : Fin 1902)) rp65_22 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
