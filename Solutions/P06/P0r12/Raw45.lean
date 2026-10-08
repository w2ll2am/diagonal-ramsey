import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp101_5_ok : RawF.check ctl A B pd i0 (raw (⟨101, by decide⟩ : Fin 1902)) rp101_5 = true := by decide +kernel

theorem rp101_6_ok : RawF.check ctl A B pd i0 (raw (⟨101, by decide⟩ : Fin 1902)) rp101_6 = true := by decide +kernel

theorem rp101_7_ok : RawF.check ctl A B pd i0 (raw (⟨101, by decide⟩ : Fin 1902)) rp101_7 = true := by decide +kernel

theorem rp101_8_ok : RawF.check ctl A B pd i0 (raw (⟨101, by decide⟩ : Fin 1902)) rp101_8 = true := by decide +kernel

theorem raw101_h : ((raw (⟨101, by decide⟩ : Fin 1902)).ok (rawMin (⟨101, by decide⟩ : Fin 1902)) && chainF ((raw (⟨101, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp101.map (fun x => (x.lo, x.hi))) ((raw (⟨101, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp102_0_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_0 = true := by decide +kernel

theorem rp102_1_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_1 = true := by decide +kernel

theorem rp102_2_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_2 = true := by decide +kernel

theorem rp102_3_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_3 = true := by decide +kernel

theorem rp102_4_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_4 = true := by decide +kernel

theorem rp102_5_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_5 = true := by decide +kernel

theorem rp102_6_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_6 = true := by decide +kernel

theorem rp102_7_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_7 = true := by decide +kernel

theorem rp102_8_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_8 = true := by decide +kernel

theorem rp102_9_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_9 = true := by decide +kernel

theorem rp102_10_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_10 = true := by decide +kernel

theorem rp102_11_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_11 = true := by decide +kernel

theorem rp102_12_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_12 = true := by decide +kernel

theorem rp102_13_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_13 = true := by decide +kernel

theorem rp102_14_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_14 = true := by decide +kernel

theorem rp102_15_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_15 = true := by decide +kernel

theorem rp102_16_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_16 = true := by decide +kernel

theorem rp102_17_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_17 = true := by decide +kernel

theorem rp102_18_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_18 = true := by decide +kernel

theorem rp102_19_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_19 = true := by decide +kernel

theorem rp102_20_ok : RawF.check ctl A B pd i0 (raw (⟨102, by decide⟩ : Fin 1902)) rp102_20 = true := by decide +kernel

theorem raw102_h : ((raw (⟨102, by decide⟩ : Fin 1902)).ok (rawMin (⟨102, by decide⟩ : Fin 1902)) && chainF ((raw (⟨102, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp102.map (fun x => (x.lo, x.hi))) ((raw (⟨102, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp103_0_ok : RawF.check ctl A B pd i0 (raw (⟨103, by decide⟩ : Fin 1902)) rp103_0 = true := by decide +kernel

theorem rp103_1_ok : RawF.check ctl A B pd i0 (raw (⟨103, by decide⟩ : Fin 1902)) rp103_1 = true := by decide +kernel

theorem rp103_2_ok : RawF.check ctl A B pd i0 (raw (⟨103, by decide⟩ : Fin 1902)) rp103_2 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
