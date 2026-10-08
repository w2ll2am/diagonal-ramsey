import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D25

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp936_1_ok : RawF.check ctl A B pd i0 (raw (⟨936, by decide⟩ : Fin 1902)) rp936_1 = true := by decide +kernel

theorem rp936_2_ok : RawF.check ctl A B pd i0 (raw (⟨936, by decide⟩ : Fin 1902)) rp936_2 = true := by decide +kernel

theorem raw936_h : ((raw (⟨936, by decide⟩ : Fin 1902)).ok (rawMin (⟨936, by decide⟩ : Fin 1902)) && chainF ((raw (⟨936, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp936.map (fun x => (x.lo, x.hi))) ((raw (⟨936, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp937_0_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_0 = true := by decide +kernel

theorem rp937_1_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_1 = true := by decide +kernel

theorem rp937_2_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_2 = true := by decide +kernel

theorem rp937_3_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_3 = true := by decide +kernel

theorem rp937_4_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_4 = true := by decide +kernel

theorem rp937_5_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_5 = true := by decide +kernel

theorem rp937_6_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_6 = true := by decide +kernel

theorem rp937_7_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_7 = true := by decide +kernel

theorem rp937_8_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_8 = true := by decide +kernel

theorem rp937_9_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_9 = true := by decide +kernel

theorem rp937_10_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_10 = true := by decide +kernel

theorem rp937_11_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_11 = true := by decide +kernel

theorem rp937_12_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_12 = true := by decide +kernel

theorem rp937_13_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_13 = true := by decide +kernel

theorem rp937_14_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_14 = true := by decide +kernel

theorem rp937_15_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_15 = true := by decide +kernel

theorem rp937_16_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_16 = true := by decide +kernel

theorem rp937_17_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_17 = true := by decide +kernel

theorem rp937_18_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_18 = true := by decide +kernel

theorem rp937_19_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_19 = true := by decide +kernel

theorem rp937_20_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_20 = true := by decide +kernel

theorem rp937_21_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_21 = true := by decide +kernel

theorem rp937_22_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_22 = true := by decide +kernel

theorem rp937_23_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_23 = true := by decide +kernel

theorem rp937_24_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_24 = true := by decide +kernel

theorem rp937_25_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_25 = true := by decide +kernel

theorem rp937_26_ok : RawF.check ctl A B pd i0 (raw (⟨937, by decide⟩ : Fin 1902)) rp937_26 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
