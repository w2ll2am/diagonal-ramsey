import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D25

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp940_4_ok : RawF.check ctl A B pd i0 (raw (⟨940, by decide⟩ : Fin 1902)) rp940_4 = true := by decide +kernel

theorem rp940_5_ok : RawF.check ctl A B pd i0 (raw (⟨940, by decide⟩ : Fin 1902)) rp940_5 = true := by decide +kernel

theorem rp940_6_ok : RawF.check ctl A B pd i0 (raw (⟨940, by decide⟩ : Fin 1902)) rp940_6 = true := by decide +kernel

theorem raw940_h : ((raw (⟨940, by decide⟩ : Fin 1902)).ok (rawMin (⟨940, by decide⟩ : Fin 1902)) && chainF ((raw (⟨940, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp940.map (fun x => (x.lo, x.hi))) ((raw (⟨940, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp941_0_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_0 = true := by decide +kernel

theorem rp941_1_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_1 = true := by decide +kernel

theorem rp941_2_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_2 = true := by decide +kernel

theorem rp941_3_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_3 = true := by decide +kernel

theorem rp941_4_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_4 = true := by decide +kernel

theorem rp941_5_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_5 = true := by decide +kernel

theorem rp941_6_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_6 = true := by decide +kernel

theorem rp941_7_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_7 = true := by decide +kernel

theorem rp941_8_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_8 = true := by decide +kernel

theorem rp941_9_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_9 = true := by decide +kernel

theorem rp941_10_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_10 = true := by decide +kernel

theorem rp941_11_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_11 = true := by decide +kernel

theorem rp941_12_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_12 = true := by decide +kernel

theorem rp941_13_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_13 = true := by decide +kernel

theorem rp941_14_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_14 = true := by decide +kernel

theorem rp941_15_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_15 = true := by decide +kernel

theorem rp941_16_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_16 = true := by decide +kernel

theorem rp941_17_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_17 = true := by decide +kernel

theorem rp941_18_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_18 = true := by decide +kernel

theorem rp941_19_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_19 = true := by decide +kernel

theorem rp941_20_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_20 = true := by decide +kernel

theorem rp941_21_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_21 = true := by decide +kernel

theorem rp941_22_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_22 = true := by decide +kernel

theorem rp941_23_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_23 = true := by decide +kernel

theorem rp941_24_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_24 = true := by decide +kernel

theorem rp941_25_ok : RawF.check ctl A B pd i0 (raw (⟨941, by decide⟩ : Fin 1902)) rp941_25 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
