import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D19

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp774_1_ok : RawF.check ctl A B pd i0 (raw (⟨774, by decide⟩ : Fin 1902)) rp774_1 = true := by decide +kernel

theorem rp774_2_ok : RawF.check ctl A B pd i0 (raw (⟨774, by decide⟩ : Fin 1902)) rp774_2 = true := by decide +kernel

theorem rp774_3_ok : RawF.check ctl A B pd i0 (raw (⟨774, by decide⟩ : Fin 1902)) rp774_3 = true := by decide +kernel

theorem rp774_4_ok : RawF.check ctl A B pd i0 (raw (⟨774, by decide⟩ : Fin 1902)) rp774_4 = true := by decide +kernel

theorem raw774_h : ((raw (⟨774, by decide⟩ : Fin 1902)).ok (rawMin (⟨774, by decide⟩ : Fin 1902)) && chainF ((raw (⟨774, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp774.map (fun x => (x.lo, x.hi))) ((raw (⟨774, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp775_0_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_0 = true := by decide +kernel

theorem rp775_1_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_1 = true := by decide +kernel

theorem rp775_2_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_2 = true := by decide +kernel

theorem rp775_3_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_3 = true := by decide +kernel

theorem rp775_4_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_4 = true := by decide +kernel

theorem rp775_5_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_5 = true := by decide +kernel

theorem rp775_6_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_6 = true := by decide +kernel

theorem rp775_7_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_7 = true := by decide +kernel

theorem rp775_8_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_8 = true := by decide +kernel

theorem rp775_9_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_9 = true := by decide +kernel

theorem rp775_10_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_10 = true := by decide +kernel

theorem rp775_11_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_11 = true := by decide +kernel

theorem rp775_12_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_12 = true := by decide +kernel

theorem rp775_13_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_13 = true := by decide +kernel

theorem rp775_14_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_14 = true := by decide +kernel

theorem rp775_15_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_15 = true := by decide +kernel

theorem rp775_16_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_16 = true := by decide +kernel

theorem rp775_17_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_17 = true := by decide +kernel

theorem rp775_18_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_18 = true := by decide +kernel

theorem rp775_19_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_19 = true := by decide +kernel

theorem rp775_20_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_20 = true := by decide +kernel

theorem rp775_21_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_21 = true := by decide +kernel

theorem rp775_22_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_22 = true := by decide +kernel

theorem rp775_23_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_23 = true := by decide +kernel

theorem rp775_24_ok : RawF.check ctl A B pd i0 (raw (⟨775, by decide⟩ : Fin 1902)) rp775_24 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
