import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp445_5_ok : RawF.check ctl A B pd i0 (raw (⟨445, by decide⟩ : Fin 1902)) rp445_5 = true := by decide +kernel

theorem rp445_6_ok : RawF.check ctl A B pd i0 (raw (⟨445, by decide⟩ : Fin 1902)) rp445_6 = true := by decide +kernel

theorem rp445_7_ok : RawF.check ctl A B pd i0 (raw (⟨445, by decide⟩ : Fin 1902)) rp445_7 = true := by decide +kernel

theorem raw445_h : ((raw (⟨445, by decide⟩ : Fin 1902)).ok (rawMin (⟨445, by decide⟩ : Fin 1902)) && chainF ((raw (⟨445, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp445.map (fun x => (x.lo, x.hi))) ((raw (⟨445, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp446_0_ok : RawF.check ctl A B pd i0 (raw (⟨446, by decide⟩ : Fin 1902)) rp446_0 = true := by decide +kernel

theorem raw446_h : ((raw (⟨446, by decide⟩ : Fin 1902)).ok (rawMin (⟨446, by decide⟩ : Fin 1902)) && chainF ((raw (⟨446, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp446.map (fun x => (x.lo, x.hi))) ((raw (⟨446, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp447_0_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_0 = true := by decide +kernel

theorem rp447_1_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_1 = true := by decide +kernel

theorem rp447_2_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_2 = true := by decide +kernel

theorem rp447_3_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_3 = true := by decide +kernel

theorem rp447_4_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_4 = true := by decide +kernel

theorem rp447_5_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_5 = true := by decide +kernel

theorem rp447_6_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_6 = true := by decide +kernel

theorem rp447_7_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_7 = true := by decide +kernel

theorem rp447_8_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_8 = true := by decide +kernel

theorem rp447_9_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_9 = true := by decide +kernel

theorem rp447_10_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_10 = true := by decide +kernel

theorem rp447_11_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_11 = true := by decide +kernel

theorem rp447_12_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_12 = true := by decide +kernel

theorem rp447_13_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_13 = true := by decide +kernel

theorem rp447_14_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_14 = true := by decide +kernel

theorem rp447_15_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_15 = true := by decide +kernel

theorem rp447_16_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_16 = true := by decide +kernel

theorem rp447_17_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_17 = true := by decide +kernel

theorem rp447_18_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_18 = true := by decide +kernel

theorem rp447_19_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_19 = true := by decide +kernel

theorem rp447_20_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_20 = true := by decide +kernel

theorem rp447_21_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_21 = true := by decide +kernel

theorem rp447_22_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_22 = true := by decide +kernel

theorem rp447_23_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_23 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
