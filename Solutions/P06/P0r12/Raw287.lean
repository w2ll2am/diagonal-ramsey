import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp805_34_ok : RawF.check ctl A B pd i0 (raw (⟨805, by decide⟩ : Fin 1902)) rp805_34 = true := by decide +kernel

theorem rp805_35_ok : RawF.check ctl A B pd i0 (raw (⟨805, by decide⟩ : Fin 1902)) rp805_35 = true := by decide +kernel

theorem raw805_h : ((raw (⟨805, by decide⟩ : Fin 1902)).ok (rawMin (⟨805, by decide⟩ : Fin 1902)) && chainF ((raw (⟨805, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp805.map (fun x => (x.lo, x.hi))) ((raw (⟨805, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp806_0_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_0 = true := by decide +kernel

theorem rp806_1_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_1 = true := by decide +kernel

theorem rp806_2_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_2 = true := by decide +kernel

theorem rp806_3_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_3 = true := by decide +kernel

theorem rp806_4_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_4 = true := by decide +kernel

theorem rp806_5_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_5 = true := by decide +kernel

theorem rp806_6_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_6 = true := by decide +kernel

theorem rp806_7_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_7 = true := by decide +kernel

theorem rp806_8_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_8 = true := by decide +kernel

theorem rp806_9_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_9 = true := by decide +kernel

theorem rp806_10_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_10 = true := by decide +kernel

theorem rp806_11_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_11 = true := by decide +kernel

theorem rp806_12_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_12 = true := by decide +kernel

theorem rp806_13_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_13 = true := by decide +kernel

theorem rp806_14_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_14 = true := by decide +kernel

theorem rp806_15_ok : RawF.check ctl A B pd i0 (raw (⟨806, by decide⟩ : Fin 1902)) rp806_15 = true := by decide +kernel

theorem raw806_h : ((raw (⟨806, by decide⟩ : Fin 1902)).ok (rawMin (⟨806, by decide⟩ : Fin 1902)) && chainF ((raw (⟨806, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp806.map (fun x => (x.lo, x.hi))) ((raw (⟨806, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp807_0_ok : RawF.check ctl A B pd i0 (raw (⟨807, by decide⟩ : Fin 1902)) rp807_0 = true := by decide +kernel

theorem raw807_h : ((raw (⟨807, by decide⟩ : Fin 1902)).ok (rawMin (⟨807, by decide⟩ : Fin 1902)) && chainF ((raw (⟨807, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp807.map (fun x => (x.lo, x.hi))) ((raw (⟨807, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp808_0_ok : RawF.check ctl A B pd i0 (raw (⟨808, by decide⟩ : Fin 1902)) rp808_0 = true := by decide +kernel

theorem rp808_1_ok : RawF.check ctl A B pd i0 (raw (⟨808, by decide⟩ : Fin 1902)) rp808_1 = true := by decide +kernel

theorem rp808_2_ok : RawF.check ctl A B pd i0 (raw (⟨808, by decide⟩ : Fin 1902)) rp808_2 = true := by decide +kernel

theorem rp808_3_ok : RawF.check ctl A B pd i0 (raw (⟨808, by decide⟩ : Fin 1902)) rp808_3 = true := by decide +kernel

theorem rp808_4_ok : RawF.check ctl A B pd i0 (raw (⟨808, by decide⟩ : Fin 1902)) rp808_4 = true := by decide +kernel

theorem rp808_5_ok : RawF.check ctl A B pd i0 (raw (⟨808, by decide⟩ : Fin 1902)) rp808_5 = true := by decide +kernel

theorem rp808_6_ok : RawF.check ctl A B pd i0 (raw (⟨808, by decide⟩ : Fin 1902)) rp808_6 = true := by decide +kernel

theorem rp808_7_ok : RawF.check ctl A B pd i0 (raw (⟨808, by decide⟩ : Fin 1902)) rp808_7 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
