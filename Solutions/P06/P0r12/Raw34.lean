import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp83_2_ok : RawF.check ctl A B pd i0 (raw (⟨83, by decide⟩ : Fin 1902)) rp83_2 = true := by decide +kernel

theorem rp83_3_ok : RawF.check ctl A B pd i0 (raw (⟨83, by decide⟩ : Fin 1902)) rp83_3 = true := by decide +kernel

theorem raw83_h : ((raw (⟨83, by decide⟩ : Fin 1902)).ok (rawMin (⟨83, by decide⟩ : Fin 1902)) && chainF ((raw (⟨83, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp83.map (fun x => (x.lo, x.hi))) ((raw (⟨83, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp84_0_ok : RawF.check ctl A B pd i0 (raw (⟨84, by decide⟩ : Fin 1902)) rp84_0 = true := by decide +kernel

theorem rp84_1_ok : RawF.check ctl A B pd i0 (raw (⟨84, by decide⟩ : Fin 1902)) rp84_1 = true := by decide +kernel

theorem rp84_2_ok : RawF.check ctl A B pd i0 (raw (⟨84, by decide⟩ : Fin 1902)) rp84_2 = true := by decide +kernel

theorem raw84_h : ((raw (⟨84, by decide⟩ : Fin 1902)).ok (rawMin (⟨84, by decide⟩ : Fin 1902)) && chainF ((raw (⟨84, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp84.map (fun x => (x.lo, x.hi))) ((raw (⟨84, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp85_0_ok : RawF.check ctl A B pd i0 (raw (⟨85, by decide⟩ : Fin 1902)) rp85_0 = true := by decide +kernel

theorem rp85_1_ok : RawF.check ctl A B pd i0 (raw (⟨85, by decide⟩ : Fin 1902)) rp85_1 = true := by decide +kernel

theorem raw85_h : ((raw (⟨85, by decide⟩ : Fin 1902)).ok (rawMin (⟨85, by decide⟩ : Fin 1902)) && chainF ((raw (⟨85, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp85.map (fun x => (x.lo, x.hi))) ((raw (⟨85, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp86_0_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_0 = true := by decide +kernel

theorem rp86_1_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_1 = true := by decide +kernel

theorem rp86_2_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_2 = true := by decide +kernel

theorem rp86_3_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_3 = true := by decide +kernel

theorem rp86_4_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_4 = true := by decide +kernel

theorem rp86_5_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_5 = true := by decide +kernel

theorem rp86_6_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_6 = true := by decide +kernel

theorem rp86_7_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_7 = true := by decide +kernel

theorem rp86_8_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_8 = true := by decide +kernel

theorem rp86_9_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_9 = true := by decide +kernel

theorem rp86_10_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_10 = true := by decide +kernel

theorem rp86_11_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_11 = true := by decide +kernel

theorem rp86_12_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_12 = true := by decide +kernel

theorem rp86_13_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_13 = true := by decide +kernel

theorem rp86_14_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_14 = true := by decide +kernel

theorem rp86_15_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_15 = true := by decide +kernel

theorem rp86_16_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_16 = true := by decide +kernel

theorem rp86_17_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_17 = true := by decide +kernel

theorem rp86_18_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_18 = true := by decide +kernel

theorem rp86_19_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_19 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
