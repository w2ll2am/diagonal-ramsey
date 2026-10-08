import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D24

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp909_4_ok : RawF.check ctl A B pd i0 (raw (⟨909, by decide⟩ : Fin 1902)) rp909_4 = true := by decide +kernel

theorem rp909_5_ok : RawF.check ctl A B pd i0 (raw (⟨909, by decide⟩ : Fin 1902)) rp909_5 = true := by decide +kernel

theorem raw909_h : ((raw (⟨909, by decide⟩ : Fin 1902)).ok (rawMin (⟨909, by decide⟩ : Fin 1902)) && chainF ((raw (⟨909, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp909.map (fun x => (x.lo, x.hi))) ((raw (⟨909, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp910_0_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_0 = true := by decide +kernel

theorem rp910_1_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_1 = true := by decide +kernel

theorem rp910_2_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_2 = true := by decide +kernel

theorem rp910_3_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_3 = true := by decide +kernel

theorem rp910_4_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_4 = true := by decide +kernel

theorem rp910_5_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_5 = true := by decide +kernel

theorem rp910_6_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_6 = true := by decide +kernel

theorem rp910_7_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_7 = true := by decide +kernel

theorem rp910_8_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_8 = true := by decide +kernel

theorem rp910_9_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_9 = true := by decide +kernel

theorem rp910_10_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_10 = true := by decide +kernel

theorem rp910_11_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_11 = true := by decide +kernel

theorem rp910_12_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_12 = true := by decide +kernel

theorem rp910_13_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_13 = true := by decide +kernel

theorem rp910_14_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_14 = true := by decide +kernel

theorem rp910_15_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_15 = true := by decide +kernel

theorem rp910_16_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_16 = true := by decide +kernel

theorem rp910_17_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_17 = true := by decide +kernel

theorem rp910_18_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_18 = true := by decide +kernel

theorem rp910_19_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_19 = true := by decide +kernel

theorem rp910_20_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_20 = true := by decide +kernel

theorem rp910_21_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_21 = true := by decide +kernel

theorem rp910_22_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_22 = true := by decide +kernel

theorem rp910_23_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_23 = true := by decide +kernel

theorem rp910_24_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_24 = true := by decide +kernel

theorem rp910_25_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_25 = true := by decide +kernel

theorem rp910_26_ok : RawF.check ctl A B pd i0 (raw (⟨910, by decide⟩ : Fin 1902)) rp910_26 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
