import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp706_1_ok : RawF.check ctl A B pd i0 (raw (⟨706, by decide⟩ : Fin 1902)) rp706_1 = true := by decide +kernel

theorem rp706_2_ok : RawF.check ctl A B pd i0 (raw (⟨706, by decide⟩ : Fin 1902)) rp706_2 = true := by decide +kernel

theorem raw706_h : ((raw (⟨706, by decide⟩ : Fin 1902)).ok (rawMin (⟨706, by decide⟩ : Fin 1902)) && chainF ((raw (⟨706, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp706.map (fun x => (x.lo, x.hi))) ((raw (⟨706, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp707_0_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_0 = true := by decide +kernel

theorem rp707_1_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_1 = true := by decide +kernel

theorem rp707_2_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_2 = true := by decide +kernel

theorem rp707_3_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_3 = true := by decide +kernel

theorem rp707_4_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_4 = true := by decide +kernel

theorem rp707_5_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_5 = true := by decide +kernel

theorem rp707_6_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_6 = true := by decide +kernel

theorem rp707_7_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_7 = true := by decide +kernel

theorem rp707_8_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_8 = true := by decide +kernel

theorem rp707_9_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_9 = true := by decide +kernel

theorem rp707_10_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_10 = true := by decide +kernel

theorem rp707_11_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_11 = true := by decide +kernel

theorem rp707_12_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_12 = true := by decide +kernel

theorem rp707_13_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_13 = true := by decide +kernel

theorem rp707_14_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_14 = true := by decide +kernel

theorem rp707_15_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_15 = true := by decide +kernel

theorem rp707_16_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_16 = true := by decide +kernel

theorem rp707_17_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_17 = true := by decide +kernel

theorem rp707_18_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_18 = true := by decide +kernel

theorem rp707_19_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_19 = true := by decide +kernel

theorem rp707_20_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_20 = true := by decide +kernel

theorem rp707_21_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_21 = true := by decide +kernel

theorem rp707_22_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_22 = true := by decide +kernel

theorem rp707_23_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_23 = true := by decide +kernel

theorem rp707_24_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_24 = true := by decide +kernel

theorem rp707_25_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_25 = true := by decide +kernel

theorem rp707_26_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_26 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
