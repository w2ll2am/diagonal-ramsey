import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp489_29_ok : RawF.check ctl A B pd i0 (raw (⟨489, by decide⟩ : Fin 1902)) rp489_29 = true := by decide +kernel

theorem rp489_30_ok : RawF.check ctl A B pd i0 (raw (⟨489, by decide⟩ : Fin 1902)) rp489_30 = true := by decide +kernel

theorem raw489_h : ((raw (⟨489, by decide⟩ : Fin 1902)).ok (rawMin (⟨489, by decide⟩ : Fin 1902)) && chainF ((raw (⟨489, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp489.map (fun x => (x.lo, x.hi))) ((raw (⟨489, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp490_0_ok : RawF.check ctl A B pd i0 (raw (⟨490, by decide⟩ : Fin 1902)) rp490_0 = true := by decide +kernel

theorem raw490_h : ((raw (⟨490, by decide⟩ : Fin 1902)).ok (rawMin (⟨490, by decide⟩ : Fin 1902)) && chainF ((raw (⟨490, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp490.map (fun x => (x.lo, x.hi))) ((raw (⟨490, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp491_0_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_0 = true := by decide +kernel

theorem rp491_1_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_1 = true := by decide +kernel

theorem rp491_2_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_2 = true := by decide +kernel

theorem rp491_3_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_3 = true := by decide +kernel

theorem rp491_4_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_4 = true := by decide +kernel

theorem rp491_5_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_5 = true := by decide +kernel

theorem rp491_6_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_6 = true := by decide +kernel

theorem rp491_7_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_7 = true := by decide +kernel

theorem rp491_8_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_8 = true := by decide +kernel

theorem rp491_9_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_9 = true := by decide +kernel

theorem rp491_10_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_10 = true := by decide +kernel

theorem rp491_11_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_11 = true := by decide +kernel

theorem rp491_12_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_12 = true := by decide +kernel

theorem rp491_13_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_13 = true := by decide +kernel

theorem rp491_14_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_14 = true := by decide +kernel

theorem rp491_15_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_15 = true := by decide +kernel

theorem rp491_16_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_16 = true := by decide +kernel

theorem rp491_17_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_17 = true := by decide +kernel

theorem rp491_18_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_18 = true := by decide +kernel

theorem rp491_19_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_19 = true := by decide +kernel

theorem rp491_20_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_20 = true := by decide +kernel

theorem rp491_21_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_21 = true := by decide +kernel

theorem rp491_22_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_22 = true := by decide +kernel

theorem rp491_23_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_23 = true := by decide +kernel

theorem rp491_24_ok : RawF.check ctl A B pd i0 (raw (⟨491, by decide⟩ : Fin 1902)) rp491_24 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
