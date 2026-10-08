import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp94_29_ok : RawF.check ctl A B pd i0 (raw (⟨94, by decide⟩ : Fin 1902)) rp94_29 = true := by decide +kernel

theorem rp94_30_ok : RawF.check ctl A B pd i0 (raw (⟨94, by decide⟩ : Fin 1902)) rp94_30 = true := by decide +kernel

theorem raw94_h : ((raw (⟨94, by decide⟩ : Fin 1902)).ok (rawMin (⟨94, by decide⟩ : Fin 1902)) && chainF ((raw (⟨94, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp94.map (fun x => (x.lo, x.hi))) ((raw (⟨94, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp95_0_ok : RawF.check ctl A B pd i0 (raw (⟨95, by decide⟩ : Fin 1902)) rp95_0 = true := by decide +kernel

theorem rp95_1_ok : RawF.check ctl A B pd i0 (raw (⟨95, by decide⟩ : Fin 1902)) rp95_1 = true := by decide +kernel

theorem rp95_2_ok : RawF.check ctl A B pd i0 (raw (⟨95, by decide⟩ : Fin 1902)) rp95_2 = true := by decide +kernel

theorem rp95_3_ok : RawF.check ctl A B pd i0 (raw (⟨95, by decide⟩ : Fin 1902)) rp95_3 = true := by decide +kernel

theorem rp95_4_ok : RawF.check ctl A B pd i0 (raw (⟨95, by decide⟩ : Fin 1902)) rp95_4 = true := by decide +kernel

theorem rp95_5_ok : RawF.check ctl A B pd i0 (raw (⟨95, by decide⟩ : Fin 1902)) rp95_5 = true := by decide +kernel

theorem rp95_6_ok : RawF.check ctl A B pd i0 (raw (⟨95, by decide⟩ : Fin 1902)) rp95_6 = true := by decide +kernel

theorem rp95_7_ok : RawF.check ctl A B pd i0 (raw (⟨95, by decide⟩ : Fin 1902)) rp95_7 = true := by decide +kernel

theorem raw95_h : ((raw (⟨95, by decide⟩ : Fin 1902)).ok (rawMin (⟨95, by decide⟩ : Fin 1902)) && chainF ((raw (⟨95, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp95.map (fun x => (x.lo, x.hi))) ((raw (⟨95, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp96_0_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_0 = true := by decide +kernel

theorem rp96_1_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_1 = true := by decide +kernel

theorem rp96_2_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_2 = true := by decide +kernel

theorem rp96_3_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_3 = true := by decide +kernel

theorem rp96_4_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_4 = true := by decide +kernel

theorem rp96_5_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_5 = true := by decide +kernel

theorem rp96_6_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_6 = true := by decide +kernel

theorem rp96_7_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_7 = true := by decide +kernel

theorem rp96_8_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_8 = true := by decide +kernel

theorem rp96_9_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_9 = true := by decide +kernel

theorem rp96_10_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_10 = true := by decide +kernel

theorem rp96_11_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_11 = true := by decide +kernel

theorem rp96_12_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_12 = true := by decide +kernel

theorem rp96_13_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_13 = true := by decide +kernel

theorem rp96_14_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_14 = true := by decide +kernel

theorem rp96_15_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_15 = true := by decide +kernel

theorem rp96_16_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_16 = true := by decide +kernel

theorem rp96_17_ok : RawF.check ctl A B pd i0 (raw (⟨96, by decide⟩ : Fin 1902)) rp96_17 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
