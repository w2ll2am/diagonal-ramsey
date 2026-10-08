import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp800_0_ok : RawF.check ctl A B pd i0 (raw (⟨800, by decide⟩ : Fin 1902)) rp800_0 = true := by decide +kernel

theorem rp800_1_ok : RawF.check ctl A B pd i0 (raw (⟨800, by decide⟩ : Fin 1902)) rp800_1 = true := by decide +kernel

theorem rp800_2_ok : RawF.check ctl A B pd i0 (raw (⟨800, by decide⟩ : Fin 1902)) rp800_2 = true := by decide +kernel

theorem raw800_h : ((raw (⟨800, by decide⟩ : Fin 1902)).ok (rawMin (⟨800, by decide⟩ : Fin 1902)) && chainF ((raw (⟨800, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp800.map (fun x => (x.lo, x.hi))) ((raw (⟨800, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp801_0_ok : RawF.check ctl A B pd i0 (raw (⟨801, by decide⟩ : Fin 1902)) rp801_0 = true := by decide +kernel

theorem raw801_h : ((raw (⟨801, by decide⟩ : Fin 1902)).ok (rawMin (⟨801, by decide⟩ : Fin 1902)) && chainF ((raw (⟨801, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp801.map (fun x => (x.lo, x.hi))) ((raw (⟨801, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp802_0_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_0 = true := by decide +kernel

theorem rp802_1_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_1 = true := by decide +kernel

theorem rp802_2_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_2 = true := by decide +kernel

theorem rp802_3_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_3 = true := by decide +kernel

theorem rp802_4_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_4 = true := by decide +kernel

theorem rp802_5_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_5 = true := by decide +kernel

theorem rp802_6_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_6 = true := by decide +kernel

theorem rp802_7_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_7 = true := by decide +kernel

theorem rp802_8_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_8 = true := by decide +kernel

theorem rp802_9_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_9 = true := by decide +kernel

theorem rp802_10_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_10 = true := by decide +kernel

theorem rp802_11_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_11 = true := by decide +kernel

theorem rp802_12_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_12 = true := by decide +kernel

theorem rp802_13_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_13 = true := by decide +kernel

theorem rp802_14_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_14 = true := by decide +kernel

theorem rp802_15_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_15 = true := by decide +kernel

theorem rp802_16_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_16 = true := by decide +kernel

theorem rp802_17_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_17 = true := by decide +kernel

theorem rp802_18_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_18 = true := by decide +kernel

theorem rp802_19_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_19 = true := by decide +kernel

theorem rp802_20_ok : RawF.check ctl A B pd i0 (raw (⟨802, by decide⟩ : Fin 1902)) rp802_20 = true := by decide +kernel

theorem raw802_h : ((raw (⟨802, by decide⟩ : Fin 1902)).ok (rawMin (⟨802, by decide⟩ : Fin 1902)) && chainF ((raw (⟨802, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp802.map (fun x => (x.lo, x.hi))) ((raw (⟨802, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp803_0_ok : RawF.check ctl A B pd i0 (raw (⟨803, by decide⟩ : Fin 1902)) rp803_0 = true := by decide +kernel

theorem rp803_1_ok : RawF.check ctl A B pd i0 (raw (⟨803, by decide⟩ : Fin 1902)) rp803_1 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
