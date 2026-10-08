import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp119_8_ok : RawF.check ctl A B pd i0 (raw (⟨119, by decide⟩ : Fin 1902)) rp119_8 = true := by decide +kernel

theorem rp119_9_ok : RawF.check ctl A B pd i0 (raw (⟨119, by decide⟩ : Fin 1902)) rp119_9 = true := by decide +kernel

theorem rp119_10_ok : RawF.check ctl A B pd i0 (raw (⟨119, by decide⟩ : Fin 1902)) rp119_10 = true := by decide +kernel

theorem rp119_11_ok : RawF.check ctl A B pd i0 (raw (⟨119, by decide⟩ : Fin 1902)) rp119_11 = true := by decide +kernel

theorem rp119_12_ok : RawF.check ctl A B pd i0 (raw (⟨119, by decide⟩ : Fin 1902)) rp119_12 = true := by decide +kernel

theorem raw119_h : ((raw (⟨119, by decide⟩ : Fin 1902)).ok (rawMin (⟨119, by decide⟩ : Fin 1902)) && chainF ((raw (⟨119, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp119.map (fun x => (x.lo, x.hi))) ((raw (⟨119, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp120_0_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_0 = true := by decide +kernel

theorem rp120_1_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_1 = true := by decide +kernel

theorem rp120_2_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_2 = true := by decide +kernel

theorem rp120_3_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_3 = true := by decide +kernel

theorem rp120_4_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_4 = true := by decide +kernel

theorem rp120_5_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_5 = true := by decide +kernel

theorem rp120_6_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_6 = true := by decide +kernel

theorem rp120_7_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_7 = true := by decide +kernel

theorem rp120_8_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_8 = true := by decide +kernel

theorem rp120_9_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_9 = true := by decide +kernel

theorem rp120_10_ok : RawF.check ctl A B pd i0 (raw (⟨120, by decide⟩ : Fin 1902)) rp120_10 = true := by decide +kernel

theorem raw120_h : ((raw (⟨120, by decide⟩ : Fin 1902)).ok (rawMin (⟨120, by decide⟩ : Fin 1902)) && chainF ((raw (⟨120, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp120.map (fun x => (x.lo, x.hi))) ((raw (⟨120, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp121_0_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_0 = true := by decide +kernel

theorem rp121_1_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_1 = true := by decide +kernel

theorem rp121_2_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_2 = true := by decide +kernel

theorem rp121_3_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_3 = true := by decide +kernel

theorem rp121_4_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_4 = true := by decide +kernel

theorem rp121_5_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_5 = true := by decide +kernel

theorem rp121_6_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_6 = true := by decide +kernel

theorem rp121_7_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_7 = true := by decide +kernel

theorem rp121_8_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_8 = true := by decide +kernel

theorem rp121_9_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_9 = true := by decide +kernel

theorem rp121_10_ok : RawF.check ctl A B pd i0 (raw (⟨121, by decide⟩ : Fin 1902)) rp121_10 = true := by decide +kernel

theorem raw121_h : ((raw (⟨121, by decide⟩ : Fin 1902)).ok (rawMin (⟨121, by decide⟩ : Fin 1902)) && chainF ((raw (⟨121, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp121.map (fun x => (x.lo, x.hi))) ((raw (⟨121, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
