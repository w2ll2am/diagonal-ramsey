import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp68_92_ok : RawF.check ctl A B pd i0 (raw (⟨68, by decide⟩ : Fin 1902)) rp68_92 = true := by decide +kernel

theorem rp68_93_ok : RawF.check ctl A B pd i0 (raw (⟨68, by decide⟩ : Fin 1902)) rp68_93 = true := by decide +kernel

theorem rp68_94_ok : RawF.check ctl A B pd i0 (raw (⟨68, by decide⟩ : Fin 1902)) rp68_94 = true := by decide +kernel

theorem raw68_h : ((raw (⟨68, by decide⟩ : Fin 1902)).ok (rawMin (⟨68, by decide⟩ : Fin 1902)) && chainF ((raw (⟨68, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp68.map (fun x => (x.lo, x.hi))) ((raw (⟨68, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp69_0_ok : RawF.check ctl A B pd i0 (raw (⟨69, by decide⟩ : Fin 1902)) rp69_0 = true := by decide +kernel

theorem rp69_1_ok : RawF.check ctl A B pd i0 (raw (⟨69, by decide⟩ : Fin 1902)) rp69_1 = true := by decide +kernel

theorem rp69_2_ok : RawF.check ctl A B pd i0 (raw (⟨69, by decide⟩ : Fin 1902)) rp69_2 = true := by decide +kernel

theorem rp69_3_ok : RawF.check ctl A B pd i0 (raw (⟨69, by decide⟩ : Fin 1902)) rp69_3 = true := by decide +kernel

theorem rp69_4_ok : RawF.check ctl A B pd i0 (raw (⟨69, by decide⟩ : Fin 1902)) rp69_4 = true := by decide +kernel

theorem rp69_5_ok : RawF.check ctl A B pd i0 (raw (⟨69, by decide⟩ : Fin 1902)) rp69_5 = true := by decide +kernel

theorem rp69_6_ok : RawF.check ctl A B pd i0 (raw (⟨69, by decide⟩ : Fin 1902)) rp69_6 = true := by decide +kernel

theorem raw69_h : ((raw (⟨69, by decide⟩ : Fin 1902)).ok (rawMin (⟨69, by decide⟩ : Fin 1902)) && chainF ((raw (⟨69, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp69.map (fun x => (x.lo, x.hi))) ((raw (⟨69, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp70_0_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_0 = true := by decide +kernel

theorem rp70_1_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_1 = true := by decide +kernel

theorem rp70_2_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_2 = true := by decide +kernel

theorem rp70_3_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_3 = true := by decide +kernel

theorem rp70_4_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_4 = true := by decide +kernel

theorem rp70_5_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_5 = true := by decide +kernel

theorem rp70_6_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_6 = true := by decide +kernel

theorem rp70_7_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_7 = true := by decide +kernel

theorem rp70_8_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_8 = true := by decide +kernel

theorem rp70_9_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_9 = true := by decide +kernel

theorem rp70_10_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_10 = true := by decide +kernel

theorem rp70_11_ok : RawF.check ctl A B pd i0 (raw (⟨70, by decide⟩ : Fin 1902)) rp70_11 = true := by decide +kernel

theorem raw70_h : ((raw (⟨70, by decide⟩ : Fin 1902)).ok (rawMin (⟨70, by decide⟩ : Fin 1902)) && chainF ((raw (⟨70, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp70.map (fun x => (x.lo, x.hi))) ((raw (⟨70, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp71_0_ok : RawF.check ctl A B pd i0 (raw (⟨71, by decide⟩ : Fin 1902)) rp71_0 = true := by decide +kernel

theorem rp71_1_ok : RawF.check ctl A B pd i0 (raw (⟨71, by decide⟩ : Fin 1902)) rp71_1 = true := by decide +kernel

theorem rp71_2_ok : RawF.check ctl A B pd i0 (raw (⟨71, by decide⟩ : Fin 1902)) rp71_2 = true := by decide +kernel

theorem rp71_3_ok : RawF.check ctl A B pd i0 (raw (⟨71, by decide⟩ : Fin 1902)) rp71_3 = true := by decide +kernel

theorem rp71_4_ok : RawF.check ctl A B pd i0 (raw (⟨71, by decide⟩ : Fin 1902)) rp71_4 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
