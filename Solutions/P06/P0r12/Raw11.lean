import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp44_2_ok : RawF.check ctl A B pd i0 (raw (⟨44, by decide⟩ : Fin 1902)) rp44_2 = true := by decide +kernel

theorem rp44_3_ok : RawF.check ctl A B pd i0 (raw (⟨44, by decide⟩ : Fin 1902)) rp44_3 = true := by decide +kernel

theorem rp44_4_ok : RawF.check ctl A B pd i0 (raw (⟨44, by decide⟩ : Fin 1902)) rp44_4 = true := by decide +kernel

theorem rp44_5_ok : RawF.check ctl A B pd i0 (raw (⟨44, by decide⟩ : Fin 1902)) rp44_5 = true := by decide +kernel

theorem rp44_6_ok : RawF.check ctl A B pd i0 (raw (⟨44, by decide⟩ : Fin 1902)) rp44_6 = true := by decide +kernel

theorem rp44_7_ok : RawF.check ctl A B pd i0 (raw (⟨44, by decide⟩ : Fin 1902)) rp44_7 = true := by decide +kernel

theorem raw44_h : ((raw (⟨44, by decide⟩ : Fin 1902)).ok (rawMin (⟨44, by decide⟩ : Fin 1902)) && chainF ((raw (⟨44, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp44.map (fun x => (x.lo, x.hi))) ((raw (⟨44, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp45_0_ok : RawF.check ctl A B pd i0 (raw (⟨45, by decide⟩ : Fin 1902)) rp45_0 = true := by decide +kernel

theorem raw45_h : ((raw (⟨45, by decide⟩ : Fin 1902)).ok (rawMin (⟨45, by decide⟩ : Fin 1902)) && chainF ((raw (⟨45, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp45.map (fun x => (x.lo, x.hi))) ((raw (⟨45, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp46_0_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_0 = true := by decide +kernel

theorem rp46_1_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_1 = true := by decide +kernel

theorem rp46_2_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_2 = true := by decide +kernel

theorem rp46_3_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_3 = true := by decide +kernel

theorem rp46_4_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_4 = true := by decide +kernel

theorem rp46_5_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_5 = true := by decide +kernel

theorem rp46_6_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_6 = true := by decide +kernel

theorem rp46_7_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_7 = true := by decide +kernel

theorem rp46_8_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_8 = true := by decide +kernel

theorem rp46_9_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_9 = true := by decide +kernel

theorem rp46_10_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_10 = true := by decide +kernel

theorem rp46_11_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_11 = true := by decide +kernel

theorem rp46_12_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_12 = true := by decide +kernel

theorem rp46_13_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_13 = true := by decide +kernel

theorem rp46_14_ok : RawF.check ctl A B pd i0 (raw (⟨46, by decide⟩ : Fin 1902)) rp46_14 = true := by decide +kernel

theorem raw46_h : ((raw (⟨46, by decide⟩ : Fin 1902)).ok (rawMin (⟨46, by decide⟩ : Fin 1902)) && chainF ((raw (⟨46, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp46.map (fun x => (x.lo, x.hi))) ((raw (⟨46, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp47_0_ok : RawF.check ctl A B pd i0 (raw (⟨47, by decide⟩ : Fin 1902)) rp47_0 = true := by decide +kernel

theorem rp47_1_ok : RawF.check ctl A B pd i0 (raw (⟨47, by decide⟩ : Fin 1902)) rp47_1 = true := by decide +kernel

theorem rp47_2_ok : RawF.check ctl A B pd i0 (raw (⟨47, by decide⟩ : Fin 1902)) rp47_2 = true := by decide +kernel

theorem rp47_3_ok : RawF.check ctl A B pd i0 (raw (⟨47, by decide⟩ : Fin 1902)) rp47_3 = true := by decide +kernel

theorem rp47_4_ok : RawF.check ctl A B pd i0 (raw (⟨47, by decide⟩ : Fin 1902)) rp47_4 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
