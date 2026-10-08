import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D8

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp495_1_ok : RawF.check ctl A B pd i0 (raw (⟨495, by decide⟩ : Fin 1902)) rp495_1 = true := by decide +kernel

theorem rp495_2_ok : RawF.check ctl A B pd i0 (raw (⟨495, by decide⟩ : Fin 1902)) rp495_2 = true := by decide +kernel

theorem raw495_h : ((raw (⟨495, by decide⟩ : Fin 1902)).ok (rawMin (⟨495, by decide⟩ : Fin 1902)) && chainF ((raw (⟨495, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp495.map (fun x => (x.lo, x.hi))) ((raw (⟨495, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp496_0_ok : RawF.check ctl A B pd i0 (raw (⟨496, by decide⟩ : Fin 1902)) rp496_0 = true := by decide +kernel

theorem rp496_1_ok : RawF.check ctl A B pd i0 (raw (⟨496, by decide⟩ : Fin 1902)) rp496_1 = true := by decide +kernel

theorem raw496_h : ((raw (⟨496, by decide⟩ : Fin 1902)).ok (rawMin (⟨496, by decide⟩ : Fin 1902)) && chainF ((raw (⟨496, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp496.map (fun x => (x.lo, x.hi))) ((raw (⟨496, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp497_0_ok : RawF.check ctl A B pd i0 (raw (⟨497, by decide⟩ : Fin 1902)) rp497_0 = true := by decide +kernel

theorem rp497_1_ok : RawF.check ctl A B pd i0 (raw (⟨497, by decide⟩ : Fin 1902)) rp497_1 = true := by decide +kernel

theorem rp497_2_ok : RawF.check ctl A B pd i0 (raw (⟨497, by decide⟩ : Fin 1902)) rp497_2 = true := by decide +kernel

theorem rp497_3_ok : RawF.check ctl A B pd i0 (raw (⟨497, by decide⟩ : Fin 1902)) rp497_3 = true := by decide +kernel

theorem raw497_h : ((raw (⟨497, by decide⟩ : Fin 1902)).ok (rawMin (⟨497, by decide⟩ : Fin 1902)) && chainF ((raw (⟨497, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp497.map (fun x => (x.lo, x.hi))) ((raw (⟨497, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp498_0_ok : RawF.check ctl A B pd i0 (raw (⟨498, by decide⟩ : Fin 1902)) rp498_0 = true := by decide +kernel

theorem rp498_1_ok : RawF.check ctl A B pd i0 (raw (⟨498, by decide⟩ : Fin 1902)) rp498_1 = true := by decide +kernel

theorem rp498_2_ok : RawF.check ctl A B pd i0 (raw (⟨498, by decide⟩ : Fin 1902)) rp498_2 = true := by decide +kernel

theorem rp498_3_ok : RawF.check ctl A B pd i0 (raw (⟨498, by decide⟩ : Fin 1902)) rp498_3 = true := by decide +kernel

theorem raw498_h : ((raw (⟨498, by decide⟩ : Fin 1902)).ok (rawMin (⟨498, by decide⟩ : Fin 1902)) && chainF ((raw (⟨498, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp498.map (fun x => (x.lo, x.hi))) ((raw (⟨498, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp499_0_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_0 = true := by decide +kernel

theorem rp499_1_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_1 = true := by decide +kernel

theorem rp499_2_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_2 = true := by decide +kernel

theorem rp499_3_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_3 = true := by decide +kernel

theorem rp499_4_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_4 = true := by decide +kernel

theorem rp499_5_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_5 = true := by decide +kernel

theorem rp499_6_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_6 = true := by decide +kernel

theorem rp499_7_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_7 = true := by decide +kernel

theorem rp499_8_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_8 = true := by decide +kernel

theorem rp499_9_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_9 = true := by decide +kernel

theorem rp499_10_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_10 = true := by decide +kernel

theorem rp499_11_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_11 = true := by decide +kernel

theorem rp499_12_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_12 = true := by decide +kernel

theorem rp499_13_ok : RawF.check ctl A B pd i0 (raw (⟨499, by decide⟩ : Fin 1902)) rp499_13 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
