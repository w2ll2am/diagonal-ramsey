import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp13_0_ok : RawF.check ctl A B pd i0 (raw (⟨13, by decide⟩ : Fin 1902)) rp13_0 = true := by decide +kernel

theorem raw13_h : ((raw (⟨13, by decide⟩ : Fin 1902)).ok (rawMin (⟨13, by decide⟩ : Fin 1902)) && chainF ((raw (⟨13, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp13.map (fun x => (x.lo, x.hi))) ((raw (⟨13, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp14_0_ok : RawF.check ctl A B pd i0 (raw (⟨14, by decide⟩ : Fin 1902)) rp14_0 = true := by decide +kernel

theorem rp14_1_ok : RawF.check ctl A B pd i0 (raw (⟨14, by decide⟩ : Fin 1902)) rp14_1 = true := by decide +kernel

theorem raw14_h : ((raw (⟨14, by decide⟩ : Fin 1902)).ok (rawMin (⟨14, by decide⟩ : Fin 1902)) && chainF ((raw (⟨14, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp14.map (fun x => (x.lo, x.hi))) ((raw (⟨14, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp15_0_ok : RawF.check ctl A B pd i0 (raw (⟨15, by decide⟩ : Fin 1902)) rp15_0 = true := by decide +kernel

theorem raw15_h : ((raw (⟨15, by decide⟩ : Fin 1902)).ok (rawMin (⟨15, by decide⟩ : Fin 1902)) && chainF ((raw (⟨15, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp15.map (fun x => (x.lo, x.hi))) ((raw (⟨15, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp16_0_ok : RawF.check ctl A B pd i0 (raw (⟨16, by decide⟩ : Fin 1902)) rp16_0 = true := by decide +kernel

theorem raw16_h : ((raw (⟨16, by decide⟩ : Fin 1902)).ok (rawMin (⟨16, by decide⟩ : Fin 1902)) && chainF ((raw (⟨16, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp16.map (fun x => (x.lo, x.hi))) ((raw (⟨16, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp17_0_ok : RawF.check ctl A B pd i0 (raw (⟨17, by decide⟩ : Fin 1902)) rp17_0 = true := by decide +kernel

theorem rp17_1_ok : RawF.check ctl A B pd i0 (raw (⟨17, by decide⟩ : Fin 1902)) rp17_1 = true := by decide +kernel

theorem rp17_2_ok : RawF.check ctl A B pd i0 (raw (⟨17, by decide⟩ : Fin 1902)) rp17_2 = true := by decide +kernel

theorem raw17_h : ((raw (⟨17, by decide⟩ : Fin 1902)).ok (rawMin (⟨17, by decide⟩ : Fin 1902)) && chainF ((raw (⟨17, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp17.map (fun x => (x.lo, x.hi))) ((raw (⟨17, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp18_0_ok : RawF.check ctl A B pd i0 (raw (⟨18, by decide⟩ : Fin 1902)) rp18_0 = true := by decide +kernel

theorem rp18_1_ok : RawF.check ctl A B pd i0 (raw (⟨18, by decide⟩ : Fin 1902)) rp18_1 = true := by decide +kernel

theorem raw18_h : ((raw (⟨18, by decide⟩ : Fin 1902)).ok (rawMin (⟨18, by decide⟩ : Fin 1902)) && chainF ((raw (⟨18, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp18.map (fun x => (x.lo, x.hi))) ((raw (⟨18, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp19_0_ok : RawF.check ctl A B pd i0 (raw (⟨19, by decide⟩ : Fin 1902)) rp19_0 = true := by decide +kernel

theorem raw19_h : ((raw (⟨19, by decide⟩ : Fin 1902)).ok (rawMin (⟨19, by decide⟩ : Fin 1902)) && chainF ((raw (⟨19, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp19.map (fun x => (x.lo, x.hi))) ((raw (⟨19, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp20_0_ok : RawF.check ctl A B pd i0 (raw (⟨20, by decide⟩ : Fin 1902)) rp20_0 = true := by decide +kernel

theorem raw20_h : ((raw (⟨20, by decide⟩ : Fin 1902)).ok (rawMin (⟨20, by decide⟩ : Fin 1902)) && chainF ((raw (⟨20, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp20.map (fun x => (x.lo, x.hi))) ((raw (⟨20, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp21_0_ok : RawF.check ctl A B pd i0 (raw (⟨21, by decide⟩ : Fin 1902)) rp21_0 = true := by decide +kernel

theorem rp21_1_ok : RawF.check ctl A B pd i0 (raw (⟨21, by decide⟩ : Fin 1902)) rp21_1 = true := by decide +kernel

theorem raw21_h : ((raw (⟨21, by decide⟩ : Fin 1902)).ok (rawMin (⟨21, by decide⟩ : Fin 1902)) && chainF ((raw (⟨21, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp21.map (fun x => (x.lo, x.hi))) ((raw (⟨21, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp22_0_ok : RawF.check ctl A B pd i0 (raw (⟨22, by decide⟩ : Fin 1902)) rp22_0 = true := by decide +kernel

theorem rp22_1_ok : RawF.check ctl A B pd i0 (raw (⟨22, by decide⟩ : Fin 1902)) rp22_1 = true := by decide +kernel

theorem rp22_2_ok : RawF.check ctl A B pd i0 (raw (⟨22, by decide⟩ : Fin 1902)) rp22_2 = true := by decide +kernel

theorem raw22_h : ((raw (⟨22, by decide⟩ : Fin 1902)).ok (rawMin (⟨22, by decide⟩ : Fin 1902)) && chainF ((raw (⟨22, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp22.map (fun x => (x.lo, x.hi))) ((raw (⟨22, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp23_0_ok : RawF.check ctl A B pd i0 (raw (⟨23, by decide⟩ : Fin 1902)) rp23_0 = true := by decide +kernel

theorem rp23_1_ok : RawF.check ctl A B pd i0 (raw (⟨23, by decide⟩ : Fin 1902)) rp23_1 = true := by decide +kernel

theorem rp23_2_ok : RawF.check ctl A B pd i0 (raw (⟨23, by decide⟩ : Fin 1902)) rp23_2 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
