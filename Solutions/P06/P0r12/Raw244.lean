import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D16
import Solutions.P06.P0r12.D17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp720_4_ok : RawF.check ctl A B pd i0 (raw (⟨720, by decide⟩ : Fin 1902)) rp720_4 = true := by decide +kernel

theorem rp720_5_ok : RawF.check ctl A B pd i0 (raw (⟨720, by decide⟩ : Fin 1902)) rp720_5 = true := by decide +kernel

theorem rp720_6_ok : RawF.check ctl A B pd i0 (raw (⟨720, by decide⟩ : Fin 1902)) rp720_6 = true := by decide +kernel

theorem raw720_h : ((raw (⟨720, by decide⟩ : Fin 1902)).ok (rawMin (⟨720, by decide⟩ : Fin 1902)) && chainF ((raw (⟨720, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp720.map (fun x => (x.lo, x.hi))) ((raw (⟨720, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp721_0_ok : RawF.check ctl A B pd i0 (raw (⟨721, by decide⟩ : Fin 1902)) rp721_0 = true := by decide +kernel

theorem raw721_h : ((raw (⟨721, by decide⟩ : Fin 1902)).ok (rawMin (⟨721, by decide⟩ : Fin 1902)) && chainF ((raw (⟨721, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp721.map (fun x => (x.lo, x.hi))) ((raw (⟨721, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp722_0_ok : RawF.check ctl A B pd i0 (raw (⟨722, by decide⟩ : Fin 1902)) rp722_0 = true := by decide +kernel

theorem rp722_1_ok : RawF.check ctl A B pd i0 (raw (⟨722, by decide⟩ : Fin 1902)) rp722_1 = true := by decide +kernel

theorem rp722_2_ok : RawF.check ctl A B pd i0 (raw (⟨722, by decide⟩ : Fin 1902)) rp722_2 = true := by decide +kernel

theorem raw722_h : ((raw (⟨722, by decide⟩ : Fin 1902)).ok (rawMin (⟨722, by decide⟩ : Fin 1902)) && chainF ((raw (⟨722, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp722.map (fun x => (x.lo, x.hi))) ((raw (⟨722, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp723_0_ok : RawF.check ctl A B pd i0 (raw (⟨723, by decide⟩ : Fin 1902)) rp723_0 = true := by decide +kernel

theorem raw723_h : ((raw (⟨723, by decide⟩ : Fin 1902)).ok (rawMin (⟨723, by decide⟩ : Fin 1902)) && chainF ((raw (⟨723, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp723.map (fun x => (x.lo, x.hi))) ((raw (⟨723, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp724_0_ok : RawF.check ctl A B pd i0 (raw (⟨724, by decide⟩ : Fin 1902)) rp724_0 = true := by decide +kernel

theorem rp724_1_ok : RawF.check ctl A B pd i0 (raw (⟨724, by decide⟩ : Fin 1902)) rp724_1 = true := by decide +kernel

theorem raw724_h : ((raw (⟨724, by decide⟩ : Fin 1902)).ok (rawMin (⟨724, by decide⟩ : Fin 1902)) && chainF ((raw (⟨724, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp724.map (fun x => (x.lo, x.hi))) ((raw (⟨724, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp725_0_ok : RawF.check ctl A B pd i0 (raw (⟨725, by decide⟩ : Fin 1902)) rp725_0 = true := by decide +kernel

theorem raw725_h : ((raw (⟨725, by decide⟩ : Fin 1902)).ok (rawMin (⟨725, by decide⟩ : Fin 1902)) && chainF ((raw (⟨725, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp725.map (fun x => (x.lo, x.hi))) ((raw (⟨725, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp726_0_ok : RawF.check ctl A B pd i0 (raw (⟨726, by decide⟩ : Fin 1902)) rp726_0 = true := by decide +kernel

theorem rp726_1_ok : RawF.check ctl A B pd i0 (raw (⟨726, by decide⟩ : Fin 1902)) rp726_1 = true := by decide +kernel

theorem rp726_2_ok : RawF.check ctl A B pd i0 (raw (⟨726, by decide⟩ : Fin 1902)) rp726_2 = true := by decide +kernel

theorem rp726_3_ok : RawF.check ctl A B pd i0 (raw (⟨726, by decide⟩ : Fin 1902)) rp726_3 = true := by decide +kernel

theorem raw726_h : ((raw (⟨726, by decide⟩ : Fin 1902)).ok (rawMin (⟨726, by decide⟩ : Fin 1902)) && chainF ((raw (⟨726, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp726.map (fun x => (x.lo, x.hi))) ((raw (⟨726, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp727_0_ok : RawF.check ctl A B pd i0 (raw (⟨727, by decide⟩ : Fin 1902)) rp727_0 = true := by decide +kernel

theorem rp727_1_ok : RawF.check ctl A B pd i0 (raw (⟨727, by decide⟩ : Fin 1902)) rp727_1 = true := by decide +kernel

theorem rp727_2_ok : RawF.check ctl A B pd i0 (raw (⟨727, by decide⟩ : Fin 1902)) rp727_2 = true := by decide +kernel

theorem rp727_3_ok : RawF.check ctl A B pd i0 (raw (⟨727, by decide⟩ : Fin 1902)) rp727_3 = true := by decide +kernel

theorem rp727_4_ok : RawF.check ctl A B pd i0 (raw (⟨727, by decide⟩ : Fin 1902)) rp727_4 = true := by decide +kernel

theorem rp727_5_ok : RawF.check ctl A B pd i0 (raw (⟨727, by decide⟩ : Fin 1902)) rp727_5 = true := by decide +kernel

theorem rp727_6_ok : RawF.check ctl A B pd i0 (raw (⟨727, by decide⟩ : Fin 1902)) rp727_6 = true := by decide +kernel

theorem rp727_7_ok : RawF.check ctl A B pd i0 (raw (⟨727, by decide⟩ : Fin 1902)) rp727_7 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
