import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D39
import Solutions.P06.P0r12.D40

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1210_0_ok : RawF.check ctl A B pd i0 (raw (⟨1210, by decide⟩ : Fin 1902)) rp1210_0 = true := by decide +kernel

theorem rp1210_1_ok : RawF.check ctl A B pd i0 (raw (⟨1210, by decide⟩ : Fin 1902)) rp1210_1 = true := by decide +kernel

theorem rp1210_2_ok : RawF.check ctl A B pd i0 (raw (⟨1210, by decide⟩ : Fin 1902)) rp1210_2 = true := by decide +kernel

theorem raw1210_h : ((raw (⟨1210, by decide⟩ : Fin 1902)).ok (rawMin (⟨1210, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1210, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1210.map (fun x => (x.lo, x.hi))) ((raw (⟨1210, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1211_0_ok : RawF.check ctl A B pd i0 (raw (⟨1211, by decide⟩ : Fin 1902)) rp1211_0 = true := by decide +kernel

theorem rp1211_1_ok : RawF.check ctl A B pd i0 (raw (⟨1211, by decide⟩ : Fin 1902)) rp1211_1 = true := by decide +kernel

theorem rp1211_2_ok : RawF.check ctl A B pd i0 (raw (⟨1211, by decide⟩ : Fin 1902)) rp1211_2 = true := by decide +kernel

theorem raw1211_h : ((raw (⟨1211, by decide⟩ : Fin 1902)).ok (rawMin (⟨1211, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1211, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1211.map (fun x => (x.lo, x.hi))) ((raw (⟨1211, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1212_0_ok : RawF.check ctl A B pd i0 (raw (⟨1212, by decide⟩ : Fin 1902)) rp1212_0 = true := by decide +kernel

theorem rp1212_1_ok : RawF.check ctl A B pd i0 (raw (⟨1212, by decide⟩ : Fin 1902)) rp1212_1 = true := by decide +kernel

theorem rp1212_2_ok : RawF.check ctl A B pd i0 (raw (⟨1212, by decide⟩ : Fin 1902)) rp1212_2 = true := by decide +kernel

theorem raw1212_h : ((raw (⟨1212, by decide⟩ : Fin 1902)).ok (rawMin (⟨1212, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1212, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1212.map (fun x => (x.lo, x.hi))) ((raw (⟨1212, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1213_0_ok : RawF.check ctl A B pd i0 (raw (⟨1213, by decide⟩ : Fin 1902)) rp1213_0 = true := by decide +kernel

theorem rp1213_1_ok : RawF.check ctl A B pd i0 (raw (⟨1213, by decide⟩ : Fin 1902)) rp1213_1 = true := by decide +kernel

theorem raw1213_h : ((raw (⟨1213, by decide⟩ : Fin 1902)).ok (rawMin (⟨1213, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1213, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1213.map (fun x => (x.lo, x.hi))) ((raw (⟨1213, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1214_0_ok : RawF.check ctl A B pd i0 (raw (⟨1214, by decide⟩ : Fin 1902)) rp1214_0 = true := by decide +kernel

theorem rp1214_1_ok : RawF.check ctl A B pd i0 (raw (⟨1214, by decide⟩ : Fin 1902)) rp1214_1 = true := by decide +kernel

theorem rp1214_2_ok : RawF.check ctl A B pd i0 (raw (⟨1214, by decide⟩ : Fin 1902)) rp1214_2 = true := by decide +kernel

theorem rp1214_3_ok : RawF.check ctl A B pd i0 (raw (⟨1214, by decide⟩ : Fin 1902)) rp1214_3 = true := by decide +kernel

theorem rp1214_4_ok : RawF.check ctl A B pd i0 (raw (⟨1214, by decide⟩ : Fin 1902)) rp1214_4 = true := by decide +kernel

theorem rp1214_5_ok : RawF.check ctl A B pd i0 (raw (⟨1214, by decide⟩ : Fin 1902)) rp1214_5 = true := by decide +kernel

theorem raw1214_h : ((raw (⟨1214, by decide⟩ : Fin 1902)).ok (rawMin (⟨1214, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1214, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1214.map (fun x => (x.lo, x.hi))) ((raw (⟨1214, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1215_0_ok : RawF.check ctl A B pd i0 (raw (⟨1215, by decide⟩ : Fin 1902)) rp1215_0 = true := by decide +kernel

theorem raw1215_h : ((raw (⟨1215, by decide⟩ : Fin 1902)).ok (rawMin (⟨1215, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1215, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1215.map (fun x => (x.lo, x.hi))) ((raw (⟨1215, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1216_0_ok : RawF.check ctl A B pd i0 (raw (⟨1216, by decide⟩ : Fin 1902)) rp1216_0 = true := by decide +kernel

theorem rp1216_1_ok : RawF.check ctl A B pd i0 (raw (⟨1216, by decide⟩ : Fin 1902)) rp1216_1 = true := by decide +kernel

theorem rp1216_2_ok : RawF.check ctl A B pd i0 (raw (⟨1216, by decide⟩ : Fin 1902)) rp1216_2 = true := by decide +kernel

theorem raw1216_h : ((raw (⟨1216, by decide⟩ : Fin 1902)).ok (rawMin (⟨1216, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1216, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1216.map (fun x => (x.lo, x.hi))) ((raw (⟨1216, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1217_0_ok : RawF.check ctl A B pd i0 (raw (⟨1217, by decide⟩ : Fin 1902)) rp1217_0 = true := by decide +kernel

theorem rp1217_1_ok : RawF.check ctl A B pd i0 (raw (⟨1217, by decide⟩ : Fin 1902)) rp1217_1 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
