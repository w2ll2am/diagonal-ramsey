import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D39

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1202_0_ok : RawF.check ctl A B pd i0 (raw (⟨1202, by decide⟩ : Fin 1902)) rp1202_0 = true := by decide +kernel

theorem rp1202_1_ok : RawF.check ctl A B pd i0 (raw (⟨1202, by decide⟩ : Fin 1902)) rp1202_1 = true := by decide +kernel

theorem rp1202_2_ok : RawF.check ctl A B pd i0 (raw (⟨1202, by decide⟩ : Fin 1902)) rp1202_2 = true := by decide +kernel

theorem raw1202_h : ((raw (⟨1202, by decide⟩ : Fin 1902)).ok (rawMin (⟨1202, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1202, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1202.map (fun x => (x.lo, x.hi))) ((raw (⟨1202, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1203_0_ok : RawF.check ctl A B pd i0 (raw (⟨1203, by decide⟩ : Fin 1902)) rp1203_0 = true := by decide +kernel

theorem rp1203_1_ok : RawF.check ctl A B pd i0 (raw (⟨1203, by decide⟩ : Fin 1902)) rp1203_1 = true := by decide +kernel

theorem raw1203_h : ((raw (⟨1203, by decide⟩ : Fin 1902)).ok (rawMin (⟨1203, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1203, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1203.map (fun x => (x.lo, x.hi))) ((raw (⟨1203, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1204_0_ok : RawF.check ctl A B pd i0 (raw (⟨1204, by decide⟩ : Fin 1902)) rp1204_0 = true := by decide +kernel

theorem raw1204_h : ((raw (⟨1204, by decide⟩ : Fin 1902)).ok (rawMin (⟨1204, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1204, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1204.map (fun x => (x.lo, x.hi))) ((raw (⟨1204, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1205_0_ok : RawF.check ctl A B pd i0 (raw (⟨1205, by decide⟩ : Fin 1902)) rp1205_0 = true := by decide +kernel

theorem raw1205_h : ((raw (⟨1205, by decide⟩ : Fin 1902)).ok (rawMin (⟨1205, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1205, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1205.map (fun x => (x.lo, x.hi))) ((raw (⟨1205, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1206_0_ok : RawF.check ctl A B pd i0 (raw (⟨1206, by decide⟩ : Fin 1902)) rp1206_0 = true := by decide +kernel

theorem rp1206_1_ok : RawF.check ctl A B pd i0 (raw (⟨1206, by decide⟩ : Fin 1902)) rp1206_1 = true := by decide +kernel

theorem rp1206_2_ok : RawF.check ctl A B pd i0 (raw (⟨1206, by decide⟩ : Fin 1902)) rp1206_2 = true := by decide +kernel

theorem raw1206_h : ((raw (⟨1206, by decide⟩ : Fin 1902)).ok (rawMin (⟨1206, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1206, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1206.map (fun x => (x.lo, x.hi))) ((raw (⟨1206, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1207_0_ok : RawF.check ctl A B pd i0 (raw (⟨1207, by decide⟩ : Fin 1902)) rp1207_0 = true := by decide +kernel

theorem rp1207_1_ok : RawF.check ctl A B pd i0 (raw (⟨1207, by decide⟩ : Fin 1902)) rp1207_1 = true := by decide +kernel

theorem rp1207_2_ok : RawF.check ctl A B pd i0 (raw (⟨1207, by decide⟩ : Fin 1902)) rp1207_2 = true := by decide +kernel

theorem rp1207_3_ok : RawF.check ctl A B pd i0 (raw (⟨1207, by decide⟩ : Fin 1902)) rp1207_3 = true := by decide +kernel

theorem rp1207_4_ok : RawF.check ctl A B pd i0 (raw (⟨1207, by decide⟩ : Fin 1902)) rp1207_4 = true := by decide +kernel

theorem rp1207_5_ok : RawF.check ctl A B pd i0 (raw (⟨1207, by decide⟩ : Fin 1902)) rp1207_5 = true := by decide +kernel

theorem raw1207_h : ((raw (⟨1207, by decide⟩ : Fin 1902)).ok (rawMin (⟨1207, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1207, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1207.map (fun x => (x.lo, x.hi))) ((raw (⟨1207, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1208_0_ok : RawF.check ctl A B pd i0 (raw (⟨1208, by decide⟩ : Fin 1902)) rp1208_0 = true := by decide +kernel

theorem rp1208_1_ok : RawF.check ctl A B pd i0 (raw (⟨1208, by decide⟩ : Fin 1902)) rp1208_1 = true := by decide +kernel

theorem rp1208_2_ok : RawF.check ctl A B pd i0 (raw (⟨1208, by decide⟩ : Fin 1902)) rp1208_2 = true := by decide +kernel

theorem raw1208_h : ((raw (⟨1208, by decide⟩ : Fin 1902)).ok (rawMin (⟨1208, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1208, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1208.map (fun x => (x.lo, x.hi))) ((raw (⟨1208, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1209_0_ok : RawF.check ctl A B pd i0 (raw (⟨1209, by decide⟩ : Fin 1902)) rp1209_0 = true := by decide +kernel

theorem rp1209_1_ok : RawF.check ctl A B pd i0 (raw (⟨1209, by decide⟩ : Fin 1902)) rp1209_1 = true := by decide +kernel

theorem rp1209_2_ok : RawF.check ctl A B pd i0 (raw (⟨1209, by decide⟩ : Fin 1902)) rp1209_2 = true := by decide +kernel

theorem raw1209_h : ((raw (⟨1209, by decide⟩ : Fin 1902)).ok (rawMin (⟨1209, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1209, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1209.map (fun x => (x.lo, x.hi))) ((raw (⟨1209, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
