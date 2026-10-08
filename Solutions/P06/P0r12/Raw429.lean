import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D40
import Solutions.P06.P0r12.D41

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1217_2_ok : RawF.check ctl A B pd i0 (raw (⟨1217, by decide⟩ : Fin 1902)) rp1217_2 = true := by decide +kernel

theorem rp1217_3_ok : RawF.check ctl A B pd i0 (raw (⟨1217, by decide⟩ : Fin 1902)) rp1217_3 = true := by decide +kernel

theorem rp1217_4_ok : RawF.check ctl A B pd i0 (raw (⟨1217, by decide⟩ : Fin 1902)) rp1217_4 = true := by decide +kernel

theorem raw1217_h : ((raw (⟨1217, by decide⟩ : Fin 1902)).ok (rawMin (⟨1217, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1217, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1217.map (fun x => (x.lo, x.hi))) ((raw (⟨1217, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1218_0_ok : RawF.check ctl A B pd i0 (raw (⟨1218, by decide⟩ : Fin 1902)) rp1218_0 = true := by decide +kernel

theorem raw1218_h : ((raw (⟨1218, by decide⟩ : Fin 1902)).ok (rawMin (⟨1218, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1218, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1218.map (fun x => (x.lo, x.hi))) ((raw (⟨1218, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1219_0_ok : RawF.check ctl A B pd i0 (raw (⟨1219, by decide⟩ : Fin 1902)) rp1219_0 = true := by decide +kernel

theorem rp1219_1_ok : RawF.check ctl A B pd i0 (raw (⟨1219, by decide⟩ : Fin 1902)) rp1219_1 = true := by decide +kernel

theorem rp1219_2_ok : RawF.check ctl A B pd i0 (raw (⟨1219, by decide⟩ : Fin 1902)) rp1219_2 = true := by decide +kernel

theorem rp1219_3_ok : RawF.check ctl A B pd i0 (raw (⟨1219, by decide⟩ : Fin 1902)) rp1219_3 = true := by decide +kernel

theorem rp1219_4_ok : RawF.check ctl A B pd i0 (raw (⟨1219, by decide⟩ : Fin 1902)) rp1219_4 = true := by decide +kernel

theorem raw1219_h : ((raw (⟨1219, by decide⟩ : Fin 1902)).ok (rawMin (⟨1219, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1219, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1219.map (fun x => (x.lo, x.hi))) ((raw (⟨1219, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1220_0_ok : RawF.check ctl A B pd i0 (raw (⟨1220, by decide⟩ : Fin 1902)) rp1220_0 = true := by decide +kernel

theorem rp1220_1_ok : RawF.check ctl A B pd i0 (raw (⟨1220, by decide⟩ : Fin 1902)) rp1220_1 = true := by decide +kernel

theorem raw1220_h : ((raw (⟨1220, by decide⟩ : Fin 1902)).ok (rawMin (⟨1220, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1220, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1220.map (fun x => (x.lo, x.hi))) ((raw (⟨1220, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1221_0_ok : RawF.check ctl A B pd i0 (raw (⟨1221, by decide⟩ : Fin 1902)) rp1221_0 = true := by decide +kernel

theorem rp1221_1_ok : RawF.check ctl A B pd i0 (raw (⟨1221, by decide⟩ : Fin 1902)) rp1221_1 = true := by decide +kernel

theorem rp1221_2_ok : RawF.check ctl A B pd i0 (raw (⟨1221, by decide⟩ : Fin 1902)) rp1221_2 = true := by decide +kernel

theorem raw1221_h : ((raw (⟨1221, by decide⟩ : Fin 1902)).ok (rawMin (⟨1221, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1221, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1221.map (fun x => (x.lo, x.hi))) ((raw (⟨1221, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1222_0_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_0 = true := by decide +kernel

theorem rp1222_1_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_1 = true := by decide +kernel

theorem rp1222_2_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_2 = true := by decide +kernel

theorem rp1222_3_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_3 = true := by decide +kernel

theorem rp1222_4_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_4 = true := by decide +kernel

theorem rp1222_5_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_5 = true := by decide +kernel

theorem rp1222_6_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_6 = true := by decide +kernel

theorem rp1222_7_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_7 = true := by decide +kernel

theorem rp1222_8_ok : RawF.check ctl A B pd i0 (raw (⟨1222, by decide⟩ : Fin 1902)) rp1222_8 = true := by decide +kernel

theorem raw1222_h : ((raw (⟨1222, by decide⟩ : Fin 1902)).ok (rawMin (⟨1222, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1222, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1222.map (fun x => (x.lo, x.hi))) ((raw (⟨1222, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1223_0_ok : RawF.check ctl A B pd i0 (raw (⟨1223, by decide⟩ : Fin 1902)) rp1223_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
