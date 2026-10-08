import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D32
import Solutions.P06.P0r12.D33

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1047_1_ok : RawF.check ctl A B pd i0 (raw (⟨1047, by decide⟩ : Fin 1902)) rp1047_1 = true := by decide +kernel

theorem rp1047_2_ok : RawF.check ctl A B pd i0 (raw (⟨1047, by decide⟩ : Fin 1902)) rp1047_2 = true := by decide +kernel

theorem rp1047_3_ok : RawF.check ctl A B pd i0 (raw (⟨1047, by decide⟩ : Fin 1902)) rp1047_3 = true := by decide +kernel

theorem raw1047_h : ((raw (⟨1047, by decide⟩ : Fin 1902)).ok (rawMin (⟨1047, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1047, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1047.map (fun x => (x.lo, x.hi))) ((raw (⟨1047, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1048_0_ok : RawF.check ctl A B pd i0 (raw (⟨1048, by decide⟩ : Fin 1902)) rp1048_0 = true := by decide +kernel

theorem rp1048_1_ok : RawF.check ctl A B pd i0 (raw (⟨1048, by decide⟩ : Fin 1902)) rp1048_1 = true := by decide +kernel

theorem raw1048_h : ((raw (⟨1048, by decide⟩ : Fin 1902)).ok (rawMin (⟨1048, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1048, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1048.map (fun x => (x.lo, x.hi))) ((raw (⟨1048, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1049_0_ok : RawF.check ctl A B pd i0 (raw (⟨1049, by decide⟩ : Fin 1902)) rp1049_0 = true := by decide +kernel

theorem rp1049_1_ok : RawF.check ctl A B pd i0 (raw (⟨1049, by decide⟩ : Fin 1902)) rp1049_1 = true := by decide +kernel

theorem rp1049_2_ok : RawF.check ctl A B pd i0 (raw (⟨1049, by decide⟩ : Fin 1902)) rp1049_2 = true := by decide +kernel

theorem rp1049_3_ok : RawF.check ctl A B pd i0 (raw (⟨1049, by decide⟩ : Fin 1902)) rp1049_3 = true := by decide +kernel

theorem raw1049_h : ((raw (⟨1049, by decide⟩ : Fin 1902)).ok (rawMin (⟨1049, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1049, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1049.map (fun x => (x.lo, x.hi))) ((raw (⟨1049, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1050_0_ok : RawF.check ctl A B pd i0 (raw (⟨1050, by decide⟩ : Fin 1902)) rp1050_0 = true := by decide +kernel

theorem raw1050_h : ((raw (⟨1050, by decide⟩ : Fin 1902)).ok (rawMin (⟨1050, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1050, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1050.map (fun x => (x.lo, x.hi))) ((raw (⟨1050, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1051_0_ok : RawF.check ctl A B pd i0 (raw (⟨1051, by decide⟩ : Fin 1902)) rp1051_0 = true := by decide +kernel

theorem rp1051_1_ok : RawF.check ctl A B pd i0 (raw (⟨1051, by decide⟩ : Fin 1902)) rp1051_1 = true := by decide +kernel

theorem raw1051_h : ((raw (⟨1051, by decide⟩ : Fin 1902)).ok (rawMin (⟨1051, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1051, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1051.map (fun x => (x.lo, x.hi))) ((raw (⟨1051, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1052_0_ok : RawF.check ctl A B pd i0 (raw (⟨1052, by decide⟩ : Fin 1902)) rp1052_0 = true := by decide +kernel

theorem rp1052_1_ok : RawF.check ctl A B pd i0 (raw (⟨1052, by decide⟩ : Fin 1902)) rp1052_1 = true := by decide +kernel

theorem rp1052_2_ok : RawF.check ctl A B pd i0 (raw (⟨1052, by decide⟩ : Fin 1902)) rp1052_2 = true := by decide +kernel

theorem rp1052_3_ok : RawF.check ctl A B pd i0 (raw (⟨1052, by decide⟩ : Fin 1902)) rp1052_3 = true := by decide +kernel

theorem rp1052_4_ok : RawF.check ctl A B pd i0 (raw (⟨1052, by decide⟩ : Fin 1902)) rp1052_4 = true := by decide +kernel

theorem rp1052_5_ok : RawF.check ctl A B pd i0 (raw (⟨1052, by decide⟩ : Fin 1902)) rp1052_5 = true := by decide +kernel

theorem rp1052_6_ok : RawF.check ctl A B pd i0 (raw (⟨1052, by decide⟩ : Fin 1902)) rp1052_6 = true := by decide +kernel

theorem raw1052_h : ((raw (⟨1052, by decide⟩ : Fin 1902)).ok (rawMin (⟨1052, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1052, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1052.map (fun x => (x.lo, x.hi))) ((raw (⟨1052, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1053_0_ok : RawF.check ctl A B pd i0 (raw (⟨1053, by decide⟩ : Fin 1902)) rp1053_0 = true := by decide +kernel

theorem raw1053_h : ((raw (⟨1053, by decide⟩ : Fin 1902)).ok (rawMin (⟨1053, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1053, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1053.map (fun x => (x.lo, x.hi))) ((raw (⟨1053, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1054_0_ok : RawF.check ctl A B pd i0 (raw (⟨1054, by decide⟩ : Fin 1902)) rp1054_0 = true := by decide +kernel

theorem raw1054_h : ((raw (⟨1054, by decide⟩ : Fin 1902)).ok (rawMin (⟨1054, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1054, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1054.map (fun x => (x.lo, x.hi))) ((raw (⟨1054, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1055_0_ok : RawF.check ctl A B pd i0 (raw (⟨1055, by decide⟩ : Fin 1902)) rp1055_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
