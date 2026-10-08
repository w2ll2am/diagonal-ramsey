import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D36

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1101_22_ok : RawF.check ctl A B pd i0 (raw (⟨1101, by decide⟩ : Fin 1902)) rp1101_22 = true := by decide +kernel

theorem rp1101_23_ok : RawF.check ctl A B pd i0 (raw (⟨1101, by decide⟩ : Fin 1902)) rp1101_23 = true := by decide +kernel

theorem rp1101_24_ok : RawF.check ctl A B pd i0 (raw (⟨1101, by decide⟩ : Fin 1902)) rp1101_24 = true := by decide +kernel

theorem rp1101_25_ok : RawF.check ctl A B pd i0 (raw (⟨1101, by decide⟩ : Fin 1902)) rp1101_25 = true := by decide +kernel

theorem rp1101_26_ok : RawF.check ctl A B pd i0 (raw (⟨1101, by decide⟩ : Fin 1902)) rp1101_26 = true := by decide +kernel

theorem raw1101_h : ((raw (⟨1101, by decide⟩ : Fin 1902)).ok (rawMin (⟨1101, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1101, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1101.map (fun x => (x.lo, x.hi))) ((raw (⟨1101, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1102_0_ok : RawF.check ctl A B pd i0 (raw (⟨1102, by decide⟩ : Fin 1902)) rp1102_0 = true := by decide +kernel

theorem rp1102_1_ok : RawF.check ctl A B pd i0 (raw (⟨1102, by decide⟩ : Fin 1902)) rp1102_1 = true := by decide +kernel

theorem rp1102_2_ok : RawF.check ctl A B pd i0 (raw (⟨1102, by decide⟩ : Fin 1902)) rp1102_2 = true := by decide +kernel

theorem rp1102_3_ok : RawF.check ctl A B pd i0 (raw (⟨1102, by decide⟩ : Fin 1902)) rp1102_3 = true := by decide +kernel

theorem rp1102_4_ok : RawF.check ctl A B pd i0 (raw (⟨1102, by decide⟩ : Fin 1902)) rp1102_4 = true := by decide +kernel

theorem raw1102_h : ((raw (⟨1102, by decide⟩ : Fin 1902)).ok (rawMin (⟨1102, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1102, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1102.map (fun x => (x.lo, x.hi))) ((raw (⟨1102, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1103_0_ok : RawF.check ctl A B pd i0 (raw (⟨1103, by decide⟩ : Fin 1902)) rp1103_0 = true := by decide +kernel

theorem rp1103_1_ok : RawF.check ctl A B pd i0 (raw (⟨1103, by decide⟩ : Fin 1902)) rp1103_1 = true := by decide +kernel

theorem raw1103_h : ((raw (⟨1103, by decide⟩ : Fin 1902)).ok (rawMin (⟨1103, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1103, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1103.map (fun x => (x.lo, x.hi))) ((raw (⟨1103, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1104_0_ok : RawF.check ctl A B pd i0 (raw (⟨1104, by decide⟩ : Fin 1902)) rp1104_0 = true := by decide +kernel

theorem raw1104_h : ((raw (⟨1104, by decide⟩ : Fin 1902)).ok (rawMin (⟨1104, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1104, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1104.map (fun x => (x.lo, x.hi))) ((raw (⟨1104, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1105_0_ok : RawF.check ctl A B pd i0 (raw (⟨1105, by decide⟩ : Fin 1902)) rp1105_0 = true := by decide +kernel

theorem rp1105_1_ok : RawF.check ctl A B pd i0 (raw (⟨1105, by decide⟩ : Fin 1902)) rp1105_1 = true := by decide +kernel

theorem raw1105_h : ((raw (⟨1105, by decide⟩ : Fin 1902)).ok (rawMin (⟨1105, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1105, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1105.map (fun x => (x.lo, x.hi))) ((raw (⟨1105, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1106_0_ok : RawF.check ctl A B pd i0 (raw (⟨1106, by decide⟩ : Fin 1902)) rp1106_0 = true := by decide +kernel

theorem raw1106_h : ((raw (⟨1106, by decide⟩ : Fin 1902)).ok (rawMin (⟨1106, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1106, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1106.map (fun x => (x.lo, x.hi))) ((raw (⟨1106, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1107_0_ok : RawF.check ctl A B pd i0 (raw (⟨1107, by decide⟩ : Fin 1902)) rp1107_0 = true := by decide +kernel

theorem raw1107_h : ((raw (⟨1107, by decide⟩ : Fin 1902)).ok (rawMin (⟨1107, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1107, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1107.map (fun x => (x.lo, x.hi))) ((raw (⟨1107, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1108_0_ok : RawF.check ctl A B pd i0 (raw (⟨1108, by decide⟩ : Fin 1902)) rp1108_0 = true := by decide +kernel

theorem rp1108_1_ok : RawF.check ctl A B pd i0 (raw (⟨1108, by decide⟩ : Fin 1902)) rp1108_1 = true := by decide +kernel

theorem raw1108_h : ((raw (⟨1108, by decide⟩ : Fin 1902)).ok (rawMin (⟨1108, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1108, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1108.map (fun x => (x.lo, x.hi))) ((raw (⟨1108, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1109_0_ok : RawF.check ctl A B pd i0 (raw (⟨1109, by decide⟩ : Fin 1902)) rp1109_0 = true := by decide +kernel

theorem rp1109_1_ok : RawF.check ctl A B pd i0 (raw (⟨1109, by decide⟩ : Fin 1902)) rp1109_1 = true := by decide +kernel

theorem rp1109_2_ok : RawF.check ctl A B pd i0 (raw (⟨1109, by decide⟩ : Fin 1902)) rp1109_2 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
