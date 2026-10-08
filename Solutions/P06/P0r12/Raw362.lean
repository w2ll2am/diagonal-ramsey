import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D26
import Solutions.P06.P0r12.D27

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1005_2_ok : RawF.check ctl A B pd i0 (raw (⟨1005, by decide⟩ : Fin 1902)) rp1005_2 = true := by decide +kernel

theorem rp1005_3_ok : RawF.check ctl A B pd i0 (raw (⟨1005, by decide⟩ : Fin 1902)) rp1005_3 = true := by decide +kernel

theorem rp1005_4_ok : RawF.check ctl A B pd i0 (raw (⟨1005, by decide⟩ : Fin 1902)) rp1005_4 = true := by decide +kernel

theorem rp1005_5_ok : RawF.check ctl A B pd i0 (raw (⟨1005, by decide⟩ : Fin 1902)) rp1005_5 = true := by decide +kernel

theorem rp1005_6_ok : RawF.check ctl A B pd i0 (raw (⟨1005, by decide⟩ : Fin 1902)) rp1005_6 = true := by decide +kernel

theorem rp1005_7_ok : RawF.check ctl A B pd i0 (raw (⟨1005, by decide⟩ : Fin 1902)) rp1005_7 = true := by decide +kernel

theorem raw1005_h : ((raw (⟨1005, by decide⟩ : Fin 1902)).ok (rawMin (⟨1005, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1005, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1005.map (fun x => (x.lo, x.hi))) ((raw (⟨1005, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1006_0_ok : RawF.check ctl A B pd i0 (raw (⟨1006, by decide⟩ : Fin 1902)) rp1006_0 = true := by decide +kernel

theorem rp1006_1_ok : RawF.check ctl A B pd i0 (raw (⟨1006, by decide⟩ : Fin 1902)) rp1006_1 = true := by decide +kernel

theorem rp1006_2_ok : RawF.check ctl A B pd i0 (raw (⟨1006, by decide⟩ : Fin 1902)) rp1006_2 = true := by decide +kernel

theorem raw1006_h : ((raw (⟨1006, by decide⟩ : Fin 1902)).ok (rawMin (⟨1006, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1006, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1006.map (fun x => (x.lo, x.hi))) ((raw (⟨1006, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1007_0_ok : RawF.check ctl A B pd i0 (raw (⟨1007, by decide⟩ : Fin 1902)) rp1007_0 = true := by decide +kernel

theorem rp1007_1_ok : RawF.check ctl A B pd i0 (raw (⟨1007, by decide⟩ : Fin 1902)) rp1007_1 = true := by decide +kernel

theorem rp1007_2_ok : RawF.check ctl A B pd i0 (raw (⟨1007, by decide⟩ : Fin 1902)) rp1007_2 = true := by decide +kernel

theorem rp1007_3_ok : RawF.check ctl A B pd i0 (raw (⟨1007, by decide⟩ : Fin 1902)) rp1007_3 = true := by decide +kernel

theorem raw1007_h : ((raw (⟨1007, by decide⟩ : Fin 1902)).ok (rawMin (⟨1007, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1007, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1007.map (fun x => (x.lo, x.hi))) ((raw (⟨1007, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1008_0_ok : RawF.check ctl A B pd i0 (raw (⟨1008, by decide⟩ : Fin 1902)) rp1008_0 = true := by decide +kernel

theorem rp1008_1_ok : RawF.check ctl A B pd i0 (raw (⟨1008, by decide⟩ : Fin 1902)) rp1008_1 = true := by decide +kernel

theorem rp1008_2_ok : RawF.check ctl A B pd i0 (raw (⟨1008, by decide⟩ : Fin 1902)) rp1008_2 = true := by decide +kernel

theorem raw1008_h : ((raw (⟨1008, by decide⟩ : Fin 1902)).ok (rawMin (⟨1008, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1008, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1008.map (fun x => (x.lo, x.hi))) ((raw (⟨1008, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1009_0_ok : RawF.check ctl A B pd i0 (raw (⟨1009, by decide⟩ : Fin 1902)) rp1009_0 = true := by decide +kernel

theorem rp1009_1_ok : RawF.check ctl A B pd i0 (raw (⟨1009, by decide⟩ : Fin 1902)) rp1009_1 = true := by decide +kernel

theorem rp1009_2_ok : RawF.check ctl A B pd i0 (raw (⟨1009, by decide⟩ : Fin 1902)) rp1009_2 = true := by decide +kernel

theorem rp1009_3_ok : RawF.check ctl A B pd i0 (raw (⟨1009, by decide⟩ : Fin 1902)) rp1009_3 = true := by decide +kernel

theorem raw1009_h : ((raw (⟨1009, by decide⟩ : Fin 1902)).ok (rawMin (⟨1009, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1009, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1009.map (fun x => (x.lo, x.hi))) ((raw (⟨1009, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1010_0_ok : RawF.check ctl A B pd i0 (raw (⟨1010, by decide⟩ : Fin 1902)) rp1010_0 = true := by decide +kernel

theorem rp1010_1_ok : RawF.check ctl A B pd i0 (raw (⟨1010, by decide⟩ : Fin 1902)) rp1010_1 = true := by decide +kernel

theorem rp1010_2_ok : RawF.check ctl A B pd i0 (raw (⟨1010, by decide⟩ : Fin 1902)) rp1010_2 = true := by decide +kernel

theorem raw1010_h : ((raw (⟨1010, by decide⟩ : Fin 1902)).ok (rawMin (⟨1010, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1010, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1010.map (fun x => (x.lo, x.hi))) ((raw (⟨1010, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1011_0_ok : RawF.check ctl A B pd i0 (raw (⟨1011, by decide⟩ : Fin 1902)) rp1011_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
