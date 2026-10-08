import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D27
import Solutions.P06.P0r12.D28

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1011_1_ok : RawF.check ctl A B pd i0 (raw (⟨1011, by decide⟩ : Fin 1902)) rp1011_1 = true := by decide +kernel

theorem raw1011_h : ((raw (⟨1011, by decide⟩ : Fin 1902)).ok (rawMin (⟨1011, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1011, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1011.map (fun x => (x.lo, x.hi))) ((raw (⟨1011, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1012_0_ok : RawF.check ctl A B pd i0 (raw (⟨1012, by decide⟩ : Fin 1902)) rp1012_0 = true := by decide +kernel

theorem raw1012_h : ((raw (⟨1012, by decide⟩ : Fin 1902)).ok (rawMin (⟨1012, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1012, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1012.map (fun x => (x.lo, x.hi))) ((raw (⟨1012, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1013_0_ok : RawF.check ctl A B pd i0 (raw (⟨1013, by decide⟩ : Fin 1902)) rp1013_0 = true := by decide +kernel

theorem rp1013_1_ok : RawF.check ctl A B pd i0 (raw (⟨1013, by decide⟩ : Fin 1902)) rp1013_1 = true := by decide +kernel

theorem rp1013_2_ok : RawF.check ctl A B pd i0 (raw (⟨1013, by decide⟩ : Fin 1902)) rp1013_2 = true := by decide +kernel

theorem rp1013_3_ok : RawF.check ctl A B pd i0 (raw (⟨1013, by decide⟩ : Fin 1902)) rp1013_3 = true := by decide +kernel

theorem raw1013_h : ((raw (⟨1013, by decide⟩ : Fin 1902)).ok (rawMin (⟨1013, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1013, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1013.map (fun x => (x.lo, x.hi))) ((raw (⟨1013, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1014_0_ok : RawF.check ctl A B pd i0 (raw (⟨1014, by decide⟩ : Fin 1902)) rp1014_0 = true := by decide +kernel

theorem rp1014_1_ok : RawF.check ctl A B pd i0 (raw (⟨1014, by decide⟩ : Fin 1902)) rp1014_1 = true := by decide +kernel

theorem raw1014_h : ((raw (⟨1014, by decide⟩ : Fin 1902)).ok (rawMin (⟨1014, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1014, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1014.map (fun x => (x.lo, x.hi))) ((raw (⟨1014, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1015_0_ok : RawF.check ctl A B pd i0 (raw (⟨1015, by decide⟩ : Fin 1902)) rp1015_0 = true := by decide +kernel

theorem rp1015_1_ok : RawF.check ctl A B pd i0 (raw (⟨1015, by decide⟩ : Fin 1902)) rp1015_1 = true := by decide +kernel

theorem rp1015_2_ok : RawF.check ctl A B pd i0 (raw (⟨1015, by decide⟩ : Fin 1902)) rp1015_2 = true := by decide +kernel

theorem raw1015_h : ((raw (⟨1015, by decide⟩ : Fin 1902)).ok (rawMin (⟨1015, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1015, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1015.map (fun x => (x.lo, x.hi))) ((raw (⟨1015, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1016_0_ok : RawF.check ctl A B pd i0 (raw (⟨1016, by decide⟩ : Fin 1902)) rp1016_0 = true := by decide +kernel

theorem rp1016_1_ok : RawF.check ctl A B pd i0 (raw (⟨1016, by decide⟩ : Fin 1902)) rp1016_1 = true := by decide +kernel

theorem raw1016_h : ((raw (⟨1016, by decide⟩ : Fin 1902)).ok (rawMin (⟨1016, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1016, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1016.map (fun x => (x.lo, x.hi))) ((raw (⟨1016, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1017_0_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_0 = true := by decide +kernel

theorem rp1017_1_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_1 = true := by decide +kernel

theorem rp1017_2_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_2 = true := by decide +kernel

theorem rp1017_3_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_3 = true := by decide +kernel

theorem rp1017_4_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_4 = true := by decide +kernel

theorem rp1017_5_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_5 = true := by decide +kernel

theorem rp1017_6_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_6 = true := by decide +kernel

theorem rp1017_7_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_7 = true := by decide +kernel

theorem rp1017_8_ok : RawF.check ctl A B pd i0 (raw (⟨1017, by decide⟩ : Fin 1902)) rp1017_8 = true := by decide +kernel

theorem raw1017_h : ((raw (⟨1017, by decide⟩ : Fin 1902)).ok (rawMin (⟨1017, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1017, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1017.map (fun x => (x.lo, x.hi))) ((raw (⟨1017, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1018_0_ok : RawF.check ctl A B pd i0 (raw (⟨1018, by decide⟩ : Fin 1902)) rp1018_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
