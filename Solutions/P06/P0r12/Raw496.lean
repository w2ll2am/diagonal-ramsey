import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D50
import Solutions.P06.P0r12.D51

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1400_12_ok : RawF.check ctl A B pd i0 (raw (⟨1400, by decide⟩ : Fin 1902)) rp1400_12 = true := by decide +kernel

theorem rp1400_13_ok : RawF.check ctl A B pd i0 (raw (⟨1400, by decide⟩ : Fin 1902)) rp1400_13 = true := by decide +kernel

theorem raw1400_h : ((raw (⟨1400, by decide⟩ : Fin 1902)).ok (rawMin (⟨1400, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1400, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1400.map (fun x => (x.lo, x.hi))) ((raw (⟨1400, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1401_0_ok : RawF.check ctl A B pd i0 (raw (⟨1401, by decide⟩ : Fin 1902)) rp1401_0 = true := by decide +kernel

theorem rp1401_1_ok : RawF.check ctl A B pd i0 (raw (⟨1401, by decide⟩ : Fin 1902)) rp1401_1 = true := by decide +kernel

theorem raw1401_h : ((raw (⟨1401, by decide⟩ : Fin 1902)).ok (rawMin (⟨1401, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1401, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1401.map (fun x => (x.lo, x.hi))) ((raw (⟨1401, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1402_0_ok : RawF.check ctl A B pd i0 (raw (⟨1402, by decide⟩ : Fin 1902)) rp1402_0 = true := by decide +kernel

theorem raw1402_h : ((raw (⟨1402, by decide⟩ : Fin 1902)).ok (rawMin (⟨1402, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1402, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1402.map (fun x => (x.lo, x.hi))) ((raw (⟨1402, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1403_0_ok : RawF.check ctl A B pd i0 (raw (⟨1403, by decide⟩ : Fin 1902)) rp1403_0 = true := by decide +kernel

theorem rp1403_1_ok : RawF.check ctl A B pd i0 (raw (⟨1403, by decide⟩ : Fin 1902)) rp1403_1 = true := by decide +kernel

theorem rp1403_2_ok : RawF.check ctl A B pd i0 (raw (⟨1403, by decide⟩ : Fin 1902)) rp1403_2 = true := by decide +kernel

theorem raw1403_h : ((raw (⟨1403, by decide⟩ : Fin 1902)).ok (rawMin (⟨1403, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1403, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1403.map (fun x => (x.lo, x.hi))) ((raw (⟨1403, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1404_0_ok : RawF.check ctl A B pd i0 (raw (⟨1404, by decide⟩ : Fin 1902)) rp1404_0 = true := by decide +kernel

theorem rp1404_1_ok : RawF.check ctl A B pd i0 (raw (⟨1404, by decide⟩ : Fin 1902)) rp1404_1 = true := by decide +kernel

theorem rp1404_2_ok : RawF.check ctl A B pd i0 (raw (⟨1404, by decide⟩ : Fin 1902)) rp1404_2 = true := by decide +kernel

theorem raw1404_h : ((raw (⟨1404, by decide⟩ : Fin 1902)).ok (rawMin (⟨1404, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1404, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1404.map (fun x => (x.lo, x.hi))) ((raw (⟨1404, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1405_0_ok : RawF.check ctl A B pd i0 (raw (⟨1405, by decide⟩ : Fin 1902)) rp1405_0 = true := by decide +kernel

theorem rp1405_1_ok : RawF.check ctl A B pd i0 (raw (⟨1405, by decide⟩ : Fin 1902)) rp1405_1 = true := by decide +kernel

theorem rp1405_2_ok : RawF.check ctl A B pd i0 (raw (⟨1405, by decide⟩ : Fin 1902)) rp1405_2 = true := by decide +kernel

theorem raw1405_h : ((raw (⟨1405, by decide⟩ : Fin 1902)).ok (rawMin (⟨1405, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1405, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1405.map (fun x => (x.lo, x.hi))) ((raw (⟨1405, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1406_0_ok : RawF.check ctl A B pd i0 (raw (⟨1406, by decide⟩ : Fin 1902)) rp1406_0 = true := by decide +kernel

theorem rp1406_1_ok : RawF.check ctl A B pd i0 (raw (⟨1406, by decide⟩ : Fin 1902)) rp1406_1 = true := by decide +kernel

theorem rp1406_2_ok : RawF.check ctl A B pd i0 (raw (⟨1406, by decide⟩ : Fin 1902)) rp1406_2 = true := by decide +kernel

theorem raw1406_h : ((raw (⟨1406, by decide⟩ : Fin 1902)).ok (rawMin (⟨1406, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1406, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1406.map (fun x => (x.lo, x.hi))) ((raw (⟨1406, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1407_0_ok : RawF.check ctl A B pd i0 (raw (⟨1407, by decide⟩ : Fin 1902)) rp1407_0 = true := by decide +kernel

theorem raw1407_h : ((raw (⟨1407, by decide⟩ : Fin 1902)).ok (rawMin (⟨1407, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1407, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1407.map (fun x => (x.lo, x.hi))) ((raw (⟨1407, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1408_0_ok : RawF.check ctl A B pd i0 (raw (⟨1408, by decide⟩ : Fin 1902)) rp1408_0 = true := by decide +kernel

theorem rp1408_1_ok : RawF.check ctl A B pd i0 (raw (⟨1408, by decide⟩ : Fin 1902)) rp1408_1 = true := by decide +kernel

theorem rp1408_2_ok : RawF.check ctl A B pd i0 (raw (⟨1408, by decide⟩ : Fin 1902)) rp1408_2 = true := by decide +kernel

theorem rp1408_3_ok : RawF.check ctl A B pd i0 (raw (⟨1408, by decide⟩ : Fin 1902)) rp1408_3 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
