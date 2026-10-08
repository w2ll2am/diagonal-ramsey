import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D68

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1710_0_ok : RawF.check ctl A B pd i0 (raw (⟨1710, by decide⟩ : Fin 1902)) rp1710_0 = true := by decide +kernel

theorem rp1710_1_ok : RawF.check ctl A B pd i0 (raw (⟨1710, by decide⟩ : Fin 1902)) rp1710_1 = true := by decide +kernel

theorem rp1710_2_ok : RawF.check ctl A B pd i0 (raw (⟨1710, by decide⟩ : Fin 1902)) rp1710_2 = true := by decide +kernel

theorem rp1710_3_ok : RawF.check ctl A B pd i0 (raw (⟨1710, by decide⟩ : Fin 1902)) rp1710_3 = true := by decide +kernel

theorem raw1710_h : ((raw (⟨1710, by decide⟩ : Fin 1902)).ok (rawMin (⟨1710, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1710, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1710.map (fun x => (x.lo, x.hi))) ((raw (⟨1710, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1711_0_ok : RawF.check ctl A B pd i0 (raw (⟨1711, by decide⟩ : Fin 1902)) rp1711_0 = true := by decide +kernel

theorem raw1711_h : ((raw (⟨1711, by decide⟩ : Fin 1902)).ok (rawMin (⟨1711, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1711, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1711.map (fun x => (x.lo, x.hi))) ((raw (⟨1711, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1712_0_ok : RawF.check ctl A B pd i0 (raw (⟨1712, by decide⟩ : Fin 1902)) rp1712_0 = true := by decide +kernel

theorem raw1712_h : ((raw (⟨1712, by decide⟩ : Fin 1902)).ok (rawMin (⟨1712, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1712, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1712.map (fun x => (x.lo, x.hi))) ((raw (⟨1712, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1713_0_ok : RawF.check ctl A B pd i0 (raw (⟨1713, by decide⟩ : Fin 1902)) rp1713_0 = true := by decide +kernel

theorem rp1713_1_ok : RawF.check ctl A B pd i0 (raw (⟨1713, by decide⟩ : Fin 1902)) rp1713_1 = true := by decide +kernel

theorem raw1713_h : ((raw (⟨1713, by decide⟩ : Fin 1902)).ok (rawMin (⟨1713, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1713, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1713.map (fun x => (x.lo, x.hi))) ((raw (⟨1713, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1714_0_ok : RawF.check ctl A B pd i0 (raw (⟨1714, by decide⟩ : Fin 1902)) rp1714_0 = true := by decide +kernel

theorem rp1714_1_ok : RawF.check ctl A B pd i0 (raw (⟨1714, by decide⟩ : Fin 1902)) rp1714_1 = true := by decide +kernel

theorem rp1714_2_ok : RawF.check ctl A B pd i0 (raw (⟨1714, by decide⟩ : Fin 1902)) rp1714_2 = true := by decide +kernel

theorem raw1714_h : ((raw (⟨1714, by decide⟩ : Fin 1902)).ok (rawMin (⟨1714, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1714, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1714.map (fun x => (x.lo, x.hi))) ((raw (⟨1714, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1715_0_ok : RawF.check ctl A B pd i0 (raw (⟨1715, by decide⟩ : Fin 1902)) rp1715_0 = true := by decide +kernel

theorem raw1715_h : ((raw (⟨1715, by decide⟩ : Fin 1902)).ok (rawMin (⟨1715, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1715, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1715.map (fun x => (x.lo, x.hi))) ((raw (⟨1715, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1716_0_ok : RawF.check ctl A B pd i0 (raw (⟨1716, by decide⟩ : Fin 1902)) rp1716_0 = true := by decide +kernel

theorem rp1716_1_ok : RawF.check ctl A B pd i0 (raw (⟨1716, by decide⟩ : Fin 1902)) rp1716_1 = true := by decide +kernel

theorem rp1716_2_ok : RawF.check ctl A B pd i0 (raw (⟨1716, by decide⟩ : Fin 1902)) rp1716_2 = true := by decide +kernel

theorem rp1716_3_ok : RawF.check ctl A B pd i0 (raw (⟨1716, by decide⟩ : Fin 1902)) rp1716_3 = true := by decide +kernel

theorem rp1716_4_ok : RawF.check ctl A B pd i0 (raw (⟨1716, by decide⟩ : Fin 1902)) rp1716_4 = true := by decide +kernel

theorem rp1716_5_ok : RawF.check ctl A B pd i0 (raw (⟨1716, by decide⟩ : Fin 1902)) rp1716_5 = true := by decide +kernel

theorem raw1716_h : ((raw (⟨1716, by decide⟩ : Fin 1902)).ok (rawMin (⟨1716, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1716, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1716.map (fun x => (x.lo, x.hi))) ((raw (⟨1716, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1717_0_ok : RawF.check ctl A B pd i0 (raw (⟨1717, by decide⟩ : Fin 1902)) rp1717_0 = true := by decide +kernel

theorem rp1717_1_ok : RawF.check ctl A B pd i0 (raw (⟨1717, by decide⟩ : Fin 1902)) rp1717_1 = true := by decide +kernel

theorem raw1717_h : ((raw (⟨1717, by decide⟩ : Fin 1902)).ok (rawMin (⟨1717, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1717, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1717.map (fun x => (x.lo, x.hi))) ((raw (⟨1717, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1718_0_ok : RawF.check ctl A B pd i0 (raw (⟨1718, by decide⟩ : Fin 1902)) rp1718_0 = true := by decide +kernel

theorem rp1718_1_ok : RawF.check ctl A B pd i0 (raw (⟨1718, by decide⟩ : Fin 1902)) rp1718_1 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
