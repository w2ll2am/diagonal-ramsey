import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D76

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp1786_1_ok : RawF.check ctl A B pd i0 (raw (⟨1786, by decide⟩ : Fin 1902)) rp1786_1 = true := by decide +kernel

theorem rp1786_2_ok : RawF.check ctl A B pd i0 (raw (⟨1786, by decide⟩ : Fin 1902)) rp1786_2 = true := by decide +kernel

theorem raw1786_h : ((raw (⟨1786, by decide⟩ : Fin 1902)).ok (rawMin (⟨1786, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1786, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1786.map (fun x => (x.lo, x.hi))) ((raw (⟨1786, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1787_0_ok : RawF.check ctl A B pd i0 (raw (⟨1787, by decide⟩ : Fin 1902)) rp1787_0 = true := by decide +kernel

theorem rp1787_1_ok : RawF.check ctl A B pd i0 (raw (⟨1787, by decide⟩ : Fin 1902)) rp1787_1 = true := by decide +kernel

theorem raw1787_h : ((raw (⟨1787, by decide⟩ : Fin 1902)).ok (rawMin (⟨1787, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1787, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1787.map (fun x => (x.lo, x.hi))) ((raw (⟨1787, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1788_0_ok : RawF.check ctl A B pd i0 (raw (⟨1788, by decide⟩ : Fin 1902)) rp1788_0 = true := by decide +kernel

theorem raw1788_h : ((raw (⟨1788, by decide⟩ : Fin 1902)).ok (rawMin (⟨1788, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1788, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1788.map (fun x => (x.lo, x.hi))) ((raw (⟨1788, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1789_0_ok : RawF.check ctl A B pd i0 (raw (⟨1789, by decide⟩ : Fin 1902)) rp1789_0 = true := by decide +kernel

theorem raw1789_h : ((raw (⟨1789, by decide⟩ : Fin 1902)).ok (rawMin (⟨1789, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1789, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1789.map (fun x => (x.lo, x.hi))) ((raw (⟨1789, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1790_0_ok : RawF.check ctl A B pd i0 (raw (⟨1790, by decide⟩ : Fin 1902)) rp1790_0 = true := by decide +kernel

theorem raw1790_h : ((raw (⟨1790, by decide⟩ : Fin 1902)).ok (rawMin (⟨1790, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1790, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1790.map (fun x => (x.lo, x.hi))) ((raw (⟨1790, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1791_0_ok : RawF.check ctl A B pd i0 (raw (⟨1791, by decide⟩ : Fin 1902)) rp1791_0 = true := by decide +kernel

theorem raw1791_h : ((raw (⟨1791, by decide⟩ : Fin 1902)).ok (rawMin (⟨1791, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1791, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1791.map (fun x => (x.lo, x.hi))) ((raw (⟨1791, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1792_0_ok : RawF.check ctl A B pd i0 (raw (⟨1792, by decide⟩ : Fin 1902)) rp1792_0 = true := by decide +kernel

theorem rp1792_1_ok : RawF.check ctl A B pd i0 (raw (⟨1792, by decide⟩ : Fin 1902)) rp1792_1 = true := by decide +kernel

theorem raw1792_h : ((raw (⟨1792, by decide⟩ : Fin 1902)).ok (rawMin (⟨1792, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1792, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1792.map (fun x => (x.lo, x.hi))) ((raw (⟨1792, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1793_0_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_0 = true := by decide +kernel

theorem rp1793_1_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_1 = true := by decide +kernel

theorem rp1793_2_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_2 = true := by decide +kernel

theorem rp1793_3_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_3 = true := by decide +kernel

theorem rp1793_4_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_4 = true := by decide +kernel

theorem rp1793_5_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_5 = true := by decide +kernel

theorem rp1793_6_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_6 = true := by decide +kernel

theorem rp1793_7_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_7 = true := by decide +kernel

theorem rp1793_8_ok : RawF.check ctl A B pd i0 (raw (⟨1793, by decide⟩ : Fin 1902)) rp1793_8 = true := by decide +kernel

theorem raw1793_h : ((raw (⟨1793, by decide⟩ : Fin 1902)).ok (rawMin (⟨1793, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1793, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1793.map (fun x => (x.lo, x.hi))) ((raw (⟨1793, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1794_0_ok : RawF.check ctl A B pd i0 (raw (⟨1794, by decide⟩ : Fin 1902)) rp1794_0 = true := by decide +kernel

theorem raw1794_h : ((raw (⟨1794, by decide⟩ : Fin 1902)).ok (rawMin (⟨1794, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1794, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1794.map (fun x => (x.lo, x.hi))) ((raw (⟨1794, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1795_0_ok : RawF.check ctl A B pd i0 (raw (⟨1795, by decide⟩ : Fin 1902)) rp1795_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
