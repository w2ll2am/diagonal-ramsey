import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem raw4_h : ((raw (⟨4, by decide⟩ : Fin 1902)).ok (rawMin (⟨4, by decide⟩ : Fin 1902)) && chainF ((raw (⟨4, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp4.map (fun x => (x.lo, x.hi))) ((raw (⟨4, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp5_0_ok : RawF.check ctl A B pd i0 (raw (⟨5, by decide⟩ : Fin 1902)) rp5_0 = true := by decide +kernel

theorem rp5_1_ok : RawF.check ctl A B pd i0 (raw (⟨5, by decide⟩ : Fin 1902)) rp5_1 = true := by decide +kernel

theorem raw5_h : ((raw (⟨5, by decide⟩ : Fin 1902)).ok (rawMin (⟨5, by decide⟩ : Fin 1902)) && chainF ((raw (⟨5, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp5.map (fun x => (x.lo, x.hi))) ((raw (⟨5, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp6_0_ok : RawF.check ctl A B pd i0 (raw (⟨6, by decide⟩ : Fin 1902)) rp6_0 = true := by decide +kernel

theorem rp6_1_ok : RawF.check ctl A B pd i0 (raw (⟨6, by decide⟩ : Fin 1902)) rp6_1 = true := by decide +kernel

theorem rp6_2_ok : RawF.check ctl A B pd i0 (raw (⟨6, by decide⟩ : Fin 1902)) rp6_2 = true := by decide +kernel

theorem raw6_h : ((raw (⟨6, by decide⟩ : Fin 1902)).ok (rawMin (⟨6, by decide⟩ : Fin 1902)) && chainF ((raw (⟨6, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp6.map (fun x => (x.lo, x.hi))) ((raw (⟨6, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp7_0_ok : RawF.check ctl A B pd i0 (raw (⟨7, by decide⟩ : Fin 1902)) rp7_0 = true := by decide +kernel

theorem rp7_1_ok : RawF.check ctl A B pd i0 (raw (⟨7, by decide⟩ : Fin 1902)) rp7_1 = true := by decide +kernel

theorem rp7_2_ok : RawF.check ctl A B pd i0 (raw (⟨7, by decide⟩ : Fin 1902)) rp7_2 = true := by decide +kernel

theorem rp7_3_ok : RawF.check ctl A B pd i0 (raw (⟨7, by decide⟩ : Fin 1902)) rp7_3 = true := by decide +kernel

theorem raw7_h : ((raw (⟨7, by decide⟩ : Fin 1902)).ok (rawMin (⟨7, by decide⟩ : Fin 1902)) && chainF ((raw (⟨7, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp7.map (fun x => (x.lo, x.hi))) ((raw (⟨7, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp8_0_ok : RawF.check ctl A B pd i0 (raw (⟨8, by decide⟩ : Fin 1902)) rp8_0 = true := by decide +kernel

theorem raw8_h : ((raw (⟨8, by decide⟩ : Fin 1902)).ok (rawMin (⟨8, by decide⟩ : Fin 1902)) && chainF ((raw (⟨8, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp8.map (fun x => (x.lo, x.hi))) ((raw (⟨8, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp9_0_ok : RawF.check ctl A B pd i0 (raw (⟨9, by decide⟩ : Fin 1902)) rp9_0 = true := by decide +kernel

theorem rp9_1_ok : RawF.check ctl A B pd i0 (raw (⟨9, by decide⟩ : Fin 1902)) rp9_1 = true := by decide +kernel

theorem rp9_2_ok : RawF.check ctl A B pd i0 (raw (⟨9, by decide⟩ : Fin 1902)) rp9_2 = true := by decide +kernel

theorem rp9_3_ok : RawF.check ctl A B pd i0 (raw (⟨9, by decide⟩ : Fin 1902)) rp9_3 = true := by decide +kernel

theorem rp9_4_ok : RawF.check ctl A B pd i0 (raw (⟨9, by decide⟩ : Fin 1902)) rp9_4 = true := by decide +kernel

theorem raw9_h : ((raw (⟨9, by decide⟩ : Fin 1902)).ok (rawMin (⟨9, by decide⟩ : Fin 1902)) && chainF ((raw (⟨9, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp9.map (fun x => (x.lo, x.hi))) ((raw (⟨9, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp10_0_ok : RawF.check ctl A B pd i0 (raw (⟨10, by decide⟩ : Fin 1902)) rp10_0 = true := by decide +kernel

theorem rp10_1_ok : RawF.check ctl A B pd i0 (raw (⟨10, by decide⟩ : Fin 1902)) rp10_1 = true := by decide +kernel

theorem raw10_h : ((raw (⟨10, by decide⟩ : Fin 1902)).ok (rawMin (⟨10, by decide⟩ : Fin 1902)) && chainF ((raw (⟨10, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp10.map (fun x => (x.lo, x.hi))) ((raw (⟨10, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp11_0_ok : RawF.check ctl A B pd i0 (raw (⟨11, by decide⟩ : Fin 1902)) rp11_0 = true := by decide +kernel

theorem raw11_h : ((raw (⟨11, by decide⟩ : Fin 1902)).ok (rawMin (⟨11, by decide⟩ : Fin 1902)) && chainF ((raw (⟨11, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp11.map (fun x => (x.lo, x.hi))) ((raw (⟨11, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp12_0_ok : RawF.check ctl A B pd i0 (raw (⟨12, by decide⟩ : Fin 1902)) rp12_0 = true := by decide +kernel

theorem rp12_1_ok : RawF.check ctl A B pd i0 (raw (⟨12, by decide⟩ : Fin 1902)) rp12_1 = true := by decide +kernel

theorem rp12_2_ok : RawF.check ctl A B pd i0 (raw (⟨12, by decide⟩ : Fin 1902)) rp12_2 = true := by decide +kernel

theorem raw12_h : ((raw (⟨12, by decide⟩ : Fin 1902)).ok (rawMin (⟨12, by decide⟩ : Fin 1902)) && chainF ((raw (⟨12, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp12.map (fun x => (x.lo, x.hi))) ((raw (⟨12, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
