import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp216_2_ok : RawF.check ctl A B pd i0 (raw (⟨216, by decide⟩ : Fin 1902)) rp216_2 = true := by decide +kernel

theorem raw216_h : ((raw (⟨216, by decide⟩ : Fin 1902)).ok (rawMin (⟨216, by decide⟩ : Fin 1902)) && chainF ((raw (⟨216, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp216.map (fun x => (x.lo, x.hi))) ((raw (⟨216, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp217_0_ok : RawF.check ctl A B pd i0 (raw (⟨217, by decide⟩ : Fin 1902)) rp217_0 = true := by decide +kernel

theorem raw217_h : ((raw (⟨217, by decide⟩ : Fin 1902)).ok (rawMin (⟨217, by decide⟩ : Fin 1902)) && chainF ((raw (⟨217, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp217.map (fun x => (x.lo, x.hi))) ((raw (⟨217, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp218_0_ok : RawF.check ctl A B pd i0 (raw (⟨218, by decide⟩ : Fin 1902)) rp218_0 = true := by decide +kernel

theorem rp218_1_ok : RawF.check ctl A B pd i0 (raw (⟨218, by decide⟩ : Fin 1902)) rp218_1 = true := by decide +kernel

theorem rp218_2_ok : RawF.check ctl A B pd i0 (raw (⟨218, by decide⟩ : Fin 1902)) rp218_2 = true := by decide +kernel

theorem rp218_3_ok : RawF.check ctl A B pd i0 (raw (⟨218, by decide⟩ : Fin 1902)) rp218_3 = true := by decide +kernel

theorem rp218_4_ok : RawF.check ctl A B pd i0 (raw (⟨218, by decide⟩ : Fin 1902)) rp218_4 = true := by decide +kernel

theorem raw218_h : ((raw (⟨218, by decide⟩ : Fin 1902)).ok (rawMin (⟨218, by decide⟩ : Fin 1902)) && chainF ((raw (⟨218, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp218.map (fun x => (x.lo, x.hi))) ((raw (⟨218, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp219_0_ok : RawF.check ctl A B pd i0 (raw (⟨219, by decide⟩ : Fin 1902)) rp219_0 = true := by decide +kernel

theorem rp219_1_ok : RawF.check ctl A B pd i0 (raw (⟨219, by decide⟩ : Fin 1902)) rp219_1 = true := by decide +kernel

theorem rp219_2_ok : RawF.check ctl A B pd i0 (raw (⟨219, by decide⟩ : Fin 1902)) rp219_2 = true := by decide +kernel

theorem rp219_3_ok : RawF.check ctl A B pd i0 (raw (⟨219, by decide⟩ : Fin 1902)) rp219_3 = true := by decide +kernel

theorem rp219_4_ok : RawF.check ctl A B pd i0 (raw (⟨219, by decide⟩ : Fin 1902)) rp219_4 = true := by decide +kernel

theorem raw219_h : ((raw (⟨219, by decide⟩ : Fin 1902)).ok (rawMin (⟨219, by decide⟩ : Fin 1902)) && chainF ((raw (⟨219, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp219.map (fun x => (x.lo, x.hi))) ((raw (⟨219, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp220_0_ok : RawF.check ctl A B pd i0 (raw (⟨220, by decide⟩ : Fin 1902)) rp220_0 = true := by decide +kernel

theorem raw220_h : ((raw (⟨220, by decide⟩ : Fin 1902)).ok (rawMin (⟨220, by decide⟩ : Fin 1902)) && chainF ((raw (⟨220, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp220.map (fun x => (x.lo, x.hi))) ((raw (⟨220, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp221_0_ok : RawF.check ctl A B pd i0 (raw (⟨221, by decide⟩ : Fin 1902)) rp221_0 = true := by decide +kernel

theorem raw221_h : ((raw (⟨221, by decide⟩ : Fin 1902)).ok (rawMin (⟨221, by decide⟩ : Fin 1902)) && chainF ((raw (⟨221, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp221.map (fun x => (x.lo, x.hi))) ((raw (⟨221, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp222_0_ok : RawF.check ctl A B pd i0 (raw (⟨222, by decide⟩ : Fin 1902)) rp222_0 = true := by decide +kernel

theorem rp222_1_ok : RawF.check ctl A B pd i0 (raw (⟨222, by decide⟩ : Fin 1902)) rp222_1 = true := by decide +kernel

theorem rp222_2_ok : RawF.check ctl A B pd i0 (raw (⟨222, by decide⟩ : Fin 1902)) rp222_2 = true := by decide +kernel

theorem rp222_3_ok : RawF.check ctl A B pd i0 (raw (⟨222, by decide⟩ : Fin 1902)) rp222_3 = true := by decide +kernel

theorem rp222_4_ok : RawF.check ctl A B pd i0 (raw (⟨222, by decide⟩ : Fin 1902)) rp222_4 = true := by decide +kernel

theorem rp222_5_ok : RawF.check ctl A B pd i0 (raw (⟨222, by decide⟩ : Fin 1902)) rp222_5 = true := by decide +kernel

theorem raw222_h : ((raw (⟨222, by decide⟩ : Fin 1902)).ok (rawMin (⟨222, by decide⟩ : Fin 1902)) && chainF ((raw (⟨222, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp222.map (fun x => (x.lo, x.hi))) ((raw (⟨222, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp223_0_ok : RawF.check ctl A B pd i0 (raw (⟨223, by decide⟩ : Fin 1902)) rp223_0 = true := by decide +kernel

theorem rp223_1_ok : RawF.check ctl A B pd i0 (raw (⟨223, by decide⟩ : Fin 1902)) rp223_1 = true := by decide +kernel

theorem rp223_2_ok : RawF.check ctl A B pd i0 (raw (⟨223, by decide⟩ : Fin 1902)) rp223_2 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
