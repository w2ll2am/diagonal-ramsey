import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp410_4_ok : RawF.check ctl A B pd i0 (raw (⟨410, by decide⟩ : Fin 1902)) rp410_4 = true := by decide +kernel

theorem rp410_5_ok : RawF.check ctl A B pd i0 (raw (⟨410, by decide⟩ : Fin 1902)) rp410_5 = true := by decide +kernel

theorem rp410_6_ok : RawF.check ctl A B pd i0 (raw (⟨410, by decide⟩ : Fin 1902)) rp410_6 = true := by decide +kernel

theorem rp410_7_ok : RawF.check ctl A B pd i0 (raw (⟨410, by decide⟩ : Fin 1902)) rp410_7 = true := by decide +kernel

theorem raw410_h : ((raw (⟨410, by decide⟩ : Fin 1902)).ok (rawMin (⟨410, by decide⟩ : Fin 1902)) && chainF ((raw (⟨410, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp410.map (fun x => (x.lo, x.hi))) ((raw (⟨410, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp411_0_ok : RawF.check ctl A B pd i0 (raw (⟨411, by decide⟩ : Fin 1902)) rp411_0 = true := by decide +kernel

theorem rp411_1_ok : RawF.check ctl A B pd i0 (raw (⟨411, by decide⟩ : Fin 1902)) rp411_1 = true := by decide +kernel

theorem rp411_2_ok : RawF.check ctl A B pd i0 (raw (⟨411, by decide⟩ : Fin 1902)) rp411_2 = true := by decide +kernel

theorem raw411_h : ((raw (⟨411, by decide⟩ : Fin 1902)).ok (rawMin (⟨411, by decide⟩ : Fin 1902)) && chainF ((raw (⟨411, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp411.map (fun x => (x.lo, x.hi))) ((raw (⟨411, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp412_0_ok : RawF.check ctl A B pd i0 (raw (⟨412, by decide⟩ : Fin 1902)) rp412_0 = true := by decide +kernel

theorem rp412_1_ok : RawF.check ctl A B pd i0 (raw (⟨412, by decide⟩ : Fin 1902)) rp412_1 = true := by decide +kernel

theorem rp412_2_ok : RawF.check ctl A B pd i0 (raw (⟨412, by decide⟩ : Fin 1902)) rp412_2 = true := by decide +kernel

theorem raw412_h : ((raw (⟨412, by decide⟩ : Fin 1902)).ok (rawMin (⟨412, by decide⟩ : Fin 1902)) && chainF ((raw (⟨412, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp412.map (fun x => (x.lo, x.hi))) ((raw (⟨412, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp413_0_ok : RawF.check ctl A B pd i0 (raw (⟨413, by decide⟩ : Fin 1902)) rp413_0 = true := by decide +kernel

theorem rp413_1_ok : RawF.check ctl A B pd i0 (raw (⟨413, by decide⟩ : Fin 1902)) rp413_1 = true := by decide +kernel

theorem raw413_h : ((raw (⟨413, by decide⟩ : Fin 1902)).ok (rawMin (⟨413, by decide⟩ : Fin 1902)) && chainF ((raw (⟨413, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp413.map (fun x => (x.lo, x.hi))) ((raw (⟨413, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp414_0_ok : RawF.check ctl A B pd i0 (raw (⟨414, by decide⟩ : Fin 1902)) rp414_0 = true := by decide +kernel

theorem rp414_1_ok : RawF.check ctl A B pd i0 (raw (⟨414, by decide⟩ : Fin 1902)) rp414_1 = true := by decide +kernel

theorem rp414_2_ok : RawF.check ctl A B pd i0 (raw (⟨414, by decide⟩ : Fin 1902)) rp414_2 = true := by decide +kernel

theorem raw414_h : ((raw (⟨414, by decide⟩ : Fin 1902)).ok (rawMin (⟨414, by decide⟩ : Fin 1902)) && chainF ((raw (⟨414, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp414.map (fun x => (x.lo, x.hi))) ((raw (⟨414, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp415_0_ok : RawF.check ctl A B pd i0 (raw (⟨415, by decide⟩ : Fin 1902)) rp415_0 = true := by decide +kernel

theorem rp415_1_ok : RawF.check ctl A B pd i0 (raw (⟨415, by decide⟩ : Fin 1902)) rp415_1 = true := by decide +kernel

theorem raw415_h : ((raw (⟨415, by decide⟩ : Fin 1902)).ok (rawMin (⟨415, by decide⟩ : Fin 1902)) && chainF ((raw (⟨415, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp415.map (fun x => (x.lo, x.hi))) ((raw (⟨415, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp416_0_ok : RawF.check ctl A B pd i0 (raw (⟨416, by decide⟩ : Fin 1902)) rp416_0 = true := by decide +kernel

theorem raw416_h : ((raw (⟨416, by decide⟩ : Fin 1902)).ok (rawMin (⟨416, by decide⟩ : Fin 1902)) && chainF ((raw (⟨416, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp416.map (fun x => (x.lo, x.hi))) ((raw (⟨416, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp417_0_ok : RawF.check ctl A B pd i0 (raw (⟨417, by decide⟩ : Fin 1902)) rp417_0 = true := by decide +kernel

theorem rp417_1_ok : RawF.check ctl A B pd i0 (raw (⟨417, by decide⟩ : Fin 1902)) rp417_1 = true := by decide +kernel

theorem raw417_h : ((raw (⟨417, by decide⟩ : Fin 1902)).ok (rawMin (⟨417, by decide⟩ : Fin 1902)) && chainF ((raw (⟨417, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp417.map (fun x => (x.lo, x.hi))) ((raw (⟨417, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp418_0_ok : RawF.check ctl A B pd i0 (raw (⟨418, by decide⟩ : Fin 1902)) rp418_0 = true := by decide +kernel

theorem rp418_1_ok : RawF.check ctl A B pd i0 (raw (⟨418, by decide⟩ : Fin 1902)) rp418_1 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
