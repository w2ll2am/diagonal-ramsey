import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp380_2_ok : RawF.check ctl A B pd i0 (raw (⟨380, by decide⟩ : Fin 1902)) rp380_2 = true := by decide +kernel

theorem raw380_h : ((raw (⟨380, by decide⟩ : Fin 1902)).ok (rawMin (⟨380, by decide⟩ : Fin 1902)) && chainF ((raw (⟨380, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp380.map (fun x => (x.lo, x.hi))) ((raw (⟨380, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp381_0_ok : RawF.check ctl A B pd i0 (raw (⟨381, by decide⟩ : Fin 1902)) rp381_0 = true := by decide +kernel

theorem rp381_1_ok : RawF.check ctl A B pd i0 (raw (⟨381, by decide⟩ : Fin 1902)) rp381_1 = true := by decide +kernel

theorem raw381_h : ((raw (⟨381, by decide⟩ : Fin 1902)).ok (rawMin (⟨381, by decide⟩ : Fin 1902)) && chainF ((raw (⟨381, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp381.map (fun x => (x.lo, x.hi))) ((raw (⟨381, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp382_0_ok : RawF.check ctl A B pd i0 (raw (⟨382, by decide⟩ : Fin 1902)) rp382_0 = true := by decide +kernel

theorem rp382_1_ok : RawF.check ctl A B pd i0 (raw (⟨382, by decide⟩ : Fin 1902)) rp382_1 = true := by decide +kernel

theorem raw382_h : ((raw (⟨382, by decide⟩ : Fin 1902)).ok (rawMin (⟨382, by decide⟩ : Fin 1902)) && chainF ((raw (⟨382, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp382.map (fun x => (x.lo, x.hi))) ((raw (⟨382, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp383_0_ok : RawF.check ctl A B pd i0 (raw (⟨383, by decide⟩ : Fin 1902)) rp383_0 = true := by decide +kernel

theorem rp383_1_ok : RawF.check ctl A B pd i0 (raw (⟨383, by decide⟩ : Fin 1902)) rp383_1 = true := by decide +kernel

theorem raw383_h : ((raw (⟨383, by decide⟩ : Fin 1902)).ok (rawMin (⟨383, by decide⟩ : Fin 1902)) && chainF ((raw (⟨383, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp383.map (fun x => (x.lo, x.hi))) ((raw (⟨383, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp384_0_ok : RawF.check ctl A B pd i0 (raw (⟨384, by decide⟩ : Fin 1902)) rp384_0 = true := by decide +kernel

theorem raw384_h : ((raw (⟨384, by decide⟩ : Fin 1902)).ok (rawMin (⟨384, by decide⟩ : Fin 1902)) && chainF ((raw (⟨384, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp384.map (fun x => (x.lo, x.hi))) ((raw (⟨384, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp385_0_ok : RawF.check ctl A B pd i0 (raw (⟨385, by decide⟩ : Fin 1902)) rp385_0 = true := by decide +kernel

theorem raw385_h : ((raw (⟨385, by decide⟩ : Fin 1902)).ok (rawMin (⟨385, by decide⟩ : Fin 1902)) && chainF ((raw (⟨385, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp385.map (fun x => (x.lo, x.hi))) ((raw (⟨385, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp386_0_ok : RawF.check ctl A B pd i0 (raw (⟨386, by decide⟩ : Fin 1902)) rp386_0 = true := by decide +kernel

theorem rp386_1_ok : RawF.check ctl A B pd i0 (raw (⟨386, by decide⟩ : Fin 1902)) rp386_1 = true := by decide +kernel

theorem rp386_2_ok : RawF.check ctl A B pd i0 (raw (⟨386, by decide⟩ : Fin 1902)) rp386_2 = true := by decide +kernel

theorem raw386_h : ((raw (⟨386, by decide⟩ : Fin 1902)).ok (rawMin (⟨386, by decide⟩ : Fin 1902)) && chainF ((raw (⟨386, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp386.map (fun x => (x.lo, x.hi))) ((raw (⟨386, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp387_0_ok : RawF.check ctl A B pd i0 (raw (⟨387, by decide⟩ : Fin 1902)) rp387_0 = true := by decide +kernel

theorem rp387_1_ok : RawF.check ctl A B pd i0 (raw (⟨387, by decide⟩ : Fin 1902)) rp387_1 = true := by decide +kernel

theorem rp387_2_ok : RawF.check ctl A B pd i0 (raw (⟨387, by decide⟩ : Fin 1902)) rp387_2 = true := by decide +kernel

theorem raw387_h : ((raw (⟨387, by decide⟩ : Fin 1902)).ok (rawMin (⟨387, by decide⟩ : Fin 1902)) && chainF ((raw (⟨387, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp387.map (fun x => (x.lo, x.hi))) ((raw (⟨387, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp388_0_ok : RawF.check ctl A B pd i0 (raw (⟨388, by decide⟩ : Fin 1902)) rp388_0 = true := by decide +kernel

theorem rp388_1_ok : RawF.check ctl A B pd i0 (raw (⟨388, by decide⟩ : Fin 1902)) rp388_1 = true := by decide +kernel

theorem rp388_2_ok : RawF.check ctl A B pd i0 (raw (⟨388, by decide⟩ : Fin 1902)) rp388_2 = true := by decide +kernel

theorem raw388_h : ((raw (⟨388, by decide⟩ : Fin 1902)).ok (rawMin (⟨388, by decide⟩ : Fin 1902)) && chainF ((raw (⟨388, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp388.map (fun x => (x.lo, x.hi))) ((raw (⟨388, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp389_0_ok : RawF.check ctl A B pd i0 (raw (⟨389, by decide⟩ : Fin 1902)) rp389_0 = true := by decide +kernel

theorem rp389_1_ok : RawF.check ctl A B pd i0 (raw (⟨389, by decide⟩ : Fin 1902)) rp389_1 = true := by decide +kernel

theorem rp389_2_ok : RawF.check ctl A B pd i0 (raw (⟨389, by decide⟩ : Fin 1902)) rp389_2 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
