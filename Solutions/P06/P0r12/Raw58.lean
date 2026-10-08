import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp144_2_ok : RawF.check ctl A B pd i0 (raw (⟨144, by decide⟩ : Fin 1902)) rp144_2 = true := by decide +kernel

theorem rp144_3_ok : RawF.check ctl A B pd i0 (raw (⟨144, by decide⟩ : Fin 1902)) rp144_3 = true := by decide +kernel

theorem raw144_h : ((raw (⟨144, by decide⟩ : Fin 1902)).ok (rawMin (⟨144, by decide⟩ : Fin 1902)) && chainF ((raw (⟨144, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp144.map (fun x => (x.lo, x.hi))) ((raw (⟨144, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp145_0_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_0 = true := by decide +kernel

theorem rp145_1_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_1 = true := by decide +kernel

theorem rp145_2_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_2 = true := by decide +kernel

theorem rp145_3_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_3 = true := by decide +kernel

theorem rp145_4_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_4 = true := by decide +kernel

theorem rp145_5_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_5 = true := by decide +kernel

theorem rp145_6_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_6 = true := by decide +kernel

theorem rp145_7_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_7 = true := by decide +kernel

theorem rp145_8_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_8 = true := by decide +kernel

theorem rp145_9_ok : RawF.check ctl A B pd i0 (raw (⟨145, by decide⟩ : Fin 1902)) rp145_9 = true := by decide +kernel

theorem raw145_h : ((raw (⟨145, by decide⟩ : Fin 1902)).ok (rawMin (⟨145, by decide⟩ : Fin 1902)) && chainF ((raw (⟨145, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp145.map (fun x => (x.lo, x.hi))) ((raw (⟨145, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp146_0_ok : RawF.check ctl A B pd i0 (raw (⟨146, by decide⟩ : Fin 1902)) rp146_0 = true := by decide +kernel

theorem raw146_h : ((raw (⟨146, by decide⟩ : Fin 1902)).ok (rawMin (⟨146, by decide⟩ : Fin 1902)) && chainF ((raw (⟨146, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp146.map (fun x => (x.lo, x.hi))) ((raw (⟨146, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp147_0_ok : RawF.check ctl A B pd i0 (raw (⟨147, by decide⟩ : Fin 1902)) rp147_0 = true := by decide +kernel

theorem raw147_h : ((raw (⟨147, by decide⟩ : Fin 1902)).ok (rawMin (⟨147, by decide⟩ : Fin 1902)) && chainF ((raw (⟨147, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp147.map (fun x => (x.lo, x.hi))) ((raw (⟨147, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp148_0_ok : RawF.check ctl A B pd i0 (raw (⟨148, by decide⟩ : Fin 1902)) rp148_0 = true := by decide +kernel

theorem rp148_1_ok : RawF.check ctl A B pd i0 (raw (⟨148, by decide⟩ : Fin 1902)) rp148_1 = true := by decide +kernel

theorem rp148_2_ok : RawF.check ctl A B pd i0 (raw (⟨148, by decide⟩ : Fin 1902)) rp148_2 = true := by decide +kernel

theorem rp148_3_ok : RawF.check ctl A B pd i0 (raw (⟨148, by decide⟩ : Fin 1902)) rp148_3 = true := by decide +kernel

theorem raw148_h : ((raw (⟨148, by decide⟩ : Fin 1902)).ok (rawMin (⟨148, by decide⟩ : Fin 1902)) && chainF ((raw (⟨148, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp148.map (fun x => (x.lo, x.hi))) ((raw (⟨148, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp149_0_ok : RawF.check ctl A B pd i0 (raw (⟨149, by decide⟩ : Fin 1902)) rp149_0 = true := by decide +kernel

theorem rp149_1_ok : RawF.check ctl A B pd i0 (raw (⟨149, by decide⟩ : Fin 1902)) rp149_1 = true := by decide +kernel

theorem rp149_2_ok : RawF.check ctl A B pd i0 (raw (⟨149, by decide⟩ : Fin 1902)) rp149_2 = true := by decide +kernel

theorem rp149_3_ok : RawF.check ctl A B pd i0 (raw (⟨149, by decide⟩ : Fin 1902)) rp149_3 = true := by decide +kernel

theorem rp149_4_ok : RawF.check ctl A B pd i0 (raw (⟨149, by decide⟩ : Fin 1902)) rp149_4 = true := by decide +kernel

theorem rp149_5_ok : RawF.check ctl A B pd i0 (raw (⟨149, by decide⟩ : Fin 1902)) rp149_5 = true := by decide +kernel

theorem rp149_6_ok : RawF.check ctl A B pd i0 (raw (⟨149, by decide⟩ : Fin 1902)) rp149_6 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
