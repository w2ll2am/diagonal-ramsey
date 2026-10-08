import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp0_0_ok : RawF.check ctl A B pd i0 (raw (⟨0, by decide⟩ : Fin 1902)) rp0_0 = true := by decide +kernel

theorem rp0_1_ok : RawF.check ctl A B pd i0 (raw (⟨0, by decide⟩ : Fin 1902)) rp0_1 = true := by decide +kernel

theorem rp0_2_ok : RawF.check ctl A B pd i0 (raw (⟨0, by decide⟩ : Fin 1902)) rp0_2 = true := by decide +kernel

theorem rp0_3_ok : RawF.check ctl A B pd i0 (raw (⟨0, by decide⟩ : Fin 1902)) rp0_3 = true := by decide +kernel

theorem rp0_4_ok : RawF.check ctl A B pd i0 (raw (⟨0, by decide⟩ : Fin 1902)) rp0_4 = true := by decide +kernel

theorem rp0_5_ok : RawF.check ctl A B pd i0 (raw (⟨0, by decide⟩ : Fin 1902)) rp0_5 = true := by decide +kernel

theorem rp0_6_ok : RawF.check ctl A B pd i0 (raw (⟨0, by decide⟩ : Fin 1902)) rp0_6 = true := by decide +kernel

theorem rp0_7_ok : RawF.check ctl A B pd i0 (raw (⟨0, by decide⟩ : Fin 1902)) rp0_7 = true := by decide +kernel

theorem raw0_h : ((raw (⟨0, by decide⟩ : Fin 1902)).ok (rawMin (⟨0, by decide⟩ : Fin 1902)) && chainF ((raw (⟨0, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp0.map (fun x => (x.lo, x.hi))) ((raw (⟨0, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp1_0_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_0 = true := by decide +kernel

theorem rp1_1_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_1 = true := by decide +kernel

theorem rp1_2_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_2 = true := by decide +kernel

theorem rp1_3_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_3 = true := by decide +kernel

theorem rp1_4_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_4 = true := by decide +kernel

theorem rp1_5_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_5 = true := by decide +kernel

theorem rp1_6_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_6 = true := by decide +kernel

theorem rp1_7_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_7 = true := by decide +kernel

theorem rp1_8_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_8 = true := by decide +kernel

theorem rp1_9_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_9 = true := by decide +kernel

theorem rp1_10_ok : RawF.check ctl A B pd i0 (raw (⟨1, by decide⟩ : Fin 1902)) rp1_10 = true := by decide +kernel

theorem raw1_h : ((raw (⟨1, by decide⟩ : Fin 1902)).ok (rawMin (⟨1, by decide⟩ : Fin 1902)) && chainF ((raw (⟨1, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp1.map (fun x => (x.lo, x.hi))) ((raw (⟨1, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp2_0_ok : RawF.check ctl A B pd i0 (raw (⟨2, by decide⟩ : Fin 1902)) rp2_0 = true := by decide +kernel

theorem rp2_1_ok : RawF.check ctl A B pd i0 (raw (⟨2, by decide⟩ : Fin 1902)) rp2_1 = true := by decide +kernel

theorem rp2_2_ok : RawF.check ctl A B pd i0 (raw (⟨2, by decide⟩ : Fin 1902)) rp2_2 = true := by decide +kernel

theorem rp2_3_ok : RawF.check ctl A B pd i0 (raw (⟨2, by decide⟩ : Fin 1902)) rp2_3 = true := by decide +kernel

theorem raw2_h : ((raw (⟨2, by decide⟩ : Fin 1902)).ok (rawMin (⟨2, by decide⟩ : Fin 1902)) && chainF ((raw (⟨2, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp2.map (fun x => (x.lo, x.hi))) ((raw (⟨2, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp3_0_ok : RawF.check ctl A B pd i0 (raw (⟨3, by decide⟩ : Fin 1902)) rp3_0 = true := by decide +kernel

theorem rp3_1_ok : RawF.check ctl A B pd i0 (raw (⟨3, by decide⟩ : Fin 1902)) rp3_1 = true := by decide +kernel

theorem raw3_h : ((raw (⟨3, by decide⟩ : Fin 1902)).ok (rawMin (⟨3, by decide⟩ : Fin 1902)) && chainF ((raw (⟨3, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp3.map (fun x => (x.lo, x.hi))) ((raw (⟨3, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp4_0_ok : RawF.check ctl A B pd i0 (raw (⟨4, by decide⟩ : Fin 1902)) rp4_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
