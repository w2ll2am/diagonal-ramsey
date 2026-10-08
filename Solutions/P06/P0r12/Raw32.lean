import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp80_2_ok : RawF.check ctl A B pd i0 (raw (⟨80, by decide⟩ : Fin 1902)) rp80_2 = true := by decide +kernel

theorem raw80_h : ((raw (⟨80, by decide⟩ : Fin 1902)).ok (rawMin (⟨80, by decide⟩ : Fin 1902)) && chainF ((raw (⟨80, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp80.map (fun x => (x.lo, x.hi))) ((raw (⟨80, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp81_0_ok : RawF.check ctl A B pd i0 (raw (⟨81, by decide⟩ : Fin 1902)) rp81_0 = true := by decide +kernel

theorem rp81_1_ok : RawF.check ctl A B pd i0 (raw (⟨81, by decide⟩ : Fin 1902)) rp81_1 = true := by decide +kernel

theorem rp81_2_ok : RawF.check ctl A B pd i0 (raw (⟨81, by decide⟩ : Fin 1902)) rp81_2 = true := by decide +kernel

theorem rp81_3_ok : RawF.check ctl A B pd i0 (raw (⟨81, by decide⟩ : Fin 1902)) rp81_3 = true := by decide +kernel

theorem rp81_4_ok : RawF.check ctl A B pd i0 (raw (⟨81, by decide⟩ : Fin 1902)) rp81_4 = true := by decide +kernel

theorem rp81_5_ok : RawF.check ctl A B pd i0 (raw (⟨81, by decide⟩ : Fin 1902)) rp81_5 = true := by decide +kernel

theorem rp81_6_ok : RawF.check ctl A B pd i0 (raw (⟨81, by decide⟩ : Fin 1902)) rp81_6 = true := by decide +kernel

theorem raw81_h : ((raw (⟨81, by decide⟩ : Fin 1902)).ok (rawMin (⟨81, by decide⟩ : Fin 1902)) && chainF ((raw (⟨81, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp81.map (fun x => (x.lo, x.hi))) ((raw (⟨81, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp82_0_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_0 = true := by decide +kernel

theorem rp82_1_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_1 = true := by decide +kernel

theorem rp82_2_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_2 = true := by decide +kernel

theorem rp82_3_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_3 = true := by decide +kernel

theorem rp82_4_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_4 = true := by decide +kernel

theorem rp82_5_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_5 = true := by decide +kernel

theorem rp82_6_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_6 = true := by decide +kernel

theorem rp82_7_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_7 = true := by decide +kernel

theorem rp82_8_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_8 = true := by decide +kernel

theorem rp82_9_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_9 = true := by decide +kernel

theorem rp82_10_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_10 = true := by decide +kernel

theorem rp82_11_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_11 = true := by decide +kernel

theorem rp82_12_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_12 = true := by decide +kernel

theorem rp82_13_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_13 = true := by decide +kernel

theorem rp82_14_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_14 = true := by decide +kernel

theorem rp82_15_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_15 = true := by decide +kernel

theorem rp82_16_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_16 = true := by decide +kernel

theorem rp82_17_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_17 = true := by decide +kernel

theorem rp82_18_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_18 = true := by decide +kernel

theorem rp82_19_ok : RawF.check ctl A B pd i0 (raw (⟨82, by decide⟩ : Fin 1902)) rp82_19 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
