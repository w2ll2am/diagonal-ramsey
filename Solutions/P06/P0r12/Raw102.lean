import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp293_5_ok : RawF.check ctl A B pd i0 (raw (⟨293, by decide⟩ : Fin 1902)) rp293_5 = true := by decide +kernel

theorem rp293_6_ok : RawF.check ctl A B pd i0 (raw (⟨293, by decide⟩ : Fin 1902)) rp293_6 = true := by decide +kernel

theorem raw293_h : ((raw (⟨293, by decide⟩ : Fin 1902)).ok (rawMin (⟨293, by decide⟩ : Fin 1902)) && chainF ((raw (⟨293, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp293.map (fun x => (x.lo, x.hi))) ((raw (⟨293, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp294_0_ok : RawF.check ctl A B pd i0 (raw (⟨294, by decide⟩ : Fin 1902)) rp294_0 = true := by decide +kernel

theorem raw294_h : ((raw (⟨294, by decide⟩ : Fin 1902)).ok (rawMin (⟨294, by decide⟩ : Fin 1902)) && chainF ((raw (⟨294, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp294.map (fun x => (x.lo, x.hi))) ((raw (⟨294, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp295_0_ok : RawF.check ctl A B pd i0 (raw (⟨295, by decide⟩ : Fin 1902)) rp295_0 = true := by decide +kernel

theorem rp295_1_ok : RawF.check ctl A B pd i0 (raw (⟨295, by decide⟩ : Fin 1902)) rp295_1 = true := by decide +kernel

theorem raw295_h : ((raw (⟨295, by decide⟩ : Fin 1902)).ok (rawMin (⟨295, by decide⟩ : Fin 1902)) && chainF ((raw (⟨295, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp295.map (fun x => (x.lo, x.hi))) ((raw (⟨295, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp296_0_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_0 = true := by decide +kernel

theorem rp296_1_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_1 = true := by decide +kernel

theorem rp296_2_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_2 = true := by decide +kernel

theorem rp296_3_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_3 = true := by decide +kernel

theorem rp296_4_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_4 = true := by decide +kernel

theorem rp296_5_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_5 = true := by decide +kernel

theorem rp296_6_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_6 = true := by decide +kernel

theorem rp296_7_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_7 = true := by decide +kernel

theorem rp296_8_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_8 = true := by decide +kernel

theorem rp296_9_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_9 = true := by decide +kernel

theorem rp296_10_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_10 = true := by decide +kernel

theorem rp296_11_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_11 = true := by decide +kernel

theorem rp296_12_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_12 = true := by decide +kernel

theorem rp296_13_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_13 = true := by decide +kernel

theorem rp296_14_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_14 = true := by decide +kernel

theorem rp296_15_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_15 = true := by decide +kernel

theorem rp296_16_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_16 = true := by decide +kernel

theorem rp296_17_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_17 = true := by decide +kernel

theorem rp296_18_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_18 = true := by decide +kernel

theorem rp296_19_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_19 = true := by decide +kernel

theorem rp296_20_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_20 = true := by decide +kernel

theorem rp296_21_ok : RawF.check ctl A B pd i0 (raw (⟨296, by decide⟩ : Fin 1902)) rp296_21 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
