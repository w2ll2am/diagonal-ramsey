import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp256_59_ok : RawF.check ctl A B pd i0 (raw (⟨256, by decide⟩ : Fin 1902)) rp256_59 = true := by decide +kernel

theorem rp256_60_ok : RawF.check ctl A B pd i0 (raw (⟨256, by decide⟩ : Fin 1902)) rp256_60 = true := by decide +kernel

theorem raw256_h : ((raw (⟨256, by decide⟩ : Fin 1902)).ok (rawMin (⟨256, by decide⟩ : Fin 1902)) && chainF ((raw (⟨256, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp256.map (fun x => (x.lo, x.hi))) ((raw (⟨256, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp257_0_ok : RawF.check ctl A B pd i0 (raw (⟨257, by decide⟩ : Fin 1902)) rp257_0 = true := by decide +kernel

theorem rp257_1_ok : RawF.check ctl A B pd i0 (raw (⟨257, by decide⟩ : Fin 1902)) rp257_1 = true := by decide +kernel

theorem rp257_2_ok : RawF.check ctl A B pd i0 (raw (⟨257, by decide⟩ : Fin 1902)) rp257_2 = true := by decide +kernel

theorem rp257_3_ok : RawF.check ctl A B pd i0 (raw (⟨257, by decide⟩ : Fin 1902)) rp257_3 = true := by decide +kernel

theorem rp257_4_ok : RawF.check ctl A B pd i0 (raw (⟨257, by decide⟩ : Fin 1902)) rp257_4 = true := by decide +kernel

theorem rp257_5_ok : RawF.check ctl A B pd i0 (raw (⟨257, by decide⟩ : Fin 1902)) rp257_5 = true := by decide +kernel

theorem rp257_6_ok : RawF.check ctl A B pd i0 (raw (⟨257, by decide⟩ : Fin 1902)) rp257_6 = true := by decide +kernel

theorem rp257_7_ok : RawF.check ctl A B pd i0 (raw (⟨257, by decide⟩ : Fin 1902)) rp257_7 = true := by decide +kernel

theorem raw257_h : ((raw (⟨257, by decide⟩ : Fin 1902)).ok (rawMin (⟨257, by decide⟩ : Fin 1902)) && chainF ((raw (⟨257, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp257.map (fun x => (x.lo, x.hi))) ((raw (⟨257, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp258_0_ok : RawF.check ctl A B pd i0 (raw (⟨258, by decide⟩ : Fin 1902)) rp258_0 = true := by decide +kernel

theorem raw258_h : ((raw (⟨258, by decide⟩ : Fin 1902)).ok (rawMin (⟨258, by decide⟩ : Fin 1902)) && chainF ((raw (⟨258, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp258.map (fun x => (x.lo, x.hi))) ((raw (⟨258, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp259_0_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_0 = true := by decide +kernel

theorem rp259_1_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_1 = true := by decide +kernel

theorem rp259_2_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_2 = true := by decide +kernel

theorem rp259_3_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_3 = true := by decide +kernel

theorem rp259_4_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_4 = true := by decide +kernel

theorem rp259_5_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_5 = true := by decide +kernel

theorem rp259_6_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_6 = true := by decide +kernel

theorem rp259_7_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_7 = true := by decide +kernel

theorem rp259_8_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_8 = true := by decide +kernel

theorem rp259_9_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_9 = true := by decide +kernel

theorem rp259_10_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_10 = true := by decide +kernel

theorem rp259_11_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_11 = true := by decide +kernel

theorem rp259_12_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_12 = true := by decide +kernel

theorem rp259_13_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_13 = true := by decide +kernel

theorem rp259_14_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_14 = true := by decide +kernel

theorem rp259_15_ok : RawF.check ctl A B pd i0 (raw (⟨259, by decide⟩ : Fin 1902)) rp259_15 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
