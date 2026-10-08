import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp902_12_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_12 = true := by decide +kernel

theorem rp902_13_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_13 = true := by decide +kernel

theorem rp902_14_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_14 = true := by decide +kernel

theorem rp902_15_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_15 = true := by decide +kernel

theorem rp902_16_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_16 = true := by decide +kernel

theorem rp902_17_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_17 = true := by decide +kernel

theorem rp902_18_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_18 = true := by decide +kernel

theorem rp902_19_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_19 = true := by decide +kernel

theorem rp902_20_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_20 = true := by decide +kernel

theorem rp902_21_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_21 = true := by decide +kernel

theorem rp902_22_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_22 = true := by decide +kernel

theorem rp902_23_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_23 = true := by decide +kernel

theorem rp902_24_ok : RawF.check ctl A B pd i0 (raw (⟨902, by decide⟩ : Fin 1902)) rp902_24 = true := by decide +kernel

theorem raw902_h : ((raw (⟨902, by decide⟩ : Fin 1902)).ok (rawMin (⟨902, by decide⟩ : Fin 1902)) && chainF ((raw (⟨902, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp902.map (fun x => (x.lo, x.hi))) ((raw (⟨902, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp903_0_ok : RawF.check ctl A B pd i0 (raw (⟨903, by decide⟩ : Fin 1902)) rp903_0 = true := by decide +kernel

theorem rp903_1_ok : RawF.check ctl A B pd i0 (raw (⟨903, by decide⟩ : Fin 1902)) rp903_1 = true := by decide +kernel

theorem rp903_2_ok : RawF.check ctl A B pd i0 (raw (⟨903, by decide⟩ : Fin 1902)) rp903_2 = true := by decide +kernel

theorem rp903_3_ok : RawF.check ctl A B pd i0 (raw (⟨903, by decide⟩ : Fin 1902)) rp903_3 = true := by decide +kernel

theorem rp903_4_ok : RawF.check ctl A B pd i0 (raw (⟨903, by decide⟩ : Fin 1902)) rp903_4 = true := by decide +kernel

theorem rp903_5_ok : RawF.check ctl A B pd i0 (raw (⟨903, by decide⟩ : Fin 1902)) rp903_5 = true := by decide +kernel

theorem rp903_6_ok : RawF.check ctl A B pd i0 (raw (⟨903, by decide⟩ : Fin 1902)) rp903_6 = true := by decide +kernel

theorem rp903_7_ok : RawF.check ctl A B pd i0 (raw (⟨903, by decide⟩ : Fin 1902)) rp903_7 = true := by decide +kernel

theorem raw903_h : ((raw (⟨903, by decide⟩ : Fin 1902)).ok (rawMin (⟨903, by decide⟩ : Fin 1902)) && chainF ((raw (⟨903, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp903.map (fun x => (x.lo, x.hi))) ((raw (⟨903, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp904_0_ok : RawF.check ctl A B pd i0 (raw (⟨904, by decide⟩ : Fin 1902)) rp904_0 = true := by decide +kernel

theorem rp904_1_ok : RawF.check ctl A B pd i0 (raw (⟨904, by decide⟩ : Fin 1902)) rp904_1 = true := by decide +kernel

theorem rp904_2_ok : RawF.check ctl A B pd i0 (raw (⟨904, by decide⟩ : Fin 1902)) rp904_2 = true := by decide +kernel

theorem raw904_h : ((raw (⟨904, by decide⟩ : Fin 1902)).ok (rawMin (⟨904, by decide⟩ : Fin 1902)) && chainF ((raw (⟨904, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp904.map (fun x => (x.lo, x.hi))) ((raw (⟨904, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp905_0_ok : RawF.check ctl A B pd i0 (raw (⟨905, by decide⟩ : Fin 1902)) rp905_0 = true := by decide +kernel

theorem rp905_1_ok : RawF.check ctl A B pd i0 (raw (⟨905, by decide⟩ : Fin 1902)) rp905_1 = true := by decide +kernel

theorem rp905_2_ok : RawF.check ctl A B pd i0 (raw (⟨905, by decide⟩ : Fin 1902)) rp905_2 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
