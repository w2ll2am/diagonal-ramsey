import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp451_2_ok : RawF.check ctl A B pd i0 (raw (⟨451, by decide⟩ : Fin 1902)) rp451_2 = true := by decide +kernel

theorem rp451_3_ok : RawF.check ctl A B pd i0 (raw (⟨451, by decide⟩ : Fin 1902)) rp451_3 = true := by decide +kernel

theorem rp451_4_ok : RawF.check ctl A B pd i0 (raw (⟨451, by decide⟩ : Fin 1902)) rp451_4 = true := by decide +kernel

theorem rp451_5_ok : RawF.check ctl A B pd i0 (raw (⟨451, by decide⟩ : Fin 1902)) rp451_5 = true := by decide +kernel

theorem rp451_6_ok : RawF.check ctl A B pd i0 (raw (⟨451, by decide⟩ : Fin 1902)) rp451_6 = true := by decide +kernel

theorem raw451_h : ((raw (⟨451, by decide⟩ : Fin 1902)).ok (rawMin (⟨451, by decide⟩ : Fin 1902)) && chainF ((raw (⟨451, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp451.map (fun x => (x.lo, x.hi))) ((raw (⟨451, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp452_0_ok : RawF.check ctl A B pd i0 (raw (⟨452, by decide⟩ : Fin 1902)) rp452_0 = true := by decide +kernel

theorem rp452_1_ok : RawF.check ctl A B pd i0 (raw (⟨452, by decide⟩ : Fin 1902)) rp452_1 = true := by decide +kernel

theorem raw452_h : ((raw (⟨452, by decide⟩ : Fin 1902)).ok (rawMin (⟨452, by decide⟩ : Fin 1902)) && chainF ((raw (⟨452, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp452.map (fun x => (x.lo, x.hi))) ((raw (⟨452, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp453_0_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_0 = true := by decide +kernel

theorem rp453_1_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_1 = true := by decide +kernel

theorem rp453_2_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_2 = true := by decide +kernel

theorem rp453_3_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_3 = true := by decide +kernel

theorem rp453_4_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_4 = true := by decide +kernel

theorem rp453_5_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_5 = true := by decide +kernel

theorem rp453_6_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_6 = true := by decide +kernel

theorem rp453_7_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_7 = true := by decide +kernel

theorem rp453_8_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_8 = true := by decide +kernel

theorem rp453_9_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_9 = true := by decide +kernel

theorem rp453_10_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_10 = true := by decide +kernel

theorem rp453_11_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_11 = true := by decide +kernel

theorem rp453_12_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_12 = true := by decide +kernel

theorem rp453_13_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_13 = true := by decide +kernel

theorem rp453_14_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_14 = true := by decide +kernel

theorem rp453_15_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_15 = true := by decide +kernel

theorem rp453_16_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_16 = true := by decide +kernel

theorem rp453_17_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_17 = true := by decide +kernel

theorem rp453_18_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_18 = true := by decide +kernel

theorem rp453_19_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_19 = true := by decide +kernel

theorem rp453_20_ok : RawF.check ctl A B pd i0 (raw (⟨453, by decide⟩ : Fin 1902)) rp453_20 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
