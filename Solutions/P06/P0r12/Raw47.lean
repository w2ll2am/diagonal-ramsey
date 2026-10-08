import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp105_3_ok : RawF.check ctl A B pd i0 (raw (⟨105, by decide⟩ : Fin 1902)) rp105_3 = true := by decide +kernel

theorem rp105_4_ok : RawF.check ctl A B pd i0 (raw (⟨105, by decide⟩ : Fin 1902)) rp105_4 = true := by decide +kernel

theorem rp105_5_ok : RawF.check ctl A B pd i0 (raw (⟨105, by decide⟩ : Fin 1902)) rp105_5 = true := by decide +kernel

theorem rp105_6_ok : RawF.check ctl A B pd i0 (raw (⟨105, by decide⟩ : Fin 1902)) rp105_6 = true := by decide +kernel

theorem raw105_h : ((raw (⟨105, by decide⟩ : Fin 1902)).ok (rawMin (⟨105, by decide⟩ : Fin 1902)) && chainF ((raw (⟨105, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp105.map (fun x => (x.lo, x.hi))) ((raw (⟨105, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp106_0_ok : RawF.check ctl A B pd i0 (raw (⟨106, by decide⟩ : Fin 1902)) rp106_0 = true := by decide +kernel

theorem rp106_1_ok : RawF.check ctl A B pd i0 (raw (⟨106, by decide⟩ : Fin 1902)) rp106_1 = true := by decide +kernel

theorem raw106_h : ((raw (⟨106, by decide⟩ : Fin 1902)).ok (rawMin (⟨106, by decide⟩ : Fin 1902)) && chainF ((raw (⟨106, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp106.map (fun x => (x.lo, x.hi))) ((raw (⟨106, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp107_0_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_0 = true := by decide +kernel

theorem rp107_1_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_1 = true := by decide +kernel

theorem rp107_2_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_2 = true := by decide +kernel

theorem rp107_3_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_3 = true := by decide +kernel

theorem rp107_4_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_4 = true := by decide +kernel

theorem rp107_5_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_5 = true := by decide +kernel

theorem rp107_6_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_6 = true := by decide +kernel

theorem rp107_7_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_7 = true := by decide +kernel

theorem rp107_8_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_8 = true := by decide +kernel

theorem rp107_9_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_9 = true := by decide +kernel

theorem rp107_10_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_10 = true := by decide +kernel

theorem rp107_11_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_11 = true := by decide +kernel

theorem rp107_12_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_12 = true := by decide +kernel

theorem rp107_13_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_13 = true := by decide +kernel

theorem rp107_14_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_14 = true := by decide +kernel

theorem rp107_15_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_15 = true := by decide +kernel

theorem rp107_16_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_16 = true := by decide +kernel

theorem rp107_17_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_17 = true := by decide +kernel

theorem rp107_18_ok : RawF.check ctl A B pd i0 (raw (⟨107, by decide⟩ : Fin 1902)) rp107_18 = true := by decide +kernel

theorem raw107_h : ((raw (⟨107, by decide⟩ : Fin 1902)).ok (rawMin (⟨107, by decide⟩ : Fin 1902)) && chainF ((raw (⟨107, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp107.map (fun x => (x.lo, x.hi))) ((raw (⟨107, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp108_0_ok : RawF.check ctl A B pd i0 (raw (⟨108, by decide⟩ : Fin 1902)) rp108_0 = true := by decide +kernel

theorem rp108_1_ok : RawF.check ctl A B pd i0 (raw (⟨108, by decide⟩ : Fin 1902)) rp108_1 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
