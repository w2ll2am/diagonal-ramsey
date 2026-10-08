import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp624_0_ok : RawF.check ctl A B pd i0 (raw (⟨624, by decide⟩ : Fin 1902)) rp624_0 = true := by decide +kernel

theorem rp624_1_ok : RawF.check ctl A B pd i0 (raw (⟨624, by decide⟩ : Fin 1902)) rp624_1 = true := by decide +kernel

theorem rp624_2_ok : RawF.check ctl A B pd i0 (raw (⟨624, by decide⟩ : Fin 1902)) rp624_2 = true := by decide +kernel

theorem rp624_3_ok : RawF.check ctl A B pd i0 (raw (⟨624, by decide⟩ : Fin 1902)) rp624_3 = true := by decide +kernel

theorem rp624_4_ok : RawF.check ctl A B pd i0 (raw (⟨624, by decide⟩ : Fin 1902)) rp624_4 = true := by decide +kernel

theorem rp624_5_ok : RawF.check ctl A B pd i0 (raw (⟨624, by decide⟩ : Fin 1902)) rp624_5 = true := by decide +kernel

theorem rp624_6_ok : RawF.check ctl A B pd i0 (raw (⟨624, by decide⟩ : Fin 1902)) rp624_6 = true := by decide +kernel

theorem raw624_h : ((raw (⟨624, by decide⟩ : Fin 1902)).ok (rawMin (⟨624, by decide⟩ : Fin 1902)) && chainF ((raw (⟨624, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp624.map (fun x => (x.lo, x.hi))) ((raw (⟨624, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp625_0_ok : RawF.check ctl A B pd i0 (raw (⟨625, by decide⟩ : Fin 1902)) rp625_0 = true := by decide +kernel

theorem raw625_h : ((raw (⟨625, by decide⟩ : Fin 1902)).ok (rawMin (⟨625, by decide⟩ : Fin 1902)) && chainF ((raw (⟨625, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp625.map (fun x => (x.lo, x.hi))) ((raw (⟨625, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp626_0_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_0 = true := by decide +kernel

theorem rp626_1_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_1 = true := by decide +kernel

theorem rp626_2_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_2 = true := by decide +kernel

theorem rp626_3_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_3 = true := by decide +kernel

theorem rp626_4_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_4 = true := by decide +kernel

theorem rp626_5_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_5 = true := by decide +kernel

theorem rp626_6_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_6 = true := by decide +kernel

theorem rp626_7_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_7 = true := by decide +kernel

theorem rp626_8_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_8 = true := by decide +kernel

theorem rp626_9_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_9 = true := by decide +kernel

theorem rp626_10_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_10 = true := by decide +kernel

theorem rp626_11_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_11 = true := by decide +kernel

theorem rp626_12_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_12 = true := by decide +kernel

theorem rp626_13_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_13 = true := by decide +kernel

theorem rp626_14_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_14 = true := by decide +kernel

theorem rp626_15_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_15 = true := by decide +kernel

theorem rp626_16_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_16 = true := by decide +kernel

theorem rp626_17_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_17 = true := by decide +kernel

theorem rp626_18_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_18 = true := by decide +kernel

theorem rp626_19_ok : RawF.check ctl A B pd i0 (raw (⟨626, by decide⟩ : Fin 1902)) rp626_19 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
