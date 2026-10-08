import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D11
import Solutions.P06.P0r12.D12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp633_132_ok : RawF.check ctl A B pd i0 (raw (⟨633, by decide⟩ : Fin 1902)) rp633_132 = true := by decide +kernel

theorem rp633_133_ok : RawF.check ctl A B pd i0 (raw (⟨633, by decide⟩ : Fin 1902)) rp633_133 = true := by decide +kernel

theorem rp633_134_ok : RawF.check ctl A B pd i0 (raw (⟨633, by decide⟩ : Fin 1902)) rp633_134 = true := by decide +kernel

theorem rp633_135_ok : RawF.check ctl A B pd i0 (raw (⟨633, by decide⟩ : Fin 1902)) rp633_135 = true := by decide +kernel

theorem rp633_136_ok : RawF.check ctl A B pd i0 (raw (⟨633, by decide⟩ : Fin 1902)) rp633_136 = true := by decide +kernel

theorem raw633_h : ((raw (⟨633, by decide⟩ : Fin 1902)).ok (rawMin (⟨633, by decide⟩ : Fin 1902)) && chainF ((raw (⟨633, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp633.map (fun x => (x.lo, x.hi))) ((raw (⟨633, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp634_0_ok : RawF.check ctl A B pd i0 (raw (⟨634, by decide⟩ : Fin 1902)) rp634_0 = true := by decide +kernel

theorem rp634_1_ok : RawF.check ctl A B pd i0 (raw (⟨634, by decide⟩ : Fin 1902)) rp634_1 = true := by decide +kernel

theorem rp634_2_ok : RawF.check ctl A B pd i0 (raw (⟨634, by decide⟩ : Fin 1902)) rp634_2 = true := by decide +kernel

theorem rp634_3_ok : RawF.check ctl A B pd i0 (raw (⟨634, by decide⟩ : Fin 1902)) rp634_3 = true := by decide +kernel

theorem raw634_h : ((raw (⟨634, by decide⟩ : Fin 1902)).ok (rawMin (⟨634, by decide⟩ : Fin 1902)) && chainF ((raw (⟨634, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp634.map (fun x => (x.lo, x.hi))) ((raw (⟨634, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp635_0_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_0 = true := by decide +kernel

theorem rp635_1_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_1 = true := by decide +kernel

theorem rp635_2_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_2 = true := by decide +kernel

theorem rp635_3_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_3 = true := by decide +kernel

theorem rp635_4_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_4 = true := by decide +kernel

theorem rp635_5_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_5 = true := by decide +kernel

theorem rp635_6_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_6 = true := by decide +kernel

theorem rp635_7_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_7 = true := by decide +kernel

theorem rp635_8_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_8 = true := by decide +kernel

theorem rp635_9_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_9 = true := by decide +kernel

theorem rp635_10_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_10 = true := by decide +kernel

theorem rp635_11_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_11 = true := by decide +kernel

theorem rp635_12_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_12 = true := by decide +kernel

theorem rp635_13_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_13 = true := by decide +kernel

theorem rp635_14_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_14 = true := by decide +kernel

theorem rp635_15_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_15 = true := by decide +kernel

theorem rp635_16_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_16 = true := by decide +kernel

theorem rp635_17_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_17 = true := by decide +kernel

theorem rp635_18_ok : RawF.check ctl A B pd i0 (raw (⟨635, by decide⟩ : Fin 1902)) rp635_18 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
