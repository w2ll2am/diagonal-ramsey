import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp103_3_ok : RawF.check ctl A B pd i0 (raw (⟨103, by decide⟩ : Fin 1902)) rp103_3 = true := by decide +kernel

theorem rp103_4_ok : RawF.check ctl A B pd i0 (raw (⟨103, by decide⟩ : Fin 1902)) rp103_4 = true := by decide +kernel

theorem rp103_5_ok : RawF.check ctl A B pd i0 (raw (⟨103, by decide⟩ : Fin 1902)) rp103_5 = true := by decide +kernel

theorem rp103_6_ok : RawF.check ctl A B pd i0 (raw (⟨103, by decide⟩ : Fin 1902)) rp103_6 = true := by decide +kernel

theorem rp103_7_ok : RawF.check ctl A B pd i0 (raw (⟨103, by decide⟩ : Fin 1902)) rp103_7 = true := by decide +kernel

theorem raw103_h : ((raw (⟨103, by decide⟩ : Fin 1902)).ok (rawMin (⟨103, by decide⟩ : Fin 1902)) && chainF ((raw (⟨103, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp103.map (fun x => (x.lo, x.hi))) ((raw (⟨103, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp104_0_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_0 = true := by decide +kernel

theorem rp104_1_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_1 = true := by decide +kernel

theorem rp104_2_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_2 = true := by decide +kernel

theorem rp104_3_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_3 = true := by decide +kernel

theorem rp104_4_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_4 = true := by decide +kernel

theorem rp104_5_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_5 = true := by decide +kernel

theorem rp104_6_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_6 = true := by decide +kernel

theorem rp104_7_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_7 = true := by decide +kernel

theorem rp104_8_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_8 = true := by decide +kernel

theorem rp104_9_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_9 = true := by decide +kernel

theorem rp104_10_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_10 = true := by decide +kernel

theorem rp104_11_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_11 = true := by decide +kernel

theorem rp104_12_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_12 = true := by decide +kernel

theorem rp104_13_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_13 = true := by decide +kernel

theorem rp104_14_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_14 = true := by decide +kernel

theorem rp104_15_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_15 = true := by decide +kernel

theorem rp104_16_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_16 = true := by decide +kernel

theorem rp104_17_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_17 = true := by decide +kernel

theorem rp104_18_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_18 = true := by decide +kernel

theorem rp104_19_ok : RawF.check ctl A B pd i0 (raw (⟨104, by decide⟩ : Fin 1902)) rp104_19 = true := by decide +kernel

theorem raw104_h : ((raw (⟨104, by decide⟩ : Fin 1902)).ok (rawMin (⟨104, by decide⟩ : Fin 1902)) && chainF ((raw (⟨104, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp104.map (fun x => (x.lo, x.hi))) ((raw (⟨104, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp105_0_ok : RawF.check ctl A B pd i0 (raw (⟨105, by decide⟩ : Fin 1902)) rp105_0 = true := by decide +kernel

theorem rp105_1_ok : RawF.check ctl A B pd i0 (raw (⟨105, by decide⟩ : Fin 1902)) rp105_1 = true := by decide +kernel

theorem rp105_2_ok : RawF.check ctl A B pd i0 (raw (⟨105, by decide⟩ : Fin 1902)) rp105_2 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
