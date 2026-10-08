import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp86_50_ok : RawF.check ctl A B pd i0 (raw (⟨86, by decide⟩ : Fin 1902)) rp86_50 = true := by decide +kernel

theorem raw86_h : ((raw (⟨86, by decide⟩ : Fin 1902)).ok (rawMin (⟨86, by decide⟩ : Fin 1902)) && chainF ((raw (⟨86, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp86.map (fun x => (x.lo, x.hi))) ((raw (⟨86, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp87_0_ok : RawF.check ctl A B pd i0 (raw (⟨87, by decide⟩ : Fin 1902)) rp87_0 = true := by decide +kernel

theorem rp87_1_ok : RawF.check ctl A B pd i0 (raw (⟨87, by decide⟩ : Fin 1902)) rp87_1 = true := by decide +kernel

theorem rp87_2_ok : RawF.check ctl A B pd i0 (raw (⟨87, by decide⟩ : Fin 1902)) rp87_2 = true := by decide +kernel

theorem rp87_3_ok : RawF.check ctl A B pd i0 (raw (⟨87, by decide⟩ : Fin 1902)) rp87_3 = true := by decide +kernel

theorem rp87_4_ok : RawF.check ctl A B pd i0 (raw (⟨87, by decide⟩ : Fin 1902)) rp87_4 = true := by decide +kernel

theorem raw87_h : ((raw (⟨87, by decide⟩ : Fin 1902)).ok (rawMin (⟨87, by decide⟩ : Fin 1902)) && chainF ((raw (⟨87, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp87.map (fun x => (x.lo, x.hi))) ((raw (⟨87, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp88_0_ok : RawF.check ctl A B pd i0 (raw (⟨88, by decide⟩ : Fin 1902)) rp88_0 = true := by decide +kernel

theorem rp88_1_ok : RawF.check ctl A B pd i0 (raw (⟨88, by decide⟩ : Fin 1902)) rp88_1 = true := by decide +kernel

theorem rp88_2_ok : RawF.check ctl A B pd i0 (raw (⟨88, by decide⟩ : Fin 1902)) rp88_2 = true := by decide +kernel

theorem rp88_3_ok : RawF.check ctl A B pd i0 (raw (⟨88, by decide⟩ : Fin 1902)) rp88_3 = true := by decide +kernel

theorem rp88_4_ok : RawF.check ctl A B pd i0 (raw (⟨88, by decide⟩ : Fin 1902)) rp88_4 = true := by decide +kernel

theorem rp88_5_ok : RawF.check ctl A B pd i0 (raw (⟨88, by decide⟩ : Fin 1902)) rp88_5 = true := by decide +kernel

theorem rp88_6_ok : RawF.check ctl A B pd i0 (raw (⟨88, by decide⟩ : Fin 1902)) rp88_6 = true := by decide +kernel

theorem raw88_h : ((raw (⟨88, by decide⟩ : Fin 1902)).ok (rawMin (⟨88, by decide⟩ : Fin 1902)) && chainF ((raw (⟨88, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp88.map (fun x => (x.lo, x.hi))) ((raw (⟨88, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp89_0_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_0 = true := by decide +kernel

theorem rp89_1_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_1 = true := by decide +kernel

theorem rp89_2_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_2 = true := by decide +kernel

theorem rp89_3_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_3 = true := by decide +kernel

theorem rp89_4_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_4 = true := by decide +kernel

theorem rp89_5_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_5 = true := by decide +kernel

theorem rp89_6_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_6 = true := by decide +kernel

theorem rp89_7_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_7 = true := by decide +kernel

theorem rp89_8_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_8 = true := by decide +kernel

theorem rp89_9_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_9 = true := by decide +kernel

theorem rp89_10_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_10 = true := by decide +kernel

theorem rp89_11_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_11 = true := by decide +kernel

theorem rp89_12_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_12 = true := by decide +kernel

theorem rp89_13_ok : RawF.check ctl A B pd i0 (raw (⟨89, by decide⟩ : Fin 1902)) rp89_13 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
