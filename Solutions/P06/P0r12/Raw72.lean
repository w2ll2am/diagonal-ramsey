import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp232_47_ok : RawF.check ctl A B pd i0 (raw (⟨232, by decide⟩ : Fin 1902)) rp232_47 = true := by decide +kernel

theorem rp232_48_ok : RawF.check ctl A B pd i0 (raw (⟨232, by decide⟩ : Fin 1902)) rp232_48 = true := by decide +kernel

theorem raw232_h : ((raw (⟨232, by decide⟩ : Fin 1902)).ok (rawMin (⟨232, by decide⟩ : Fin 1902)) && chainF ((raw (⟨232, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp232.map (fun x => (x.lo, x.hi))) ((raw (⟨232, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp233_0_ok : RawF.check ctl A B pd i0 (raw (⟨233, by decide⟩ : Fin 1902)) rp233_0 = true := by decide +kernel

theorem rp233_1_ok : RawF.check ctl A B pd i0 (raw (⟨233, by decide⟩ : Fin 1902)) rp233_1 = true := by decide +kernel

theorem rp233_2_ok : RawF.check ctl A B pd i0 (raw (⟨233, by decide⟩ : Fin 1902)) rp233_2 = true := by decide +kernel

theorem rp233_3_ok : RawF.check ctl A B pd i0 (raw (⟨233, by decide⟩ : Fin 1902)) rp233_3 = true := by decide +kernel

theorem rp233_4_ok : RawF.check ctl A B pd i0 (raw (⟨233, by decide⟩ : Fin 1902)) rp233_4 = true := by decide +kernel

theorem rp233_5_ok : RawF.check ctl A B pd i0 (raw (⟨233, by decide⟩ : Fin 1902)) rp233_5 = true := by decide +kernel

theorem rp233_6_ok : RawF.check ctl A B pd i0 (raw (⟨233, by decide⟩ : Fin 1902)) rp233_6 = true := by decide +kernel

theorem rp233_7_ok : RawF.check ctl A B pd i0 (raw (⟨233, by decide⟩ : Fin 1902)) rp233_7 = true := by decide +kernel

theorem raw233_h : ((raw (⟨233, by decide⟩ : Fin 1902)).ok (rawMin (⟨233, by decide⟩ : Fin 1902)) && chainF ((raw (⟨233, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp233.map (fun x => (x.lo, x.hi))) ((raw (⟨233, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp234_0_ok : RawF.check ctl A B pd i0 (raw (⟨234, by decide⟩ : Fin 1902)) rp234_0 = true := by decide +kernel

theorem raw234_h : ((raw (⟨234, by decide⟩ : Fin 1902)).ok (rawMin (⟨234, by decide⟩ : Fin 1902)) && chainF ((raw (⟨234, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp234.map (fun x => (x.lo, x.hi))) ((raw (⟨234, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp235_0_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_0 = true := by decide +kernel

theorem rp235_1_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_1 = true := by decide +kernel

theorem rp235_2_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_2 = true := by decide +kernel

theorem rp235_3_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_3 = true := by decide +kernel

theorem rp235_4_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_4 = true := by decide +kernel

theorem rp235_5_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_5 = true := by decide +kernel

theorem rp235_6_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_6 = true := by decide +kernel

theorem rp235_7_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_7 = true := by decide +kernel

theorem rp235_8_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_8 = true := by decide +kernel

theorem rp235_9_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_9 = true := by decide +kernel

theorem rp235_10_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_10 = true := by decide +kernel

theorem rp235_11_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_11 = true := by decide +kernel

theorem rp235_12_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_12 = true := by decide +kernel

theorem rp235_13_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_13 = true := by decide +kernel

theorem rp235_14_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_14 = true := by decide +kernel

theorem rp235_15_ok : RawF.check ctl A B pd i0 (raw (⟨235, by decide⟩ : Fin 1902)) rp235_15 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
