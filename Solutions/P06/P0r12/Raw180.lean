import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D9

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp555_0_ok : RawF.check ctl A B pd i0 (raw (⟨555, by decide⟩ : Fin 1902)) rp555_0 = true := by decide +kernel

theorem rp555_1_ok : RawF.check ctl A B pd i0 (raw (⟨555, by decide⟩ : Fin 1902)) rp555_1 = true := by decide +kernel

theorem raw555_h : ((raw (⟨555, by decide⟩ : Fin 1902)).ok (rawMin (⟨555, by decide⟩ : Fin 1902)) && chainF ((raw (⟨555, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp555.map (fun x => (x.lo, x.hi))) ((raw (⟨555, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp556_0_ok : RawF.check ctl A B pd i0 (raw (⟨556, by decide⟩ : Fin 1902)) rp556_0 = true := by decide +kernel

theorem rp556_1_ok : RawF.check ctl A B pd i0 (raw (⟨556, by decide⟩ : Fin 1902)) rp556_1 = true := by decide +kernel

theorem rp556_2_ok : RawF.check ctl A B pd i0 (raw (⟨556, by decide⟩ : Fin 1902)) rp556_2 = true := by decide +kernel

theorem rp556_3_ok : RawF.check ctl A B pd i0 (raw (⟨556, by decide⟩ : Fin 1902)) rp556_3 = true := by decide +kernel

theorem rp556_4_ok : RawF.check ctl A B pd i0 (raw (⟨556, by decide⟩ : Fin 1902)) rp556_4 = true := by decide +kernel

theorem rp556_5_ok : RawF.check ctl A B pd i0 (raw (⟨556, by decide⟩ : Fin 1902)) rp556_5 = true := by decide +kernel

theorem raw556_h : ((raw (⟨556, by decide⟩ : Fin 1902)).ok (rawMin (⟨556, by decide⟩ : Fin 1902)) && chainF ((raw (⟨556, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp556.map (fun x => (x.lo, x.hi))) ((raw (⟨556, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp557_0_ok : RawF.check ctl A B pd i0 (raw (⟨557, by decide⟩ : Fin 1902)) rp557_0 = true := by decide +kernel

theorem raw557_h : ((raw (⟨557, by decide⟩ : Fin 1902)).ok (rawMin (⟨557, by decide⟩ : Fin 1902)) && chainF ((raw (⟨557, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp557.map (fun x => (x.lo, x.hi))) ((raw (⟨557, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp558_0_ok : RawF.check ctl A B pd i0 (raw (⟨558, by decide⟩ : Fin 1902)) rp558_0 = true := by decide +kernel

theorem rp558_1_ok : RawF.check ctl A B pd i0 (raw (⟨558, by decide⟩ : Fin 1902)) rp558_1 = true := by decide +kernel

theorem raw558_h : ((raw (⟨558, by decide⟩ : Fin 1902)).ok (rawMin (⟨558, by decide⟩ : Fin 1902)) && chainF ((raw (⟨558, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp558.map (fun x => (x.lo, x.hi))) ((raw (⟨558, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp559_0_ok : RawF.check ctl A B pd i0 (raw (⟨559, by decide⟩ : Fin 1902)) rp559_0 = true := by decide +kernel

theorem raw559_h : ((raw (⟨559, by decide⟩ : Fin 1902)).ok (rawMin (⟨559, by decide⟩ : Fin 1902)) && chainF ((raw (⟨559, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp559.map (fun x => (x.lo, x.hi))) ((raw (⟨559, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp560_0_ok : RawF.check ctl A B pd i0 (raw (⟨560, by decide⟩ : Fin 1902)) rp560_0 = true := by decide +kernel

theorem raw560_h : ((raw (⟨560, by decide⟩ : Fin 1902)).ok (rawMin (⟨560, by decide⟩ : Fin 1902)) && chainF ((raw (⟨560, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp560.map (fun x => (x.lo, x.hi))) ((raw (⟨560, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp561_0_ok : RawF.check ctl A B pd i0 (raw (⟨561, by decide⟩ : Fin 1902)) rp561_0 = true := by decide +kernel

theorem rp561_1_ok : RawF.check ctl A B pd i0 (raw (⟨561, by decide⟩ : Fin 1902)) rp561_1 = true := by decide +kernel

theorem rp561_2_ok : RawF.check ctl A B pd i0 (raw (⟨561, by decide⟩ : Fin 1902)) rp561_2 = true := by decide +kernel

theorem raw561_h : ((raw (⟨561, by decide⟩ : Fin 1902)).ok (rawMin (⟨561, by decide⟩ : Fin 1902)) && chainF ((raw (⟨561, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp561.map (fun x => (x.lo, x.hi))) ((raw (⟨561, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp562_0_ok : RawF.check ctl A B pd i0 (raw (⟨562, by decide⟩ : Fin 1902)) rp562_0 = true := by decide +kernel

theorem rp562_1_ok : RawF.check ctl A B pd i0 (raw (⟨562, by decide⟩ : Fin 1902)) rp562_1 = true := by decide +kernel

theorem rp562_2_ok : RawF.check ctl A B pd i0 (raw (⟨562, by decide⟩ : Fin 1902)) rp562_2 = true := by decide +kernel

theorem raw562_h : ((raw (⟨562, by decide⟩ : Fin 1902)).ok (rawMin (⟨562, by decide⟩ : Fin 1902)) && chainF ((raw (⟨562, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp562.map (fun x => (x.lo, x.hi))) ((raw (⟨562, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp563_0_ok : RawF.check ctl A B pd i0 (raw (⟨563, by decide⟩ : Fin 1902)) rp563_0 = true := by decide +kernel

theorem rp563_1_ok : RawF.check ctl A B pd i0 (raw (⟨563, by decide⟩ : Fin 1902)) rp563_1 = true := by decide +kernel

theorem rp563_2_ok : RawF.check ctl A B pd i0 (raw (⟨563, by decide⟩ : Fin 1902)) rp563_2 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
