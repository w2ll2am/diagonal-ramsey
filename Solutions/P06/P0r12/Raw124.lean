import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp429_1_ok : RawF.check ctl A B pd i0 (raw (⟨429, by decide⟩ : Fin 1902)) rp429_1 = true := by decide +kernel

theorem rp429_2_ok : RawF.check ctl A B pd i0 (raw (⟨429, by decide⟩ : Fin 1902)) rp429_2 = true := by decide +kernel

theorem rp429_3_ok : RawF.check ctl A B pd i0 (raw (⟨429, by decide⟩ : Fin 1902)) rp429_3 = true := by decide +kernel

theorem raw429_h : ((raw (⟨429, by decide⟩ : Fin 1902)).ok (rawMin (⟨429, by decide⟩ : Fin 1902)) && chainF ((raw (⟨429, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp429.map (fun x => (x.lo, x.hi))) ((raw (⟨429, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp430_0_ok : RawF.check ctl A B pd i0 (raw (⟨430, by decide⟩ : Fin 1902)) rp430_0 = true := by decide +kernel

theorem rp430_1_ok : RawF.check ctl A B pd i0 (raw (⟨430, by decide⟩ : Fin 1902)) rp430_1 = true := by decide +kernel

theorem raw430_h : ((raw (⟨430, by decide⟩ : Fin 1902)).ok (rawMin (⟨430, by decide⟩ : Fin 1902)) && chainF ((raw (⟨430, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp430.map (fun x => (x.lo, x.hi))) ((raw (⟨430, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp431_0_ok : RawF.check ctl A B pd i0 (raw (⟨431, by decide⟩ : Fin 1902)) rp431_0 = true := by decide +kernel

theorem rp431_1_ok : RawF.check ctl A B pd i0 (raw (⟨431, by decide⟩ : Fin 1902)) rp431_1 = true := by decide +kernel

theorem raw431_h : ((raw (⟨431, by decide⟩ : Fin 1902)).ok (rawMin (⟨431, by decide⟩ : Fin 1902)) && chainF ((raw (⟨431, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp431.map (fun x => (x.lo, x.hi))) ((raw (⟨431, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp432_0_ok : RawF.check ctl A B pd i0 (raw (⟨432, by decide⟩ : Fin 1902)) rp432_0 = true := by decide +kernel

theorem raw432_h : ((raw (⟨432, by decide⟩ : Fin 1902)).ok (rawMin (⟨432, by decide⟩ : Fin 1902)) && chainF ((raw (⟨432, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp432.map (fun x => (x.lo, x.hi))) ((raw (⟨432, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp433_0_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_0 = true := by decide +kernel

theorem rp433_1_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_1 = true := by decide +kernel

theorem rp433_2_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_2 = true := by decide +kernel

theorem rp433_3_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_3 = true := by decide +kernel

theorem rp433_4_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_4 = true := by decide +kernel

theorem rp433_5_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_5 = true := by decide +kernel

theorem rp433_6_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_6 = true := by decide +kernel

theorem rp433_7_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_7 = true := by decide +kernel

theorem rp433_8_ok : RawF.check ctl A B pd i0 (raw (⟨433, by decide⟩ : Fin 1902)) rp433_8 = true := by decide +kernel

theorem raw433_h : ((raw (⟨433, by decide⟩ : Fin 1902)).ok (rawMin (⟨433, by decide⟩ : Fin 1902)) && chainF ((raw (⟨433, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp433.map (fun x => (x.lo, x.hi))) ((raw (⟨433, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp434_0_ok : RawF.check ctl A B pd i0 (raw (⟨434, by decide⟩ : Fin 1902)) rp434_0 = true := by decide +kernel

theorem raw434_h : ((raw (⟨434, by decide⟩ : Fin 1902)).ok (rawMin (⟨434, by decide⟩ : Fin 1902)) && chainF ((raw (⟨434, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp434.map (fun x => (x.lo, x.hi))) ((raw (⟨434, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp435_0_ok : RawF.check ctl A B pd i0 (raw (⟨435, by decide⟩ : Fin 1902)) rp435_0 = true := by decide +kernel

theorem raw435_h : ((raw (⟨435, by decide⟩ : Fin 1902)).ok (rawMin (⟨435, by decide⟩ : Fin 1902)) && chainF ((raw (⟨435, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp435.map (fun x => (x.lo, x.hi))) ((raw (⟨435, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp436_0_ok : RawF.check ctl A B pd i0 (raw (⟨436, by decide⟩ : Fin 1902)) rp436_0 = true := by decide +kernel

theorem rp436_1_ok : RawF.check ctl A B pd i0 (raw (⟨436, by decide⟩ : Fin 1902)) rp436_1 = true := by decide +kernel

theorem raw436_h : ((raw (⟨436, by decide⟩ : Fin 1902)).ok (rawMin (⟨436, by decide⟩ : Fin 1902)) && chainF ((raw (⟨436, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp436.map (fun x => (x.lo, x.hi))) ((raw (⟨436, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp437_0_ok : RawF.check ctl A B pd i0 (raw (⟨437, by decide⟩ : Fin 1902)) rp437_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
