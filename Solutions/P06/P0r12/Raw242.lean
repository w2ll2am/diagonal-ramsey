import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D14
import Solutions.P06.P0r12.D15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp707_27_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_27 = true := by decide +kernel

theorem rp707_28_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_28 = true := by decide +kernel

theorem rp707_29_ok : RawF.check ctl A B pd i0 (raw (⟨707, by decide⟩ : Fin 1902)) rp707_29 = true := by decide +kernel

theorem raw707_h : ((raw (⟨707, by decide⟩ : Fin 1902)).ok (rawMin (⟨707, by decide⟩ : Fin 1902)) && chainF ((raw (⟨707, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp707.map (fun x => (x.lo, x.hi))) ((raw (⟨707, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp708_0_ok : RawF.check ctl A B pd i0 (raw (⟨708, by decide⟩ : Fin 1902)) rp708_0 = true := by decide +kernel

theorem raw708_h : ((raw (⟨708, by decide⟩ : Fin 1902)).ok (rawMin (⟨708, by decide⟩ : Fin 1902)) && chainF ((raw (⟨708, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp708.map (fun x => (x.lo, x.hi))) ((raw (⟨708, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp709_0_ok : RawF.check ctl A B pd i0 (raw (⟨709, by decide⟩ : Fin 1902)) rp709_0 = true := by decide +kernel

theorem rp709_1_ok : RawF.check ctl A B pd i0 (raw (⟨709, by decide⟩ : Fin 1902)) rp709_1 = true := by decide +kernel

theorem rp709_2_ok : RawF.check ctl A B pd i0 (raw (⟨709, by decide⟩ : Fin 1902)) rp709_2 = true := by decide +kernel

theorem raw709_h : ((raw (⟨709, by decide⟩ : Fin 1902)).ok (rawMin (⟨709, by decide⟩ : Fin 1902)) && chainF ((raw (⟨709, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp709.map (fun x => (x.lo, x.hi))) ((raw (⟨709, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp710_0_ok : RawF.check ctl A B pd i0 (raw (⟨710, by decide⟩ : Fin 1902)) rp710_0 = true := by decide +kernel

theorem raw710_h : ((raw (⟨710, by decide⟩ : Fin 1902)).ok (rawMin (⟨710, by decide⟩ : Fin 1902)) && chainF ((raw (⟨710, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp710.map (fun x => (x.lo, x.hi))) ((raw (⟨710, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp711_0_ok : RawF.check ctl A B pd i0 (raw (⟨711, by decide⟩ : Fin 1902)) rp711_0 = true := by decide +kernel

theorem raw711_h : ((raw (⟨711, by decide⟩ : Fin 1902)).ok (rawMin (⟨711, by decide⟩ : Fin 1902)) && chainF ((raw (⟨711, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp711.map (fun x => (x.lo, x.hi))) ((raw (⟨711, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp712_0_ok : RawF.check ctl A B pd i0 (raw (⟨712, by decide⟩ : Fin 1902)) rp712_0 = true := by decide +kernel

theorem rp712_1_ok : RawF.check ctl A B pd i0 (raw (⟨712, by decide⟩ : Fin 1902)) rp712_1 = true := by decide +kernel

theorem rp712_2_ok : RawF.check ctl A B pd i0 (raw (⟨712, by decide⟩ : Fin 1902)) rp712_2 = true := by decide +kernel

theorem rp712_3_ok : RawF.check ctl A B pd i0 (raw (⟨712, by decide⟩ : Fin 1902)) rp712_3 = true := by decide +kernel

theorem raw712_h : ((raw (⟨712, by decide⟩ : Fin 1902)).ok (rawMin (⟨712, by decide⟩ : Fin 1902)) && chainF ((raw (⟨712, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp712.map (fun x => (x.lo, x.hi))) ((raw (⟨712, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp713_0_ok : RawF.check ctl A B pd i0 (raw (⟨713, by decide⟩ : Fin 1902)) rp713_0 = true := by decide +kernel

theorem raw713_h : ((raw (⟨713, by decide⟩ : Fin 1902)).ok (rawMin (⟨713, by decide⟩ : Fin 1902)) && chainF ((raw (⟨713, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp713.map (fun x => (x.lo, x.hi))) ((raw (⟨713, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp714_0_ok : RawF.check ctl A B pd i0 (raw (⟨714, by decide⟩ : Fin 1902)) rp714_0 = true := by decide +kernel

theorem rp714_1_ok : RawF.check ctl A B pd i0 (raw (⟨714, by decide⟩ : Fin 1902)) rp714_1 = true := by decide +kernel

theorem rp714_2_ok : RawF.check ctl A B pd i0 (raw (⟨714, by decide⟩ : Fin 1902)) rp714_2 = true := by decide +kernel

theorem raw714_h : ((raw (⟨714, by decide⟩ : Fin 1902)).ok (rawMin (⟨714, by decide⟩ : Fin 1902)) && chainF ((raw (⟨714, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp714.map (fun x => (x.lo, x.hi))) ((raw (⟨714, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp715_0_ok : RawF.check ctl A B pd i0 (raw (⟨715, by decide⟩ : Fin 1902)) rp715_0 = true := by decide +kernel

theorem rp715_1_ok : RawF.check ctl A B pd i0 (raw (⟨715, by decide⟩ : Fin 1902)) rp715_1 = true := by decide +kernel

theorem rp715_2_ok : RawF.check ctl A B pd i0 (raw (⟨715, by decide⟩ : Fin 1902)) rp715_2 = true := by decide +kernel

theorem rp715_3_ok : RawF.check ctl A B pd i0 (raw (⟨715, by decide⟩ : Fin 1902)) rp715_3 = true := by decide +kernel

theorem rp715_4_ok : RawF.check ctl A B pd i0 (raw (⟨715, by decide⟩ : Fin 1902)) rp715_4 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
