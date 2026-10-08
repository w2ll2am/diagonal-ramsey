import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D80

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp809_2_ok : ClosedPF.check raw (closed (⟨809, by decide⟩ : Fin 1003)) qp809_2 = true := by decide +kernel

theorem qp809_3_ok : ClosedPF.check raw (closed (⟨809, by decide⟩ : Fin 1003)) qp809_3 = true := by decide +kernel

theorem qp809_4_ok : ClosedPF.check raw (closed (⟨809, by decide⟩ : Fin 1003)) qp809_4 = true := by decide +kernel

theorem cl809_h : ((closed (⟨809, by decide⟩ : Fin 1003)).ok (closedMin (⟨809, by decide⟩ : Fin 1003)) && chainF ((closed (⟨809, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp809.map (fun x => (x.lo, x.hi))) ((closed (⟨809, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp810_0_ok : ClosedPF.check raw (closed (⟨810, by decide⟩ : Fin 1003)) qp810_0 = true := by decide +kernel

theorem qp810_1_ok : ClosedPF.check raw (closed (⟨810, by decide⟩ : Fin 1003)) qp810_1 = true := by decide +kernel

theorem qp810_2_ok : ClosedPF.check raw (closed (⟨810, by decide⟩ : Fin 1003)) qp810_2 = true := by decide +kernel

theorem cl810_h : ((closed (⟨810, by decide⟩ : Fin 1003)).ok (closedMin (⟨810, by decide⟩ : Fin 1003)) && chainF ((closed (⟨810, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp810.map (fun x => (x.lo, x.hi))) ((closed (⟨810, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp811_0_ok : ClosedPF.check raw (closed (⟨811, by decide⟩ : Fin 1003)) qp811_0 = true := by decide +kernel

theorem cl811_h : ((closed (⟨811, by decide⟩ : Fin 1003)).ok (closedMin (⟨811, by decide⟩ : Fin 1003)) && chainF ((closed (⟨811, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp811.map (fun x => (x.lo, x.hi))) ((closed (⟨811, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp812_0_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_0 = true := by decide +kernel

theorem qp812_1_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_1 = true := by decide +kernel

theorem qp812_2_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_2 = true := by decide +kernel

theorem qp812_3_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_3 = true := by decide +kernel

theorem qp812_4_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_4 = true := by decide +kernel

theorem qp812_5_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_5 = true := by decide +kernel

theorem qp812_6_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_6 = true := by decide +kernel

theorem qp812_7_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_7 = true := by decide +kernel

theorem qp812_8_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_8 = true := by decide +kernel

theorem qp812_9_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_9 = true := by decide +kernel

theorem qp812_10_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_10 = true := by decide +kernel

theorem qp812_11_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_11 = true := by decide +kernel

theorem qp812_12_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_12 = true := by decide +kernel

theorem qp812_13_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_13 = true := by decide +kernel

theorem qp812_14_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_14 = true := by decide +kernel

theorem qp812_15_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_15 = true := by decide +kernel

theorem qp812_16_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_16 = true := by decide +kernel

theorem qp812_17_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_17 = true := by decide +kernel

theorem qp812_18_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_18 = true := by decide +kernel

theorem qp812_19_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_19 = true := by decide +kernel

theorem qp812_20_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_20 = true := by decide +kernel

theorem qp812_21_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_21 = true := by decide +kernel

theorem qp812_22_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_22 = true := by decide +kernel

theorem qp812_23_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_23 = true := by decide +kernel

theorem qp812_24_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_24 = true := by decide +kernel

theorem qp812_25_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_25 = true := by decide +kernel

theorem qp812_26_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_26 = true := by decide +kernel

theorem qp812_27_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_27 = true := by decide +kernel

theorem qp812_28_ok : ClosedPF.check raw (closed (⟨812, by decide⟩ : Fin 1003)) qp812_28 = true := by decide +kernel

theorem cl812_h : ((closed (⟨812, by decide⟩ : Fin 1003)).ok (closedMin (⟨812, by decide⟩ : Fin 1003)) && chainF ((closed (⟨812, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp812.map (fun x => (x.lo, x.hi))) ((closed (⟨812, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp813_0_ok : ClosedPF.check raw (closed (⟨813, by decide⟩ : Fin 1003)) qp813_0 = true := by decide +kernel

theorem qp813_1_ok : ClosedPF.check raw (closed (⟨813, by decide⟩ : Fin 1003)) qp813_1 = true := by decide +kernel

theorem qp813_2_ok : ClosedPF.check raw (closed (⟨813, by decide⟩ : Fin 1003)) qp813_2 = true := by decide +kernel

theorem qp813_3_ok : ClosedPF.check raw (closed (⟨813, by decide⟩ : Fin 1003)) qp813_3 = true := by decide +kernel

theorem cl813_h : ((closed (⟨813, by decide⟩ : Fin 1003)).ok (closedMin (⟨813, by decide⟩ : Fin 1003)) && chainF ((closed (⟨813, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp813.map (fun x => (x.lo, x.hi))) ((closed (⟨813, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp814_0_ok : ClosedPF.check raw (closed (⟨814, by decide⟩ : Fin 1003)) qp814_0 = true := by decide +kernel

theorem qp814_1_ok : ClosedPF.check raw (closed (⟨814, by decide⟩ : Fin 1003)) qp814_1 = true := by decide +kernel

theorem qp814_2_ok : ClosedPF.check raw (closed (⟨814, by decide⟩ : Fin 1003)) qp814_2 = true := by decide +kernel

theorem cl814_h : ((closed (⟨814, by decide⟩ : Fin 1003)).ok (closedMin (⟨814, by decide⟩ : Fin 1003)) && chainF ((closed (⟨814, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp814.map (fun x => (x.lo, x.hi))) ((closed (⟨814, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp815_0_ok : ClosedPF.check raw (closed (⟨815, by decide⟩ : Fin 1003)) qp815_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
