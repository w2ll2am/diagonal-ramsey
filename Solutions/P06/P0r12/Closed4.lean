import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp37_1_ok : ClosedPF.check raw (closed (⟨37, by decide⟩ : Fin 1003)) qp37_1 = true := by decide +kernel

theorem cl37_h : ((closed (⟨37, by decide⟩ : Fin 1003)).ok (closedMin (⟨37, by decide⟩ : Fin 1003)) && chainF ((closed (⟨37, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp37.map (fun x => (x.lo, x.hi))) ((closed (⟨37, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp38_0_ok : ClosedPF.check raw (closed (⟨38, by decide⟩ : Fin 1003)) qp38_0 = true := by decide +kernel

theorem qp38_1_ok : ClosedPF.check raw (closed (⟨38, by decide⟩ : Fin 1003)) qp38_1 = true := by decide +kernel

theorem qp38_2_ok : ClosedPF.check raw (closed (⟨38, by decide⟩ : Fin 1003)) qp38_2 = true := by decide +kernel

theorem qp38_3_ok : ClosedPF.check raw (closed (⟨38, by decide⟩ : Fin 1003)) qp38_3 = true := by decide +kernel

theorem qp38_4_ok : ClosedPF.check raw (closed (⟨38, by decide⟩ : Fin 1003)) qp38_4 = true := by decide +kernel

theorem qp38_5_ok : ClosedPF.check raw (closed (⟨38, by decide⟩ : Fin 1003)) qp38_5 = true := by decide +kernel

theorem qp38_6_ok : ClosedPF.check raw (closed (⟨38, by decide⟩ : Fin 1003)) qp38_6 = true := by decide +kernel

theorem qp38_7_ok : ClosedPF.check raw (closed (⟨38, by decide⟩ : Fin 1003)) qp38_7 = true := by decide +kernel

theorem cl38_h : ((closed (⟨38, by decide⟩ : Fin 1003)).ok (closedMin (⟨38, by decide⟩ : Fin 1003)) && chainF ((closed (⟨38, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp38.map (fun x => (x.lo, x.hi))) ((closed (⟨38, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp39_0_ok : ClosedPF.check raw (closed (⟨39, by decide⟩ : Fin 1003)) qp39_0 = true := by decide +kernel

theorem cl39_h : ((closed (⟨39, by decide⟩ : Fin 1003)).ok (closedMin (⟨39, by decide⟩ : Fin 1003)) && chainF ((closed (⟨39, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp39.map (fun x => (x.lo, x.hi))) ((closed (⟨39, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp40_0_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_0 = true := by decide +kernel

theorem qp40_1_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_1 = true := by decide +kernel

theorem qp40_2_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_2 = true := by decide +kernel

theorem qp40_3_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_3 = true := by decide +kernel

theorem qp40_4_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_4 = true := by decide +kernel

theorem qp40_5_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_5 = true := by decide +kernel

theorem qp40_6_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_6 = true := by decide +kernel

theorem qp40_7_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_7 = true := by decide +kernel

theorem qp40_8_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_8 = true := by decide +kernel

theorem qp40_9_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_9 = true := by decide +kernel

theorem qp40_10_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_10 = true := by decide +kernel

theorem qp40_11_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_11 = true := by decide +kernel

theorem qp40_12_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_12 = true := by decide +kernel

theorem qp40_13_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_13 = true := by decide +kernel

theorem qp40_14_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_14 = true := by decide +kernel

theorem qp40_15_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_15 = true := by decide +kernel

theorem qp40_16_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_16 = true := by decide +kernel

theorem qp40_17_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_17 = true := by decide +kernel

theorem qp40_18_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_18 = true := by decide +kernel

theorem qp40_19_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_19 = true := by decide +kernel

theorem qp40_20_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_20 = true := by decide +kernel

theorem qp40_21_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_21 = true := by decide +kernel

theorem qp40_22_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_22 = true := by decide +kernel

theorem qp40_23_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_23 = true := by decide +kernel

theorem qp40_24_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_24 = true := by decide +kernel

theorem qp40_25_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_25 = true := by decide +kernel

theorem qp40_26_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_26 = true := by decide +kernel

theorem qp40_27_ok : ClosedPF.check raw (closed (⟨40, by decide⟩ : Fin 1003)) qp40_27 = true := by decide +kernel

theorem cl40_h : ((closed (⟨40, by decide⟩ : Fin 1003)).ok (closedMin (⟨40, by decide⟩ : Fin 1003)) && chainF ((closed (⟨40, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp40.map (fun x => (x.lo, x.hi))) ((closed (⟨40, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp41_0_ok : ClosedPF.check raw (closed (⟨41, by decide⟩ : Fin 1003)) qp41_0 = true := by decide +kernel

theorem qp41_1_ok : ClosedPF.check raw (closed (⟨41, by decide⟩ : Fin 1003)) qp41_1 = true := by decide +kernel

theorem qp41_2_ok : ClosedPF.check raw (closed (⟨41, by decide⟩ : Fin 1003)) qp41_2 = true := by decide +kernel

theorem qp41_3_ok : ClosedPF.check raw (closed (⟨41, by decide⟩ : Fin 1003)) qp41_3 = true := by decide +kernel

theorem cl41_h : ((closed (⟨41, by decide⟩ : Fin 1003)).ok (closedMin (⟨41, by decide⟩ : Fin 1003)) && chainF ((closed (⟨41, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp41.map (fun x => (x.lo, x.hi))) ((closed (⟨41, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp42_0_ok : ClosedPF.check raw (closed (⟨42, by decide⟩ : Fin 1003)) qp42_0 = true := by decide +kernel

theorem cl42_h : ((closed (⟨42, by decide⟩ : Fin 1003)).ok (closedMin (⟨42, by decide⟩ : Fin 1003)) && chainF ((closed (⟨42, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp42.map (fun x => (x.lo, x.hi))) ((closed (⟨42, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp43_0_ok : ClosedPF.check raw (closed (⟨43, by decide⟩ : Fin 1003)) qp43_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
