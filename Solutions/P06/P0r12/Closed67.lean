import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D79

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp376_24_ok : ClosedPF.check raw (closed (⟨376, by decide⟩ : Fin 1003)) qp376_24 = true := by decide +kernel

theorem qp376_25_ok : ClosedPF.check raw (closed (⟨376, by decide⟩ : Fin 1003)) qp376_25 = true := by decide +kernel

theorem cl376_h : ((closed (⟨376, by decide⟩ : Fin 1003)).ok (closedMin (⟨376, by decide⟩ : Fin 1003)) && chainF ((closed (⟨376, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp376.map (fun x => (x.lo, x.hi))) ((closed (⟨376, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp377_0_ok : ClosedPF.check raw (closed (⟨377, by decide⟩ : Fin 1003)) qp377_0 = true := by decide +kernel

theorem qp377_1_ok : ClosedPF.check raw (closed (⟨377, by decide⟩ : Fin 1003)) qp377_1 = true := by decide +kernel

theorem cl377_h : ((closed (⟨377, by decide⟩ : Fin 1003)).ok (closedMin (⟨377, by decide⟩ : Fin 1003)) && chainF ((closed (⟨377, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp377.map (fun x => (x.lo, x.hi))) ((closed (⟨377, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp378_0_ok : ClosedPF.check raw (closed (⟨378, by decide⟩ : Fin 1003)) qp378_0 = true := by decide +kernel

theorem cl378_h : ((closed (⟨378, by decide⟩ : Fin 1003)).ok (closedMin (⟨378, by decide⟩ : Fin 1003)) && chainF ((closed (⟨378, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp378.map (fun x => (x.lo, x.hi))) ((closed (⟨378, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp379_0_ok : ClosedPF.check raw (closed (⟨379, by decide⟩ : Fin 1003)) qp379_0 = true := by decide +kernel

theorem qp379_1_ok : ClosedPF.check raw (closed (⟨379, by decide⟩ : Fin 1003)) qp379_1 = true := by decide +kernel

theorem cl379_h : ((closed (⟨379, by decide⟩ : Fin 1003)).ok (closedMin (⟨379, by decide⟩ : Fin 1003)) && chainF ((closed (⟨379, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp379.map (fun x => (x.lo, x.hi))) ((closed (⟨379, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp380_0_ok : ClosedPF.check raw (closed (⟨380, by decide⟩ : Fin 1003)) qp380_0 = true := by decide +kernel

theorem cl380_h : ((closed (⟨380, by decide⟩ : Fin 1003)).ok (closedMin (⟨380, by decide⟩ : Fin 1003)) && chainF ((closed (⟨380, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp380.map (fun x => (x.lo, x.hi))) ((closed (⟨380, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp381_0_ok : ClosedPF.check raw (closed (⟨381, by decide⟩ : Fin 1003)) qp381_0 = true := by decide +kernel

theorem cl381_h : ((closed (⟨381, by decide⟩ : Fin 1003)).ok (closedMin (⟨381, by decide⟩ : Fin 1003)) && chainF ((closed (⟨381, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp381.map (fun x => (x.lo, x.hi))) ((closed (⟨381, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp382_0_ok : ClosedPF.check raw (closed (⟨382, by decide⟩ : Fin 1003)) qp382_0 = true := by decide +kernel

theorem cl382_h : ((closed (⟨382, by decide⟩ : Fin 1003)).ok (closedMin (⟨382, by decide⟩ : Fin 1003)) && chainF ((closed (⟨382, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp382.map (fun x => (x.lo, x.hi))) ((closed (⟨382, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp383_0_ok : ClosedPF.check raw (closed (⟨383, by decide⟩ : Fin 1003)) qp383_0 = true := by decide +kernel

theorem qp383_1_ok : ClosedPF.check raw (closed (⟨383, by decide⟩ : Fin 1003)) qp383_1 = true := by decide +kernel

theorem qp383_2_ok : ClosedPF.check raw (closed (⟨383, by decide⟩ : Fin 1003)) qp383_2 = true := by decide +kernel

theorem qp383_3_ok : ClosedPF.check raw (closed (⟨383, by decide⟩ : Fin 1003)) qp383_3 = true := by decide +kernel

theorem qp383_4_ok : ClosedPF.check raw (closed (⟨383, by decide⟩ : Fin 1003)) qp383_4 = true := by decide +kernel

theorem qp383_5_ok : ClosedPF.check raw (closed (⟨383, by decide⟩ : Fin 1003)) qp383_5 = true := by decide +kernel

theorem qp383_6_ok : ClosedPF.check raw (closed (⟨383, by decide⟩ : Fin 1003)) qp383_6 = true := by decide +kernel

theorem cl383_h : ((closed (⟨383, by decide⟩ : Fin 1003)).ok (closedMin (⟨383, by decide⟩ : Fin 1003)) && chainF ((closed (⟨383, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp383.map (fun x => (x.lo, x.hi))) ((closed (⟨383, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp384_0_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_0 = true := by decide +kernel

theorem qp384_1_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_1 = true := by decide +kernel

theorem qp384_2_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_2 = true := by decide +kernel

theorem qp384_3_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_3 = true := by decide +kernel

theorem qp384_4_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_4 = true := by decide +kernel

theorem qp384_5_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_5 = true := by decide +kernel

theorem qp384_6_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_6 = true := by decide +kernel

theorem qp384_7_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_7 = true := by decide +kernel

theorem qp384_8_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_8 = true := by decide +kernel

theorem qp384_9_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_9 = true := by decide +kernel

theorem qp384_10_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_10 = true := by decide +kernel

theorem qp384_11_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_11 = true := by decide +kernel

theorem qp384_12_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_12 = true := by decide +kernel

theorem qp384_13_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_13 = true := by decide +kernel

theorem qp384_14_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_14 = true := by decide +kernel

theorem qp384_15_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_15 = true := by decide +kernel

theorem qp384_16_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_16 = true := by decide +kernel

theorem qp384_17_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_17 = true := by decide +kernel

theorem qp384_18_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_18 = true := by decide +kernel

theorem qp384_19_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_19 = true := by decide +kernel

theorem qp384_20_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_20 = true := by decide +kernel

theorem qp384_21_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_21 = true := by decide +kernel

theorem qp384_22_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_22 = true := by decide +kernel

theorem qp384_23_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_23 = true := by decide +kernel

theorem qp384_24_ok : ClosedPF.check raw (closed (⟨384, by decide⟩ : Fin 1003)) qp384_24 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
