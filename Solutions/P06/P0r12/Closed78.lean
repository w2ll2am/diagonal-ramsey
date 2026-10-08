import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D79

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp411_8_ok : ClosedPF.check raw (closed (⟨411, by decide⟩ : Fin 1003)) qp411_8 = true := by decide +kernel

theorem qp411_9_ok : ClosedPF.check raw (closed (⟨411, by decide⟩ : Fin 1003)) qp411_9 = true := by decide +kernel

theorem cl411_h : ((closed (⟨411, by decide⟩ : Fin 1003)).ok (closedMin (⟨411, by decide⟩ : Fin 1003)) && chainF ((closed (⟨411, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp411.map (fun x => (x.lo, x.hi))) ((closed (⟨411, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp412_0_ok : ClosedPF.check raw (closed (⟨412, by decide⟩ : Fin 1003)) qp412_0 = true := by decide +kernel

theorem qp412_1_ok : ClosedPF.check raw (closed (⟨412, by decide⟩ : Fin 1003)) qp412_1 = true := by decide +kernel

theorem cl412_h : ((closed (⟨412, by decide⟩ : Fin 1003)).ok (closedMin (⟨412, by decide⟩ : Fin 1003)) && chainF ((closed (⟨412, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp412.map (fun x => (x.lo, x.hi))) ((closed (⟨412, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp413_0_ok : ClosedPF.check raw (closed (⟨413, by decide⟩ : Fin 1003)) qp413_0 = true := by decide +kernel

theorem qp413_1_ok : ClosedPF.check raw (closed (⟨413, by decide⟩ : Fin 1003)) qp413_1 = true := by decide +kernel

theorem qp413_2_ok : ClosedPF.check raw (closed (⟨413, by decide⟩ : Fin 1003)) qp413_2 = true := by decide +kernel

theorem qp413_3_ok : ClosedPF.check raw (closed (⟨413, by decide⟩ : Fin 1003)) qp413_3 = true := by decide +kernel

theorem qp413_4_ok : ClosedPF.check raw (closed (⟨413, by decide⟩ : Fin 1003)) qp413_4 = true := by decide +kernel

theorem qp413_5_ok : ClosedPF.check raw (closed (⟨413, by decide⟩ : Fin 1003)) qp413_5 = true := by decide +kernel

theorem cl413_h : ((closed (⟨413, by decide⟩ : Fin 1003)).ok (closedMin (⟨413, by decide⟩ : Fin 1003)) && chainF ((closed (⟨413, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp413.map (fun x => (x.lo, x.hi))) ((closed (⟨413, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp414_0_ok : ClosedPF.check raw (closed (⟨414, by decide⟩ : Fin 1003)) qp414_0 = true := by decide +kernel

theorem cl414_h : ((closed (⟨414, by decide⟩ : Fin 1003)).ok (closedMin (⟨414, by decide⟩ : Fin 1003)) && chainF ((closed (⟨414, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp414.map (fun x => (x.lo, x.hi))) ((closed (⟨414, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp415_0_ok : ClosedPF.check raw (closed (⟨415, by decide⟩ : Fin 1003)) qp415_0 = true := by decide +kernel

theorem qp415_1_ok : ClosedPF.check raw (closed (⟨415, by decide⟩ : Fin 1003)) qp415_1 = true := by decide +kernel

theorem qp415_2_ok : ClosedPF.check raw (closed (⟨415, by decide⟩ : Fin 1003)) qp415_2 = true := by decide +kernel

theorem qp415_3_ok : ClosedPF.check raw (closed (⟨415, by decide⟩ : Fin 1003)) qp415_3 = true := by decide +kernel

theorem qp415_4_ok : ClosedPF.check raw (closed (⟨415, by decide⟩ : Fin 1003)) qp415_4 = true := by decide +kernel

theorem qp415_5_ok : ClosedPF.check raw (closed (⟨415, by decide⟩ : Fin 1003)) qp415_5 = true := by decide +kernel

theorem qp415_6_ok : ClosedPF.check raw (closed (⟨415, by decide⟩ : Fin 1003)) qp415_6 = true := by decide +kernel

theorem qp415_7_ok : ClosedPF.check raw (closed (⟨415, by decide⟩ : Fin 1003)) qp415_7 = true := by decide +kernel

theorem cl415_h : ((closed (⟨415, by decide⟩ : Fin 1003)).ok (closedMin (⟨415, by decide⟩ : Fin 1003)) && chainF ((closed (⟨415, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp415.map (fun x => (x.lo, x.hi))) ((closed (⟨415, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp416_0_ok : ClosedPF.check raw (closed (⟨416, by decide⟩ : Fin 1003)) qp416_0 = true := by decide +kernel

theorem qp416_1_ok : ClosedPF.check raw (closed (⟨416, by decide⟩ : Fin 1003)) qp416_1 = true := by decide +kernel

theorem cl416_h : ((closed (⟨416, by decide⟩ : Fin 1003)).ok (closedMin (⟨416, by decide⟩ : Fin 1003)) && chainF ((closed (⟨416, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp416.map (fun x => (x.lo, x.hi))) ((closed (⟨416, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp417_0_ok : ClosedPF.check raw (closed (⟨417, by decide⟩ : Fin 1003)) qp417_0 = true := by decide +kernel

theorem qp417_1_ok : ClosedPF.check raw (closed (⟨417, by decide⟩ : Fin 1003)) qp417_1 = true := by decide +kernel

theorem qp417_2_ok : ClosedPF.check raw (closed (⟨417, by decide⟩ : Fin 1003)) qp417_2 = true := by decide +kernel

theorem qp417_3_ok : ClosedPF.check raw (closed (⟨417, by decide⟩ : Fin 1003)) qp417_3 = true := by decide +kernel

theorem qp417_4_ok : ClosedPF.check raw (closed (⟨417, by decide⟩ : Fin 1003)) qp417_4 = true := by decide +kernel

theorem qp417_5_ok : ClosedPF.check raw (closed (⟨417, by decide⟩ : Fin 1003)) qp417_5 = true := by decide +kernel

theorem qp417_6_ok : ClosedPF.check raw (closed (⟨417, by decide⟩ : Fin 1003)) qp417_6 = true := by decide +kernel

theorem qp417_7_ok : ClosedPF.check raw (closed (⟨417, by decide⟩ : Fin 1003)) qp417_7 = true := by decide +kernel

theorem cl417_h : ((closed (⟨417, by decide⟩ : Fin 1003)).ok (closedMin (⟨417, by decide⟩ : Fin 1003)) && chainF ((closed (⟨417, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp417.map (fun x => (x.lo, x.hi))) ((closed (⟨417, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp418_0_ok : ClosedPF.check raw (closed (⟨418, by decide⟩ : Fin 1003)) qp418_0 = true := by decide +kernel

theorem qp418_1_ok : ClosedPF.check raw (closed (⟨418, by decide⟩ : Fin 1003)) qp418_1 = true := by decide +kernel

theorem qp418_2_ok : ClosedPF.check raw (closed (⟨418, by decide⟩ : Fin 1003)) qp418_2 = true := by decide +kernel

theorem qp418_3_ok : ClosedPF.check raw (closed (⟨418, by decide⟩ : Fin 1003)) qp418_3 = true := by decide +kernel

theorem qp418_4_ok : ClosedPF.check raw (closed (⟨418, by decide⟩ : Fin 1003)) qp418_4 = true := by decide +kernel

theorem qp418_5_ok : ClosedPF.check raw (closed (⟨418, by decide⟩ : Fin 1003)) qp418_5 = true := by decide +kernel

theorem qp418_6_ok : ClosedPF.check raw (closed (⟨418, by decide⟩ : Fin 1003)) qp418_6 = true := by decide +kernel

theorem qp418_7_ok : ClosedPF.check raw (closed (⟨418, by decide⟩ : Fin 1003)) qp418_7 = true := by decide +kernel

theorem cl418_h : ((closed (⟨418, by decide⟩ : Fin 1003)).ok (closedMin (⟨418, by decide⟩ : Fin 1003)) && chainF ((closed (⟨418, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp418.map (fun x => (x.lo, x.hi))) ((closed (⟨418, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp419_0_ok : ClosedPF.check raw (closed (⟨419, by decide⟩ : Fin 1003)) qp419_0 = true := by decide +kernel

theorem qp419_1_ok : ClosedPF.check raw (closed (⟨419, by decide⟩ : Fin 1003)) qp419_1 = true := by decide +kernel

theorem qp419_2_ok : ClosedPF.check raw (closed (⟨419, by decide⟩ : Fin 1003)) qp419_2 = true := by decide +kernel

theorem qp419_3_ok : ClosedPF.check raw (closed (⟨419, by decide⟩ : Fin 1003)) qp419_3 = true := by decide +kernel

theorem qp419_4_ok : ClosedPF.check raw (closed (⟨419, by decide⟩ : Fin 1003)) qp419_4 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
