import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D79

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp419_5_ok : ClosedPF.check raw (closed (⟨419, by decide⟩ : Fin 1003)) qp419_5 = true := by decide +kernel

theorem qp419_6_ok : ClosedPF.check raw (closed (⟨419, by decide⟩ : Fin 1003)) qp419_6 = true := by decide +kernel

theorem cl419_h : ((closed (⟨419, by decide⟩ : Fin 1003)).ok (closedMin (⟨419, by decide⟩ : Fin 1003)) && chainF ((closed (⟨419, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp419.map (fun x => (x.lo, x.hi))) ((closed (⟨419, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp420_0_ok : ClosedPF.check raw (closed (⟨420, by decide⟩ : Fin 1003)) qp420_0 = true := by decide +kernel

theorem cl420_h : ((closed (⟨420, by decide⟩ : Fin 1003)).ok (closedMin (⟨420, by decide⟩ : Fin 1003)) && chainF ((closed (⟨420, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp420.map (fun x => (x.lo, x.hi))) ((closed (⟨420, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp421_0_ok : ClosedPF.check raw (closed (⟨421, by decide⟩ : Fin 1003)) qp421_0 = true := by decide +kernel

theorem qp421_1_ok : ClosedPF.check raw (closed (⟨421, by decide⟩ : Fin 1003)) qp421_1 = true := by decide +kernel

theorem qp421_2_ok : ClosedPF.check raw (closed (⟨421, by decide⟩ : Fin 1003)) qp421_2 = true := by decide +kernel

theorem qp421_3_ok : ClosedPF.check raw (closed (⟨421, by decide⟩ : Fin 1003)) qp421_3 = true := by decide +kernel

theorem qp421_4_ok : ClosedPF.check raw (closed (⟨421, by decide⟩ : Fin 1003)) qp421_4 = true := by decide +kernel

theorem cl421_h : ((closed (⟨421, by decide⟩ : Fin 1003)).ok (closedMin (⟨421, by decide⟩ : Fin 1003)) && chainF ((closed (⟨421, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp421.map (fun x => (x.lo, x.hi))) ((closed (⟨421, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp422_0_ok : ClosedPF.check raw (closed (⟨422, by decide⟩ : Fin 1003)) qp422_0 = true := by decide +kernel

theorem qp422_1_ok : ClosedPF.check raw (closed (⟨422, by decide⟩ : Fin 1003)) qp422_1 = true := by decide +kernel

theorem qp422_2_ok : ClosedPF.check raw (closed (⟨422, by decide⟩ : Fin 1003)) qp422_2 = true := by decide +kernel

theorem cl422_h : ((closed (⟨422, by decide⟩ : Fin 1003)).ok (closedMin (⟨422, by decide⟩ : Fin 1003)) && chainF ((closed (⟨422, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp422.map (fun x => (x.lo, x.hi))) ((closed (⟨422, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp423_0_ok : ClosedPF.check raw (closed (⟨423, by decide⟩ : Fin 1003)) qp423_0 = true := by decide +kernel

theorem qp423_1_ok : ClosedPF.check raw (closed (⟨423, by decide⟩ : Fin 1003)) qp423_1 = true := by decide +kernel

theorem qp423_2_ok : ClosedPF.check raw (closed (⟨423, by decide⟩ : Fin 1003)) qp423_2 = true := by decide +kernel

theorem qp423_3_ok : ClosedPF.check raw (closed (⟨423, by decide⟩ : Fin 1003)) qp423_3 = true := by decide +kernel

theorem qp423_4_ok : ClosedPF.check raw (closed (⟨423, by decide⟩ : Fin 1003)) qp423_4 = true := by decide +kernel

theorem qp423_5_ok : ClosedPF.check raw (closed (⟨423, by decide⟩ : Fin 1003)) qp423_5 = true := by decide +kernel

theorem cl423_h : ((closed (⟨423, by decide⟩ : Fin 1003)).ok (closedMin (⟨423, by decide⟩ : Fin 1003)) && chainF ((closed (⟨423, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp423.map (fun x => (x.lo, x.hi))) ((closed (⟨423, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp424_0_ok : ClosedPF.check raw (closed (⟨424, by decide⟩ : Fin 1003)) qp424_0 = true := by decide +kernel

theorem cl424_h : ((closed (⟨424, by decide⟩ : Fin 1003)).ok (closedMin (⟨424, by decide⟩ : Fin 1003)) && chainF ((closed (⟨424, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp424.map (fun x => (x.lo, x.hi))) ((closed (⟨424, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp425_0_ok : ClosedPF.check raw (closed (⟨425, by decide⟩ : Fin 1003)) qp425_0 = true := by decide +kernel

theorem cl425_h : ((closed (⟨425, by decide⟩ : Fin 1003)).ok (closedMin (⟨425, by decide⟩ : Fin 1003)) && chainF ((closed (⟨425, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp425.map (fun x => (x.lo, x.hi))) ((closed (⟨425, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp426_0_ok : ClosedPF.check raw (closed (⟨426, by decide⟩ : Fin 1003)) qp426_0 = true := by decide +kernel

theorem qp426_1_ok : ClosedPF.check raw (closed (⟨426, by decide⟩ : Fin 1003)) qp426_1 = true := by decide +kernel

theorem qp426_2_ok : ClosedPF.check raw (closed (⟨426, by decide⟩ : Fin 1003)) qp426_2 = true := by decide +kernel

theorem qp426_3_ok : ClosedPF.check raw (closed (⟨426, by decide⟩ : Fin 1003)) qp426_3 = true := by decide +kernel

theorem qp426_4_ok : ClosedPF.check raw (closed (⟨426, by decide⟩ : Fin 1003)) qp426_4 = true := by decide +kernel

theorem cl426_h : ((closed (⟨426, by decide⟩ : Fin 1003)).ok (closedMin (⟨426, by decide⟩ : Fin 1003)) && chainF ((closed (⟨426, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp426.map (fun x => (x.lo, x.hi))) ((closed (⟨426, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp427_0_ok : ClosedPF.check raw (closed (⟨427, by decide⟩ : Fin 1003)) qp427_0 = true := by decide +kernel

theorem cl427_h : ((closed (⟨427, by decide⟩ : Fin 1003)).ok (closedMin (⟨427, by decide⟩ : Fin 1003)) && chainF ((closed (⟨427, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp427.map (fun x => (x.lo, x.hi))) ((closed (⟨427, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp428_0_ok : ClosedPF.check raw (closed (⟨428, by decide⟩ : Fin 1003)) qp428_0 = true := by decide +kernel

theorem qp428_1_ok : ClosedPF.check raw (closed (⟨428, by decide⟩ : Fin 1003)) qp428_1 = true := by decide +kernel

theorem qp428_2_ok : ClosedPF.check raw (closed (⟨428, by decide⟩ : Fin 1003)) qp428_2 = true := by decide +kernel

theorem cl428_h : ((closed (⟨428, by decide⟩ : Fin 1003)).ok (closedMin (⟨428, by decide⟩ : Fin 1003)) && chainF ((closed (⟨428, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp428.map (fun x => (x.lo, x.hi))) ((closed (⟨428, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp429_0_ok : ClosedPF.check raw (closed (⟨429, by decide⟩ : Fin 1003)) qp429_0 = true := by decide +kernel

theorem cl429_h : ((closed (⟨429, by decide⟩ : Fin 1003)).ok (closedMin (⟨429, by decide⟩ : Fin 1003)) && chainF ((closed (⟨429, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp429.map (fun x => (x.lo, x.hi))) ((closed (⟨429, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp430_0_ok : ClosedPF.check raw (closed (⟨430, by decide⟩ : Fin 1003)) qp430_0 = true := by decide +kernel

theorem qp430_1_ok : ClosedPF.check raw (closed (⟨430, by decide⟩ : Fin 1003)) qp430_1 = true := by decide +kernel

theorem qp430_2_ok : ClosedPF.check raw (closed (⟨430, by decide⟩ : Fin 1003)) qp430_2 = true := by decide +kernel

theorem cl430_h : ((closed (⟨430, by decide⟩ : Fin 1003)).ok (closedMin (⟨430, by decide⟩ : Fin 1003)) && chainF ((closed (⟨430, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp430.map (fun x => (x.lo, x.hi))) ((closed (⟨430, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp431_0_ok : ClosedPF.check raw (closed (⟨431, by decide⟩ : Fin 1003)) qp431_0 = true := by decide +kernel

theorem cl431_h : ((closed (⟨431, by decide⟩ : Fin 1003)).ok (closedMin (⟨431, by decide⟩ : Fin 1003)) && chainF ((closed (⟨431, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp431.map (fun x => (x.lo, x.hi))) ((closed (⟨431, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp432_0_ok : ClosedPF.check raw (closed (⟨432, by decide⟩ : Fin 1003)) qp432_0 = true := by decide +kernel

theorem cl432_h : ((closed (⟨432, by decide⟩ : Fin 1003)).ok (closedMin (⟨432, by decide⟩ : Fin 1003)) && chainF ((closed (⟨432, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp432.map (fun x => (x.lo, x.hi))) ((closed (⟨432, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp433_0_ok : ClosedPF.check raw (closed (⟨433, by decide⟩ : Fin 1003)) qp433_0 = true := by decide +kernel

theorem qp433_1_ok : ClosedPF.check raw (closed (⟨433, by decide⟩ : Fin 1003)) qp433_1 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
