import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D80

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp682_2_ok : ClosedPF.check raw (closed (⟨682, by decide⟩ : Fin 1003)) qp682_2 = true := by decide +kernel

theorem qp682_3_ok : ClosedPF.check raw (closed (⟨682, by decide⟩ : Fin 1003)) qp682_3 = true := by decide +kernel

theorem qp682_4_ok : ClosedPF.check raw (closed (⟨682, by decide⟩ : Fin 1003)) qp682_4 = true := by decide +kernel

theorem qp682_5_ok : ClosedPF.check raw (closed (⟨682, by decide⟩ : Fin 1003)) qp682_5 = true := by decide +kernel

theorem cl682_h : ((closed (⟨682, by decide⟩ : Fin 1003)).ok (closedMin (⟨682, by decide⟩ : Fin 1003)) && chainF ((closed (⟨682, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp682.map (fun x => (x.lo, x.hi))) ((closed (⟨682, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp683_0_ok : ClosedPF.check raw (closed (⟨683, by decide⟩ : Fin 1003)) qp683_0 = true := by decide +kernel

theorem qp683_1_ok : ClosedPF.check raw (closed (⟨683, by decide⟩ : Fin 1003)) qp683_1 = true := by decide +kernel

theorem cl683_h : ((closed (⟨683, by decide⟩ : Fin 1003)).ok (closedMin (⟨683, by decide⟩ : Fin 1003)) && chainF ((closed (⟨683, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp683.map (fun x => (x.lo, x.hi))) ((closed (⟨683, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp684_0_ok : ClosedPF.check raw (closed (⟨684, by decide⟩ : Fin 1003)) qp684_0 = true := by decide +kernel

theorem qp684_1_ok : ClosedPF.check raw (closed (⟨684, by decide⟩ : Fin 1003)) qp684_1 = true := by decide +kernel

theorem qp684_2_ok : ClosedPF.check raw (closed (⟨684, by decide⟩ : Fin 1003)) qp684_2 = true := by decide +kernel

theorem qp684_3_ok : ClosedPF.check raw (closed (⟨684, by decide⟩ : Fin 1003)) qp684_3 = true := by decide +kernel

theorem qp684_4_ok : ClosedPF.check raw (closed (⟨684, by decide⟩ : Fin 1003)) qp684_4 = true := by decide +kernel

theorem qp684_5_ok : ClosedPF.check raw (closed (⟨684, by decide⟩ : Fin 1003)) qp684_5 = true := by decide +kernel

theorem cl684_h : ((closed (⟨684, by decide⟩ : Fin 1003)).ok (closedMin (⟨684, by decide⟩ : Fin 1003)) && chainF ((closed (⟨684, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp684.map (fun x => (x.lo, x.hi))) ((closed (⟨684, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp685_0_ok : ClosedPF.check raw (closed (⟨685, by decide⟩ : Fin 1003)) qp685_0 = true := by decide +kernel

theorem qp685_1_ok : ClosedPF.check raw (closed (⟨685, by decide⟩ : Fin 1003)) qp685_1 = true := by decide +kernel

theorem qp685_2_ok : ClosedPF.check raw (closed (⟨685, by decide⟩ : Fin 1003)) qp685_2 = true := by decide +kernel

theorem qp685_3_ok : ClosedPF.check raw (closed (⟨685, by decide⟩ : Fin 1003)) qp685_3 = true := by decide +kernel

theorem qp685_4_ok : ClosedPF.check raw (closed (⟨685, by decide⟩ : Fin 1003)) qp685_4 = true := by decide +kernel

theorem qp685_5_ok : ClosedPF.check raw (closed (⟨685, by decide⟩ : Fin 1003)) qp685_5 = true := by decide +kernel

theorem qp685_6_ok : ClosedPF.check raw (closed (⟨685, by decide⟩ : Fin 1003)) qp685_6 = true := by decide +kernel

theorem cl685_h : ((closed (⟨685, by decide⟩ : Fin 1003)).ok (closedMin (⟨685, by decide⟩ : Fin 1003)) && chainF ((closed (⟨685, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp685.map (fun x => (x.lo, x.hi))) ((closed (⟨685, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp686_0_ok : ClosedPF.check raw (closed (⟨686, by decide⟩ : Fin 1003)) qp686_0 = true := by decide +kernel

theorem qp686_1_ok : ClosedPF.check raw (closed (⟨686, by decide⟩ : Fin 1003)) qp686_1 = true := by decide +kernel

theorem qp686_2_ok : ClosedPF.check raw (closed (⟨686, by decide⟩ : Fin 1003)) qp686_2 = true := by decide +kernel

theorem qp686_3_ok : ClosedPF.check raw (closed (⟨686, by decide⟩ : Fin 1003)) qp686_3 = true := by decide +kernel

theorem qp686_4_ok : ClosedPF.check raw (closed (⟨686, by decide⟩ : Fin 1003)) qp686_4 = true := by decide +kernel

theorem qp686_5_ok : ClosedPF.check raw (closed (⟨686, by decide⟩ : Fin 1003)) qp686_5 = true := by decide +kernel

theorem cl686_h : ((closed (⟨686, by decide⟩ : Fin 1003)).ok (closedMin (⟨686, by decide⟩ : Fin 1003)) && chainF ((closed (⟨686, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp686.map (fun x => (x.lo, x.hi))) ((closed (⟨686, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp687_0_ok : ClosedPF.check raw (closed (⟨687, by decide⟩ : Fin 1003)) qp687_0 = true := by decide +kernel

theorem qp687_1_ok : ClosedPF.check raw (closed (⟨687, by decide⟩ : Fin 1003)) qp687_1 = true := by decide +kernel

theorem qp687_2_ok : ClosedPF.check raw (closed (⟨687, by decide⟩ : Fin 1003)) qp687_2 = true := by decide +kernel

theorem qp687_3_ok : ClosedPF.check raw (closed (⟨687, by decide⟩ : Fin 1003)) qp687_3 = true := by decide +kernel

theorem qp687_4_ok : ClosedPF.check raw (closed (⟨687, by decide⟩ : Fin 1003)) qp687_4 = true := by decide +kernel

theorem qp687_5_ok : ClosedPF.check raw (closed (⟨687, by decide⟩ : Fin 1003)) qp687_5 = true := by decide +kernel

theorem cl687_h : ((closed (⟨687, by decide⟩ : Fin 1003)).ok (closedMin (⟨687, by decide⟩ : Fin 1003)) && chainF ((closed (⟨687, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp687.map (fun x => (x.lo, x.hi))) ((closed (⟨687, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp688_0_ok : ClosedPF.check raw (closed (⟨688, by decide⟩ : Fin 1003)) qp688_0 = true := by decide +kernel

theorem qp688_1_ok : ClosedPF.check raw (closed (⟨688, by decide⟩ : Fin 1003)) qp688_1 = true := by decide +kernel

theorem qp688_2_ok : ClosedPF.check raw (closed (⟨688, by decide⟩ : Fin 1003)) qp688_2 = true := by decide +kernel

theorem qp688_3_ok : ClosedPF.check raw (closed (⟨688, by decide⟩ : Fin 1003)) qp688_3 = true := by decide +kernel

theorem cl688_h : ((closed (⟨688, by decide⟩ : Fin 1003)).ok (closedMin (⟨688, by decide⟩ : Fin 1003)) && chainF ((closed (⟨688, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp688.map (fun x => (x.lo, x.hi))) ((closed (⟨688, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp689_0_ok : ClosedPF.check raw (closed (⟨689, by decide⟩ : Fin 1003)) qp689_0 = true := by decide +kernel

theorem qp689_1_ok : ClosedPF.check raw (closed (⟨689, by decide⟩ : Fin 1003)) qp689_1 = true := by decide +kernel

theorem qp689_2_ok : ClosedPF.check raw (closed (⟨689, by decide⟩ : Fin 1003)) qp689_2 = true := by decide +kernel

theorem qp689_3_ok : ClosedPF.check raw (closed (⟨689, by decide⟩ : Fin 1003)) qp689_3 = true := by decide +kernel

theorem qp689_4_ok : ClosedPF.check raw (closed (⟨689, by decide⟩ : Fin 1003)) qp689_4 = true := by decide +kernel

theorem cl689_h : ((closed (⟨689, by decide⟩ : Fin 1003)).ok (closedMin (⟨689, by decide⟩ : Fin 1003)) && chainF ((closed (⟨689, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp689.map (fun x => (x.lo, x.hi))) ((closed (⟨689, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp690_0_ok : ClosedPF.check raw (closed (⟨690, by decide⟩ : Fin 1003)) qp690_0 = true := by decide +kernel

theorem qp690_1_ok : ClosedPF.check raw (closed (⟨690, by decide⟩ : Fin 1003)) qp690_1 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
