import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp140_2_ok : ClosedPF.check raw (closed (⟨140, by decide⟩ : Fin 1003)) qp140_2 = true := by decide +kernel

theorem cl140_h : ((closed (⟨140, by decide⟩ : Fin 1003)).ok (closedMin (⟨140, by decide⟩ : Fin 1003)) && chainF ((closed (⟨140, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp140.map (fun x => (x.lo, x.hi))) ((closed (⟨140, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp141_0_ok : ClosedPF.check raw (closed (⟨141, by decide⟩ : Fin 1003)) qp141_0 = true := by decide +kernel

theorem qp141_1_ok : ClosedPF.check raw (closed (⟨141, by decide⟩ : Fin 1003)) qp141_1 = true := by decide +kernel

theorem cl141_h : ((closed (⟨141, by decide⟩ : Fin 1003)).ok (closedMin (⟨141, by decide⟩ : Fin 1003)) && chainF ((closed (⟨141, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp141.map (fun x => (x.lo, x.hi))) ((closed (⟨141, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp142_0_ok : ClosedPF.check raw (closed (⟨142, by decide⟩ : Fin 1003)) qp142_0 = true := by decide +kernel

theorem qp142_1_ok : ClosedPF.check raw (closed (⟨142, by decide⟩ : Fin 1003)) qp142_1 = true := by decide +kernel

theorem qp142_2_ok : ClosedPF.check raw (closed (⟨142, by decide⟩ : Fin 1003)) qp142_2 = true := by decide +kernel

theorem cl142_h : ((closed (⟨142, by decide⟩ : Fin 1003)).ok (closedMin (⟨142, by decide⟩ : Fin 1003)) && chainF ((closed (⟨142, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp142.map (fun x => (x.lo, x.hi))) ((closed (⟨142, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp143_0_ok : ClosedPF.check raw (closed (⟨143, by decide⟩ : Fin 1003)) qp143_0 = true := by decide +kernel

theorem qp143_1_ok : ClosedPF.check raw (closed (⟨143, by decide⟩ : Fin 1003)) qp143_1 = true := by decide +kernel

theorem qp143_2_ok : ClosedPF.check raw (closed (⟨143, by decide⟩ : Fin 1003)) qp143_2 = true := by decide +kernel

theorem qp143_3_ok : ClosedPF.check raw (closed (⟨143, by decide⟩ : Fin 1003)) qp143_3 = true := by decide +kernel

theorem qp143_4_ok : ClosedPF.check raw (closed (⟨143, by decide⟩ : Fin 1003)) qp143_4 = true := by decide +kernel

theorem cl143_h : ((closed (⟨143, by decide⟩ : Fin 1003)).ok (closedMin (⟨143, by decide⟩ : Fin 1003)) && chainF ((closed (⟨143, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp143.map (fun x => (x.lo, x.hi))) ((closed (⟨143, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp144_0_ok : ClosedPF.check raw (closed (⟨144, by decide⟩ : Fin 1003)) qp144_0 = true := by decide +kernel

theorem qp144_1_ok : ClosedPF.check raw (closed (⟨144, by decide⟩ : Fin 1003)) qp144_1 = true := by decide +kernel

theorem cl144_h : ((closed (⟨144, by decide⟩ : Fin 1003)).ok (closedMin (⟨144, by decide⟩ : Fin 1003)) && chainF ((closed (⟨144, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp144.map (fun x => (x.lo, x.hi))) ((closed (⟨144, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp145_0_ok : ClosedPF.check raw (closed (⟨145, by decide⟩ : Fin 1003)) qp145_0 = true := by decide +kernel

theorem qp145_1_ok : ClosedPF.check raw (closed (⟨145, by decide⟩ : Fin 1003)) qp145_1 = true := by decide +kernel

theorem qp145_2_ok : ClosedPF.check raw (closed (⟨145, by decide⟩ : Fin 1003)) qp145_2 = true := by decide +kernel

theorem cl145_h : ((closed (⟨145, by decide⟩ : Fin 1003)).ok (closedMin (⟨145, by decide⟩ : Fin 1003)) && chainF ((closed (⟨145, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp145.map (fun x => (x.lo, x.hi))) ((closed (⟨145, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp146_0_ok : ClosedPF.check raw (closed (⟨146, by decide⟩ : Fin 1003)) qp146_0 = true := by decide +kernel

theorem cl146_h : ((closed (⟨146, by decide⟩ : Fin 1003)).ok (closedMin (⟨146, by decide⟩ : Fin 1003)) && chainF ((closed (⟨146, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp146.map (fun x => (x.lo, x.hi))) ((closed (⟨146, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp147_0_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_0 = true := by decide +kernel

theorem qp147_1_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_1 = true := by decide +kernel

theorem qp147_2_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_2 = true := by decide +kernel

theorem qp147_3_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_3 = true := by decide +kernel

theorem qp147_4_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_4 = true := by decide +kernel

theorem qp147_5_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_5 = true := by decide +kernel

theorem qp147_6_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_6 = true := by decide +kernel

theorem qp147_7_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_7 = true := by decide +kernel

theorem qp147_8_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_8 = true := by decide +kernel

theorem qp147_9_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_9 = true := by decide +kernel

theorem qp147_10_ok : ClosedPF.check raw (closed (⟨147, by decide⟩ : Fin 1003)) qp147_10 = true := by decide +kernel

theorem cl147_h : ((closed (⟨147, by decide⟩ : Fin 1003)).ok (closedMin (⟨147, by decide⟩ : Fin 1003)) && chainF ((closed (⟨147, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp147.map (fun x => (x.lo, x.hi))) ((closed (⟨147, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp148_0_ok : ClosedPF.check raw (closed (⟨148, by decide⟩ : Fin 1003)) qp148_0 = true := by decide +kernel

theorem qp148_1_ok : ClosedPF.check raw (closed (⟨148, by decide⟩ : Fin 1003)) qp148_1 = true := by decide +kernel

theorem qp148_2_ok : ClosedPF.check raw (closed (⟨148, by decide⟩ : Fin 1003)) qp148_2 = true := by decide +kernel

theorem cl148_h : ((closed (⟨148, by decide⟩ : Fin 1003)).ok (closedMin (⟨148, by decide⟩ : Fin 1003)) && chainF ((closed (⟨148, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp148.map (fun x => (x.lo, x.hi))) ((closed (⟨148, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp149_0_ok : ClosedPF.check raw (closed (⟨149, by decide⟩ : Fin 1003)) qp149_0 = true := by decide +kernel

theorem qp149_1_ok : ClosedPF.check raw (closed (⟨149, by decide⟩ : Fin 1003)) qp149_1 = true := by decide +kernel

theorem qp149_2_ok : ClosedPF.check raw (closed (⟨149, by decide⟩ : Fin 1003)) qp149_2 = true := by decide +kernel

theorem qp149_3_ok : ClosedPF.check raw (closed (⟨149, by decide⟩ : Fin 1003)) qp149_3 = true := by decide +kernel

theorem qp149_4_ok : ClosedPF.check raw (closed (⟨149, by decide⟩ : Fin 1003)) qp149_4 = true := by decide +kernel

theorem qp149_5_ok : ClosedPF.check raw (closed (⟨149, by decide⟩ : Fin 1003)) qp149_5 = true := by decide +kernel

theorem qp149_6_ok : ClosedPF.check raw (closed (⟨149, by decide⟩ : Fin 1003)) qp149_6 = true := by decide +kernel

theorem cl149_h : ((closed (⟨149, by decide⟩ : Fin 1003)).ok (closedMin (⟨149, by decide⟩ : Fin 1003)) && chainF ((closed (⟨149, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp149.map (fun x => (x.lo, x.hi))) ((closed (⟨149, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp150_0_ok : ClosedPF.check raw (closed (⟨150, by decide⟩ : Fin 1003)) qp150_0 = true := by decide +kernel

theorem cl150_h : ((closed (⟨150, by decide⟩ : Fin 1003)).ok (closedMin (⟨150, by decide⟩ : Fin 1003)) && chainF ((closed (⟨150, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp150.map (fun x => (x.lo, x.hi))) ((closed (⟨150, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
