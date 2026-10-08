import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp198_4_ok : ClosedPF.check raw (closed (⟨198, by decide⟩ : Fin 1003)) qp198_4 = true := by decide +kernel

theorem qp198_5_ok : ClosedPF.check raw (closed (⟨198, by decide⟩ : Fin 1003)) qp198_5 = true := by decide +kernel

theorem cl198_h : ((closed (⟨198, by decide⟩ : Fin 1003)).ok (closedMin (⟨198, by decide⟩ : Fin 1003)) && chainF ((closed (⟨198, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp198.map (fun x => (x.lo, x.hi))) ((closed (⟨198, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp199_0_ok : ClosedPF.check raw (closed (⟨199, by decide⟩ : Fin 1003)) qp199_0 = true := by decide +kernel

theorem qp199_1_ok : ClosedPF.check raw (closed (⟨199, by decide⟩ : Fin 1003)) qp199_1 = true := by decide +kernel

theorem qp199_2_ok : ClosedPF.check raw (closed (⟨199, by decide⟩ : Fin 1003)) qp199_2 = true := by decide +kernel

theorem qp199_3_ok : ClosedPF.check raw (closed (⟨199, by decide⟩ : Fin 1003)) qp199_3 = true := by decide +kernel

theorem qp199_4_ok : ClosedPF.check raw (closed (⟨199, by decide⟩ : Fin 1003)) qp199_4 = true := by decide +kernel

theorem cl199_h : ((closed (⟨199, by decide⟩ : Fin 1003)).ok (closedMin (⟨199, by decide⟩ : Fin 1003)) && chainF ((closed (⟨199, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp199.map (fun x => (x.lo, x.hi))) ((closed (⟨199, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp200_0_ok : ClosedPF.check raw (closed (⟨200, by decide⟩ : Fin 1003)) qp200_0 = true := by decide +kernel

theorem cl200_h : ((closed (⟨200, by decide⟩ : Fin 1003)).ok (closedMin (⟨200, by decide⟩ : Fin 1003)) && chainF ((closed (⟨200, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp200.map (fun x => (x.lo, x.hi))) ((closed (⟨200, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp201_0_ok : ClosedPF.check raw (closed (⟨201, by decide⟩ : Fin 1003)) qp201_0 = true := by decide +kernel

theorem cl201_h : ((closed (⟨201, by decide⟩ : Fin 1003)).ok (closedMin (⟨201, by decide⟩ : Fin 1003)) && chainF ((closed (⟨201, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp201.map (fun x => (x.lo, x.hi))) ((closed (⟨201, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp202_0_ok : ClosedPF.check raw (closed (⟨202, by decide⟩ : Fin 1003)) qp202_0 = true := by decide +kernel

theorem qp202_1_ok : ClosedPF.check raw (closed (⟨202, by decide⟩ : Fin 1003)) qp202_1 = true := by decide +kernel

theorem qp202_2_ok : ClosedPF.check raw (closed (⟨202, by decide⟩ : Fin 1003)) qp202_2 = true := by decide +kernel

theorem qp202_3_ok : ClosedPF.check raw (closed (⟨202, by decide⟩ : Fin 1003)) qp202_3 = true := by decide +kernel

theorem qp202_4_ok : ClosedPF.check raw (closed (⟨202, by decide⟩ : Fin 1003)) qp202_4 = true := by decide +kernel

theorem qp202_5_ok : ClosedPF.check raw (closed (⟨202, by decide⟩ : Fin 1003)) qp202_5 = true := by decide +kernel

theorem cl202_h : ((closed (⟨202, by decide⟩ : Fin 1003)).ok (closedMin (⟨202, by decide⟩ : Fin 1003)) && chainF ((closed (⟨202, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp202.map (fun x => (x.lo, x.hi))) ((closed (⟨202, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp203_0_ok : ClosedPF.check raw (closed (⟨203, by decide⟩ : Fin 1003)) qp203_0 = true := by decide +kernel

theorem qp203_1_ok : ClosedPF.check raw (closed (⟨203, by decide⟩ : Fin 1003)) qp203_1 = true := by decide +kernel

theorem qp203_2_ok : ClosedPF.check raw (closed (⟨203, by decide⟩ : Fin 1003)) qp203_2 = true := by decide +kernel

theorem cl203_h : ((closed (⟨203, by decide⟩ : Fin 1003)).ok (closedMin (⟨203, by decide⟩ : Fin 1003)) && chainF ((closed (⟨203, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp203.map (fun x => (x.lo, x.hi))) ((closed (⟨203, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp204_0_ok : ClosedPF.check raw (closed (⟨204, by decide⟩ : Fin 1003)) qp204_0 = true := by decide +kernel

theorem qp204_1_ok : ClosedPF.check raw (closed (⟨204, by decide⟩ : Fin 1003)) qp204_1 = true := by decide +kernel

theorem qp204_2_ok : ClosedPF.check raw (closed (⟨204, by decide⟩ : Fin 1003)) qp204_2 = true := by decide +kernel

theorem qp204_3_ok : ClosedPF.check raw (closed (⟨204, by decide⟩ : Fin 1003)) qp204_3 = true := by decide +kernel

theorem cl204_h : ((closed (⟨204, by decide⟩ : Fin 1003)).ok (closedMin (⟨204, by decide⟩ : Fin 1003)) && chainF ((closed (⟨204, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp204.map (fun x => (x.lo, x.hi))) ((closed (⟨204, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp205_0_ok : ClosedPF.check raw (closed (⟨205, by decide⟩ : Fin 1003)) qp205_0 = true := by decide +kernel

theorem cl205_h : ((closed (⟨205, by decide⟩ : Fin 1003)).ok (closedMin (⟨205, by decide⟩ : Fin 1003)) && chainF ((closed (⟨205, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp205.map (fun x => (x.lo, x.hi))) ((closed (⟨205, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp206_0_ok : ClosedPF.check raw (closed (⟨206, by decide⟩ : Fin 1003)) qp206_0 = true := by decide +kernel

theorem qp206_1_ok : ClosedPF.check raw (closed (⟨206, by decide⟩ : Fin 1003)) qp206_1 = true := by decide +kernel

theorem qp206_2_ok : ClosedPF.check raw (closed (⟨206, by decide⟩ : Fin 1003)) qp206_2 = true := by decide +kernel

theorem qp206_3_ok : ClosedPF.check raw (closed (⟨206, by decide⟩ : Fin 1003)) qp206_3 = true := by decide +kernel

theorem qp206_4_ok : ClosedPF.check raw (closed (⟨206, by decide⟩ : Fin 1003)) qp206_4 = true := by decide +kernel

theorem qp206_5_ok : ClosedPF.check raw (closed (⟨206, by decide⟩ : Fin 1003)) qp206_5 = true := by decide +kernel

theorem cl206_h : ((closed (⟨206, by decide⟩ : Fin 1003)).ok (closedMin (⟨206, by decide⟩ : Fin 1003)) && chainF ((closed (⟨206, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp206.map (fun x => (x.lo, x.hi))) ((closed (⟨206, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp207_0_ok : ClosedPF.check raw (closed (⟨207, by decide⟩ : Fin 1003)) qp207_0 = true := by decide +kernel

theorem cl207_h : ((closed (⟨207, by decide⟩ : Fin 1003)).ok (closedMin (⟨207, by decide⟩ : Fin 1003)) && chainF ((closed (⟨207, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp207.map (fun x => (x.lo, x.hi))) ((closed (⟨207, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp208_0_ok : ClosedPF.check raw (closed (⟨208, by decide⟩ : Fin 1003)) qp208_0 = true := by decide +kernel

theorem cl208_h : ((closed (⟨208, by decide⟩ : Fin 1003)).ok (closedMin (⟨208, by decide⟩ : Fin 1003)) && chainF ((closed (⟨208, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp208.map (fun x => (x.lo, x.hi))) ((closed (⟨208, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp209_0_ok : ClosedPF.check raw (closed (⟨209, by decide⟩ : Fin 1003)) qp209_0 = true := by decide +kernel

theorem qp209_1_ok : ClosedPF.check raw (closed (⟨209, by decide⟩ : Fin 1003)) qp209_1 = true := by decide +kernel

theorem qp209_2_ok : ClosedPF.check raw (closed (⟨209, by decide⟩ : Fin 1003)) qp209_2 = true := by decide +kernel

theorem qp209_3_ok : ClosedPF.check raw (closed (⟨209, by decide⟩ : Fin 1003)) qp209_3 = true := by decide +kernel

theorem qp209_4_ok : ClosedPF.check raw (closed (⟨209, by decide⟩ : Fin 1003)) qp209_4 = true := by decide +kernel

theorem qp209_5_ok : ClosedPF.check raw (closed (⟨209, by decide⟩ : Fin 1003)) qp209_5 = true := by decide +kernel

theorem qp209_6_ok : ClosedPF.check raw (closed (⟨209, by decide⟩ : Fin 1003)) qp209_6 = true := by decide +kernel

theorem qp209_7_ok : ClosedPF.check raw (closed (⟨209, by decide⟩ : Fin 1003)) qp209_7 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
