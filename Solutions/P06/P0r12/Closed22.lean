import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp92_14_ok : ClosedPF.check raw (closed (⟨92, by decide⟩ : Fin 1003)) qp92_14 = true := by decide +kernel

theorem qp92_15_ok : ClosedPF.check raw (closed (⟨92, by decide⟩ : Fin 1003)) qp92_15 = true := by decide +kernel

theorem qp92_16_ok : ClosedPF.check raw (closed (⟨92, by decide⟩ : Fin 1003)) qp92_16 = true := by decide +kernel

theorem cl92_h : ((closed (⟨92, by decide⟩ : Fin 1003)).ok (closedMin (⟨92, by decide⟩ : Fin 1003)) && chainF ((closed (⟨92, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp92.map (fun x => (x.lo, x.hi))) ((closed (⟨92, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp93_0_ok : ClosedPF.check raw (closed (⟨93, by decide⟩ : Fin 1003)) qp93_0 = true := by decide +kernel

theorem qp93_1_ok : ClosedPF.check raw (closed (⟨93, by decide⟩ : Fin 1003)) qp93_1 = true := by decide +kernel

theorem qp93_2_ok : ClosedPF.check raw (closed (⟨93, by decide⟩ : Fin 1003)) qp93_2 = true := by decide +kernel

theorem qp93_3_ok : ClosedPF.check raw (closed (⟨93, by decide⟩ : Fin 1003)) qp93_3 = true := by decide +kernel

theorem qp93_4_ok : ClosedPF.check raw (closed (⟨93, by decide⟩ : Fin 1003)) qp93_4 = true := by decide +kernel

theorem qp93_5_ok : ClosedPF.check raw (closed (⟨93, by decide⟩ : Fin 1003)) qp93_5 = true := by decide +kernel

theorem qp93_6_ok : ClosedPF.check raw (closed (⟨93, by decide⟩ : Fin 1003)) qp93_6 = true := by decide +kernel

theorem cl93_h : ((closed (⟨93, by decide⟩ : Fin 1003)).ok (closedMin (⟨93, by decide⟩ : Fin 1003)) && chainF ((closed (⟨93, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp93.map (fun x => (x.lo, x.hi))) ((closed (⟨93, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp94_0_ok : ClosedPF.check raw (closed (⟨94, by decide⟩ : Fin 1003)) qp94_0 = true := by decide +kernel

theorem qp94_1_ok : ClosedPF.check raw (closed (⟨94, by decide⟩ : Fin 1003)) qp94_1 = true := by decide +kernel

theorem cl94_h : ((closed (⟨94, by decide⟩ : Fin 1003)).ok (closedMin (⟨94, by decide⟩ : Fin 1003)) && chainF ((closed (⟨94, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp94.map (fun x => (x.lo, x.hi))) ((closed (⟨94, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp95_0_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_0 = true := by decide +kernel

theorem qp95_1_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_1 = true := by decide +kernel

theorem qp95_2_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_2 = true := by decide +kernel

theorem qp95_3_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_3 = true := by decide +kernel

theorem qp95_4_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_4 = true := by decide +kernel

theorem qp95_5_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_5 = true := by decide +kernel

theorem qp95_6_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_6 = true := by decide +kernel

theorem qp95_7_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_7 = true := by decide +kernel

theorem qp95_8_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_8 = true := by decide +kernel

theorem qp95_9_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_9 = true := by decide +kernel

theorem qp95_10_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_10 = true := by decide +kernel

theorem qp95_11_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_11 = true := by decide +kernel

theorem qp95_12_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_12 = true := by decide +kernel

theorem qp95_13_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_13 = true := by decide +kernel

theorem qp95_14_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_14 = true := by decide +kernel

theorem qp95_15_ok : ClosedPF.check raw (closed (⟨95, by decide⟩ : Fin 1003)) qp95_15 = true := by decide +kernel

theorem cl95_h : ((closed (⟨95, by decide⟩ : Fin 1003)).ok (closedMin (⟨95, by decide⟩ : Fin 1003)) && chainF ((closed (⟨95, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp95.map (fun x => (x.lo, x.hi))) ((closed (⟨95, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp96_0_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_0 = true := by decide +kernel

theorem qp96_1_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_1 = true := by decide +kernel

theorem qp96_2_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_2 = true := by decide +kernel

theorem qp96_3_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_3 = true := by decide +kernel

theorem qp96_4_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_4 = true := by decide +kernel

theorem qp96_5_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_5 = true := by decide +kernel

theorem qp96_6_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_6 = true := by decide +kernel

theorem qp96_7_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_7 = true := by decide +kernel

theorem qp96_8_ok : ClosedPF.check raw (closed (⟨96, by decide⟩ : Fin 1003)) qp96_8 = true := by decide +kernel

theorem cl96_h : ((closed (⟨96, by decide⟩ : Fin 1003)).ok (closedMin (⟨96, by decide⟩ : Fin 1003)) && chainF ((closed (⟨96, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp96.map (fun x => (x.lo, x.hi))) ((closed (⟨96, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp97_0_ok : ClosedPF.check raw (closed (⟨97, by decide⟩ : Fin 1003)) qp97_0 = true := by decide +kernel

theorem qp97_1_ok : ClosedPF.check raw (closed (⟨97, by decide⟩ : Fin 1003)) qp97_1 = true := by decide +kernel

theorem qp97_2_ok : ClosedPF.check raw (closed (⟨97, by decide⟩ : Fin 1003)) qp97_2 = true := by decide +kernel

theorem qp97_3_ok : ClosedPF.check raw (closed (⟨97, by decide⟩ : Fin 1003)) qp97_3 = true := by decide +kernel

theorem qp97_4_ok : ClosedPF.check raw (closed (⟨97, by decide⟩ : Fin 1003)) qp97_4 = true := by decide +kernel

theorem qp97_5_ok : ClosedPF.check raw (closed (⟨97, by decide⟩ : Fin 1003)) qp97_5 = true := by decide +kernel

theorem qp97_6_ok : ClosedPF.check raw (closed (⟨97, by decide⟩ : Fin 1003)) qp97_6 = true := by decide +kernel

theorem qp97_7_ok : ClosedPF.check raw (closed (⟨97, by decide⟩ : Fin 1003)) qp97_7 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
