import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D79

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp603_4_ok : ClosedPF.check raw (closed (⟨603, by decide⟩ : Fin 1003)) qp603_4 = true := by decide +kernel

theorem qp603_5_ok : ClosedPF.check raw (closed (⟨603, by decide⟩ : Fin 1003)) qp603_5 = true := by decide +kernel

theorem qp603_6_ok : ClosedPF.check raw (closed (⟨603, by decide⟩ : Fin 1003)) qp603_6 = true := by decide +kernel

theorem cl603_h : ((closed (⟨603, by decide⟩ : Fin 1003)).ok (closedMin (⟨603, by decide⟩ : Fin 1003)) && chainF ((closed (⟨603, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp603.map (fun x => (x.lo, x.hi))) ((closed (⟨603, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp604_0_ok : ClosedPF.check raw (closed (⟨604, by decide⟩ : Fin 1003)) qp604_0 = true := by decide +kernel

theorem cl604_h : ((closed (⟨604, by decide⟩ : Fin 1003)).ok (closedMin (⟨604, by decide⟩ : Fin 1003)) && chainF ((closed (⟨604, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp604.map (fun x => (x.lo, x.hi))) ((closed (⟨604, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp605_0_ok : ClosedPF.check raw (closed (⟨605, by decide⟩ : Fin 1003)) qp605_0 = true := by decide +kernel

theorem qp605_1_ok : ClosedPF.check raw (closed (⟨605, by decide⟩ : Fin 1003)) qp605_1 = true := by decide +kernel

theorem qp605_2_ok : ClosedPF.check raw (closed (⟨605, by decide⟩ : Fin 1003)) qp605_2 = true := by decide +kernel

theorem qp605_3_ok : ClosedPF.check raw (closed (⟨605, by decide⟩ : Fin 1003)) qp605_3 = true := by decide +kernel

theorem qp605_4_ok : ClosedPF.check raw (closed (⟨605, by decide⟩ : Fin 1003)) qp605_4 = true := by decide +kernel

theorem qp605_5_ok : ClosedPF.check raw (closed (⟨605, by decide⟩ : Fin 1003)) qp605_5 = true := by decide +kernel

theorem qp605_6_ok : ClosedPF.check raw (closed (⟨605, by decide⟩ : Fin 1003)) qp605_6 = true := by decide +kernel

theorem cl605_h : ((closed (⟨605, by decide⟩ : Fin 1003)).ok (closedMin (⟨605, by decide⟩ : Fin 1003)) && chainF ((closed (⟨605, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp605.map (fun x => (x.lo, x.hi))) ((closed (⟨605, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp606_0_ok : ClosedPF.check raw (closed (⟨606, by decide⟩ : Fin 1003)) qp606_0 = true := by decide +kernel

theorem qp606_1_ok : ClosedPF.check raw (closed (⟨606, by decide⟩ : Fin 1003)) qp606_1 = true := by decide +kernel

theorem qp606_2_ok : ClosedPF.check raw (closed (⟨606, by decide⟩ : Fin 1003)) qp606_2 = true := by decide +kernel

theorem qp606_3_ok : ClosedPF.check raw (closed (⟨606, by decide⟩ : Fin 1003)) qp606_3 = true := by decide +kernel

theorem qp606_4_ok : ClosedPF.check raw (closed (⟨606, by decide⟩ : Fin 1003)) qp606_4 = true := by decide +kernel

theorem qp606_5_ok : ClosedPF.check raw (closed (⟨606, by decide⟩ : Fin 1003)) qp606_5 = true := by decide +kernel

theorem cl606_h : ((closed (⟨606, by decide⟩ : Fin 1003)).ok (closedMin (⟨606, by decide⟩ : Fin 1003)) && chainF ((closed (⟨606, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp606.map (fun x => (x.lo, x.hi))) ((closed (⟨606, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp607_0_ok : ClosedPF.check raw (closed (⟨607, by decide⟩ : Fin 1003)) qp607_0 = true := by decide +kernel

theorem qp607_1_ok : ClosedPF.check raw (closed (⟨607, by decide⟩ : Fin 1003)) qp607_1 = true := by decide +kernel

theorem qp607_2_ok : ClosedPF.check raw (closed (⟨607, by decide⟩ : Fin 1003)) qp607_2 = true := by decide +kernel

theorem qp607_3_ok : ClosedPF.check raw (closed (⟨607, by decide⟩ : Fin 1003)) qp607_3 = true := by decide +kernel

theorem qp607_4_ok : ClosedPF.check raw (closed (⟨607, by decide⟩ : Fin 1003)) qp607_4 = true := by decide +kernel

theorem cl607_h : ((closed (⟨607, by decide⟩ : Fin 1003)).ok (closedMin (⟨607, by decide⟩ : Fin 1003)) && chainF ((closed (⟨607, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp607.map (fun x => (x.lo, x.hi))) ((closed (⟨607, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp608_0_ok : ClosedPF.check raw (closed (⟨608, by decide⟩ : Fin 1003)) qp608_0 = true := by decide +kernel

theorem cl608_h : ((closed (⟨608, by decide⟩ : Fin 1003)).ok (closedMin (⟨608, by decide⟩ : Fin 1003)) && chainF ((closed (⟨608, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp608.map (fun x => (x.lo, x.hi))) ((closed (⟨608, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp609_0_ok : ClosedPF.check raw (closed (⟨609, by decide⟩ : Fin 1003)) qp609_0 = true := by decide +kernel

theorem qp609_1_ok : ClosedPF.check raw (closed (⟨609, by decide⟩ : Fin 1003)) qp609_1 = true := by decide +kernel

theorem qp609_2_ok : ClosedPF.check raw (closed (⟨609, by decide⟩ : Fin 1003)) qp609_2 = true := by decide +kernel

theorem qp609_3_ok : ClosedPF.check raw (closed (⟨609, by decide⟩ : Fin 1003)) qp609_3 = true := by decide +kernel

theorem cl609_h : ((closed (⟨609, by decide⟩ : Fin 1003)).ok (closedMin (⟨609, by decide⟩ : Fin 1003)) && chainF ((closed (⟨609, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp609.map (fun x => (x.lo, x.hi))) ((closed (⟨609, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp610_0_ok : ClosedPF.check raw (closed (⟨610, by decide⟩ : Fin 1003)) qp610_0 = true := by decide +kernel

theorem qp610_1_ok : ClosedPF.check raw (closed (⟨610, by decide⟩ : Fin 1003)) qp610_1 = true := by decide +kernel

theorem qp610_2_ok : ClosedPF.check raw (closed (⟨610, by decide⟩ : Fin 1003)) qp610_2 = true := by decide +kernel

theorem qp610_3_ok : ClosedPF.check raw (closed (⟨610, by decide⟩ : Fin 1003)) qp610_3 = true := by decide +kernel

theorem qp610_4_ok : ClosedPF.check raw (closed (⟨610, by decide⟩ : Fin 1003)) qp610_4 = true := by decide +kernel

theorem cl610_h : ((closed (⟨610, by decide⟩ : Fin 1003)).ok (closedMin (⟨610, by decide⟩ : Fin 1003)) && chainF ((closed (⟨610, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp610.map (fun x => (x.lo, x.hi))) ((closed (⟨610, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp611_0_ok : ClosedPF.check raw (closed (⟨611, by decide⟩ : Fin 1003)) qp611_0 = true := by decide +kernel

theorem qp611_1_ok : ClosedPF.check raw (closed (⟨611, by decide⟩ : Fin 1003)) qp611_1 = true := by decide +kernel

theorem qp611_2_ok : ClosedPF.check raw (closed (⟨611, by decide⟩ : Fin 1003)) qp611_2 = true := by decide +kernel

theorem cl611_h : ((closed (⟨611, by decide⟩ : Fin 1003)).ok (closedMin (⟨611, by decide⟩ : Fin 1003)) && chainF ((closed (⟨611, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp611.map (fun x => (x.lo, x.hi))) ((closed (⟨611, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp612_0_ok : ClosedPF.check raw (closed (⟨612, by decide⟩ : Fin 1003)) qp612_0 = true := by decide +kernel

theorem qp612_1_ok : ClosedPF.check raw (closed (⟨612, by decide⟩ : Fin 1003)) qp612_1 = true := by decide +kernel

theorem qp612_2_ok : ClosedPF.check raw (closed (⟨612, by decide⟩ : Fin 1003)) qp612_2 = true := by decide +kernel

theorem qp612_3_ok : ClosedPF.check raw (closed (⟨612, by decide⟩ : Fin 1003)) qp612_3 = true := by decide +kernel

theorem cl612_h : ((closed (⟨612, by decide⟩ : Fin 1003)).ok (closedMin (⟨612, by decide⟩ : Fin 1003)) && chainF ((closed (⟨612, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp612.map (fun x => (x.lo, x.hi))) ((closed (⟨612, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp613_0_ok : ClosedPF.check raw (closed (⟨613, by decide⟩ : Fin 1003)) qp613_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
