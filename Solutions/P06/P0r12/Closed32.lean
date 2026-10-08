import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp167_5_ok : ClosedPF.check raw (closed (⟨167, by decide⟩ : Fin 1003)) qp167_5 = true := by decide +kernel

theorem qp167_6_ok : ClosedPF.check raw (closed (⟨167, by decide⟩ : Fin 1003)) qp167_6 = true := by decide +kernel

theorem cl167_h : ((closed (⟨167, by decide⟩ : Fin 1003)).ok (closedMin (⟨167, by decide⟩ : Fin 1003)) && chainF ((closed (⟨167, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp167.map (fun x => (x.lo, x.hi))) ((closed (⟨167, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp168_0_ok : ClosedPF.check raw (closed (⟨168, by decide⟩ : Fin 1003)) qp168_0 = true := by decide +kernel

theorem cl168_h : ((closed (⟨168, by decide⟩ : Fin 1003)).ok (closedMin (⟨168, by decide⟩ : Fin 1003)) && chainF ((closed (⟨168, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp168.map (fun x => (x.lo, x.hi))) ((closed (⟨168, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp169_0_ok : ClosedPF.check raw (closed (⟨169, by decide⟩ : Fin 1003)) qp169_0 = true := by decide +kernel

theorem qp169_1_ok : ClosedPF.check raw (closed (⟨169, by decide⟩ : Fin 1003)) qp169_1 = true := by decide +kernel

theorem qp169_2_ok : ClosedPF.check raw (closed (⟨169, by decide⟩ : Fin 1003)) qp169_2 = true := by decide +kernel

theorem cl169_h : ((closed (⟨169, by decide⟩ : Fin 1003)).ok (closedMin (⟨169, by decide⟩ : Fin 1003)) && chainF ((closed (⟨169, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp169.map (fun x => (x.lo, x.hi))) ((closed (⟨169, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp170_0_ok : ClosedPF.check raw (closed (⟨170, by decide⟩ : Fin 1003)) qp170_0 = true := by decide +kernel

theorem cl170_h : ((closed (⟨170, by decide⟩ : Fin 1003)).ok (closedMin (⟨170, by decide⟩ : Fin 1003)) && chainF ((closed (⟨170, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp170.map (fun x => (x.lo, x.hi))) ((closed (⟨170, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp171_0_ok : ClosedPF.check raw (closed (⟨171, by decide⟩ : Fin 1003)) qp171_0 = true := by decide +kernel

theorem cl171_h : ((closed (⟨171, by decide⟩ : Fin 1003)).ok (closedMin (⟨171, by decide⟩ : Fin 1003)) && chainF ((closed (⟨171, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp171.map (fun x => (x.lo, x.hi))) ((closed (⟨171, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp172_0_ok : ClosedPF.check raw (closed (⟨172, by decide⟩ : Fin 1003)) qp172_0 = true := by decide +kernel

theorem qp172_1_ok : ClosedPF.check raw (closed (⟨172, by decide⟩ : Fin 1003)) qp172_1 = true := by decide +kernel

theorem qp172_2_ok : ClosedPF.check raw (closed (⟨172, by decide⟩ : Fin 1003)) qp172_2 = true := by decide +kernel

theorem qp172_3_ok : ClosedPF.check raw (closed (⟨172, by decide⟩ : Fin 1003)) qp172_3 = true := by decide +kernel

theorem cl172_h : ((closed (⟨172, by decide⟩ : Fin 1003)).ok (closedMin (⟨172, by decide⟩ : Fin 1003)) && chainF ((closed (⟨172, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp172.map (fun x => (x.lo, x.hi))) ((closed (⟨172, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp173_0_ok : ClosedPF.check raw (closed (⟨173, by decide⟩ : Fin 1003)) qp173_0 = true := by decide +kernel

theorem cl173_h : ((closed (⟨173, by decide⟩ : Fin 1003)).ok (closedMin (⟨173, by decide⟩ : Fin 1003)) && chainF ((closed (⟨173, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp173.map (fun x => (x.lo, x.hi))) ((closed (⟨173, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp174_0_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_0 = true := by decide +kernel

theorem qp174_1_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_1 = true := by decide +kernel

theorem qp174_2_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_2 = true := by decide +kernel

theorem qp174_3_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_3 = true := by decide +kernel

theorem qp174_4_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_4 = true := by decide +kernel

theorem qp174_5_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_5 = true := by decide +kernel

theorem qp174_6_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_6 = true := by decide +kernel

theorem qp174_7_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_7 = true := by decide +kernel

theorem qp174_8_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_8 = true := by decide +kernel

theorem qp174_9_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_9 = true := by decide +kernel

theorem qp174_10_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_10 = true := by decide +kernel

theorem qp174_11_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_11 = true := by decide +kernel

theorem qp174_12_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_12 = true := by decide +kernel

theorem qp174_13_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_13 = true := by decide +kernel

theorem qp174_14_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_14 = true := by decide +kernel

theorem qp174_15_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_15 = true := by decide +kernel

theorem qp174_16_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_16 = true := by decide +kernel

theorem qp174_17_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_17 = true := by decide +kernel

theorem qp174_18_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_18 = true := by decide +kernel

theorem qp174_19_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_19 = true := by decide +kernel

theorem qp174_20_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_20 = true := by decide +kernel

theorem qp174_21_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_21 = true := by decide +kernel

theorem qp174_22_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_22 = true := by decide +kernel

theorem qp174_23_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_23 = true := by decide +kernel

theorem qp174_24_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_24 = true := by decide +kernel

theorem qp174_25_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_25 = true := by decide +kernel

theorem qp174_26_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_26 = true := by decide +kernel

theorem qp174_27_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_27 = true := by decide +kernel

theorem qp174_28_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_28 = true := by decide +kernel

theorem qp174_29_ok : ClosedPF.check raw (closed (⟨174, by decide⟩ : Fin 1003)) qp174_29 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
