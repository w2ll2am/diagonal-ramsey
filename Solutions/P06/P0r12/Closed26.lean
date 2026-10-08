import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp115_4_ok : ClosedPF.check raw (closed (⟨115, by decide⟩ : Fin 1003)) qp115_4 = true := by decide +kernel

theorem qp115_5_ok : ClosedPF.check raw (closed (⟨115, by decide⟩ : Fin 1003)) qp115_5 = true := by decide +kernel

theorem cl115_h : ((closed (⟨115, by decide⟩ : Fin 1003)).ok (closedMin (⟨115, by decide⟩ : Fin 1003)) && chainF ((closed (⟨115, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp115.map (fun x => (x.lo, x.hi))) ((closed (⟨115, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp116_0_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_0 = true := by decide +kernel

theorem qp116_1_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_1 = true := by decide +kernel

theorem qp116_2_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_2 = true := by decide +kernel

theorem qp116_3_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_3 = true := by decide +kernel

theorem qp116_4_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_4 = true := by decide +kernel

theorem qp116_5_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_5 = true := by decide +kernel

theorem qp116_6_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_6 = true := by decide +kernel

theorem qp116_7_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_7 = true := by decide +kernel

theorem qp116_8_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_8 = true := by decide +kernel

theorem qp116_9_ok : ClosedPF.check raw (closed (⟨116, by decide⟩ : Fin 1003)) qp116_9 = true := by decide +kernel

theorem cl116_h : ((closed (⟨116, by decide⟩ : Fin 1003)).ok (closedMin (⟨116, by decide⟩ : Fin 1003)) && chainF ((closed (⟨116, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp116.map (fun x => (x.lo, x.hi))) ((closed (⟨116, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp117_0_ok : ClosedPF.check raw (closed (⟨117, by decide⟩ : Fin 1003)) qp117_0 = true := by decide +kernel

theorem qp117_1_ok : ClosedPF.check raw (closed (⟨117, by decide⟩ : Fin 1003)) qp117_1 = true := by decide +kernel

theorem qp117_2_ok : ClosedPF.check raw (closed (⟨117, by decide⟩ : Fin 1003)) qp117_2 = true := by decide +kernel

theorem qp117_3_ok : ClosedPF.check raw (closed (⟨117, by decide⟩ : Fin 1003)) qp117_3 = true := by decide +kernel

theorem qp117_4_ok : ClosedPF.check raw (closed (⟨117, by decide⟩ : Fin 1003)) qp117_4 = true := by decide +kernel

theorem qp117_5_ok : ClosedPF.check raw (closed (⟨117, by decide⟩ : Fin 1003)) qp117_5 = true := by decide +kernel

theorem cl117_h : ((closed (⟨117, by decide⟩ : Fin 1003)).ok (closedMin (⟨117, by decide⟩ : Fin 1003)) && chainF ((closed (⟨117, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp117.map (fun x => (x.lo, x.hi))) ((closed (⟨117, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp118_0_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_0 = true := by decide +kernel

theorem qp118_1_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_1 = true := by decide +kernel

theorem qp118_2_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_2 = true := by decide +kernel

theorem qp118_3_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_3 = true := by decide +kernel

theorem qp118_4_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_4 = true := by decide +kernel

theorem qp118_5_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_5 = true := by decide +kernel

theorem qp118_6_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_6 = true := by decide +kernel

theorem qp118_7_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_7 = true := by decide +kernel

theorem qp118_8_ok : ClosedPF.check raw (closed (⟨118, by decide⟩ : Fin 1003)) qp118_8 = true := by decide +kernel

theorem cl118_h : ((closed (⟨118, by decide⟩ : Fin 1003)).ok (closedMin (⟨118, by decide⟩ : Fin 1003)) && chainF ((closed (⟨118, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp118.map (fun x => (x.lo, x.hi))) ((closed (⟨118, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp119_0_ok : ClosedPF.check raw (closed (⟨119, by decide⟩ : Fin 1003)) qp119_0 = true := by decide +kernel

theorem cl119_h : ((closed (⟨119, by decide⟩ : Fin 1003)).ok (closedMin (⟨119, by decide⟩ : Fin 1003)) && chainF ((closed (⟨119, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp119.map (fun x => (x.lo, x.hi))) ((closed (⟨119, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp120_0_ok : ClosedPF.check raw (closed (⟨120, by decide⟩ : Fin 1003)) qp120_0 = true := by decide +kernel

theorem qp120_1_ok : ClosedPF.check raw (closed (⟨120, by decide⟩ : Fin 1003)) qp120_1 = true := by decide +kernel

theorem qp120_2_ok : ClosedPF.check raw (closed (⟨120, by decide⟩ : Fin 1003)) qp120_2 = true := by decide +kernel

theorem qp120_3_ok : ClosedPF.check raw (closed (⟨120, by decide⟩ : Fin 1003)) qp120_3 = true := by decide +kernel

theorem qp120_4_ok : ClosedPF.check raw (closed (⟨120, by decide⟩ : Fin 1003)) qp120_4 = true := by decide +kernel

theorem qp120_5_ok : ClosedPF.check raw (closed (⟨120, by decide⟩ : Fin 1003)) qp120_5 = true := by decide +kernel

theorem qp120_6_ok : ClosedPF.check raw (closed (⟨120, by decide⟩ : Fin 1003)) qp120_6 = true := by decide +kernel

theorem cl120_h : ((closed (⟨120, by decide⟩ : Fin 1003)).ok (closedMin (⟨120, by decide⟩ : Fin 1003)) && chainF ((closed (⟨120, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp120.map (fun x => (x.lo, x.hi))) ((closed (⟨120, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp121_0_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_0 = true := by decide +kernel

theorem qp121_1_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_1 = true := by decide +kernel

theorem qp121_2_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_2 = true := by decide +kernel

theorem qp121_3_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_3 = true := by decide +kernel

theorem qp121_4_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_4 = true := by decide +kernel

theorem qp121_5_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_5 = true := by decide +kernel

theorem qp121_6_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_6 = true := by decide +kernel

theorem qp121_7_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_7 = true := by decide +kernel

theorem qp121_8_ok : ClosedPF.check raw (closed (⟨121, by decide⟩ : Fin 1003)) qp121_8 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
