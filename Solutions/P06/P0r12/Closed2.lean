import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp7_0_ok : ClosedPF.check raw (closed (⟨7, by decide⟩ : Fin 1003)) qp7_0 = true := by decide +kernel

theorem qp7_1_ok : ClosedPF.check raw (closed (⟨7, by decide⟩ : Fin 1003)) qp7_1 = true := by decide +kernel

theorem qp7_2_ok : ClosedPF.check raw (closed (⟨7, by decide⟩ : Fin 1003)) qp7_2 = true := by decide +kernel

theorem cl7_h : ((closed (⟨7, by decide⟩ : Fin 1003)).ok (closedMin (⟨7, by decide⟩ : Fin 1003)) && chainF ((closed (⟨7, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp7.map (fun x => (x.lo, x.hi))) ((closed (⟨7, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp8_0_ok : ClosedPF.check raw (closed (⟨8, by decide⟩ : Fin 1003)) qp8_0 = true := by decide +kernel

theorem qp8_1_ok : ClosedPF.check raw (closed (⟨8, by decide⟩ : Fin 1003)) qp8_1 = true := by decide +kernel

theorem qp8_2_ok : ClosedPF.check raw (closed (⟨8, by decide⟩ : Fin 1003)) qp8_2 = true := by decide +kernel

theorem qp8_3_ok : ClosedPF.check raw (closed (⟨8, by decide⟩ : Fin 1003)) qp8_3 = true := by decide +kernel

theorem cl8_h : ((closed (⟨8, by decide⟩ : Fin 1003)).ok (closedMin (⟨8, by decide⟩ : Fin 1003)) && chainF ((closed (⟨8, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp8.map (fun x => (x.lo, x.hi))) ((closed (⟨8, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp9_0_ok : ClosedPF.check raw (closed (⟨9, by decide⟩ : Fin 1003)) qp9_0 = true := by decide +kernel

theorem cl9_h : ((closed (⟨9, by decide⟩ : Fin 1003)).ok (closedMin (⟨9, by decide⟩ : Fin 1003)) && chainF ((closed (⟨9, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp9.map (fun x => (x.lo, x.hi))) ((closed (⟨9, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp10_0_ok : ClosedPF.check raw (closed (⟨10, by decide⟩ : Fin 1003)) qp10_0 = true := by decide +kernel

theorem qp10_1_ok : ClosedPF.check raw (closed (⟨10, by decide⟩ : Fin 1003)) qp10_1 = true := by decide +kernel

theorem qp10_2_ok : ClosedPF.check raw (closed (⟨10, by decide⟩ : Fin 1003)) qp10_2 = true := by decide +kernel

theorem qp10_3_ok : ClosedPF.check raw (closed (⟨10, by decide⟩ : Fin 1003)) qp10_3 = true := by decide +kernel

theorem qp10_4_ok : ClosedPF.check raw (closed (⟨10, by decide⟩ : Fin 1003)) qp10_4 = true := by decide +kernel

theorem cl10_h : ((closed (⟨10, by decide⟩ : Fin 1003)).ok (closedMin (⟨10, by decide⟩ : Fin 1003)) && chainF ((closed (⟨10, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp10.map (fun x => (x.lo, x.hi))) ((closed (⟨10, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp11_0_ok : ClosedPF.check raw (closed (⟨11, by decide⟩ : Fin 1003)) qp11_0 = true := by decide +kernel

theorem qp11_1_ok : ClosedPF.check raw (closed (⟨11, by decide⟩ : Fin 1003)) qp11_1 = true := by decide +kernel

theorem cl11_h : ((closed (⟨11, by decide⟩ : Fin 1003)).ok (closedMin (⟨11, by decide⟩ : Fin 1003)) && chainF ((closed (⟨11, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp11.map (fun x => (x.lo, x.hi))) ((closed (⟨11, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp12_0_ok : ClosedPF.check raw (closed (⟨12, by decide⟩ : Fin 1003)) qp12_0 = true := by decide +kernel

theorem cl12_h : ((closed (⟨12, by decide⟩ : Fin 1003)).ok (closedMin (⟨12, by decide⟩ : Fin 1003)) && chainF ((closed (⟨12, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp12.map (fun x => (x.lo, x.hi))) ((closed (⟨12, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp13_0_ok : ClosedPF.check raw (closed (⟨13, by decide⟩ : Fin 1003)) qp13_0 = true := by decide +kernel

theorem qp13_1_ok : ClosedPF.check raw (closed (⟨13, by decide⟩ : Fin 1003)) qp13_1 = true := by decide +kernel

theorem qp13_2_ok : ClosedPF.check raw (closed (⟨13, by decide⟩ : Fin 1003)) qp13_2 = true := by decide +kernel

theorem cl13_h : ((closed (⟨13, by decide⟩ : Fin 1003)).ok (closedMin (⟨13, by decide⟩ : Fin 1003)) && chainF ((closed (⟨13, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp13.map (fun x => (x.lo, x.hi))) ((closed (⟨13, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp14_0_ok : ClosedPF.check raw (closed (⟨14, by decide⟩ : Fin 1003)) qp14_0 = true := by decide +kernel

theorem cl14_h : ((closed (⟨14, by decide⟩ : Fin 1003)).ok (closedMin (⟨14, by decide⟩ : Fin 1003)) && chainF ((closed (⟨14, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp14.map (fun x => (x.lo, x.hi))) ((closed (⟨14, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp15_0_ok : ClosedPF.check raw (closed (⟨15, by decide⟩ : Fin 1003)) qp15_0 = true := by decide +kernel

theorem qp15_1_ok : ClosedPF.check raw (closed (⟨15, by decide⟩ : Fin 1003)) qp15_1 = true := by decide +kernel

theorem cl15_h : ((closed (⟨15, by decide⟩ : Fin 1003)).ok (closedMin (⟨15, by decide⟩ : Fin 1003)) && chainF ((closed (⟨15, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp15.map (fun x => (x.lo, x.hi))) ((closed (⟨15, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp16_0_ok : ClosedPF.check raw (closed (⟨16, by decide⟩ : Fin 1003)) qp16_0 = true := by decide +kernel

theorem cl16_h : ((closed (⟨16, by decide⟩ : Fin 1003)).ok (closedMin (⟨16, by decide⟩ : Fin 1003)) && chainF ((closed (⟨16, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp16.map (fun x => (x.lo, x.hi))) ((closed (⟨16, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp17_0_ok : ClosedPF.check raw (closed (⟨17, by decide⟩ : Fin 1003)) qp17_0 = true := by decide +kernel

theorem cl17_h : ((closed (⟨17, by decide⟩ : Fin 1003)).ok (closedMin (⟨17, by decide⟩ : Fin 1003)) && chainF ((closed (⟨17, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp17.map (fun x => (x.lo, x.hi))) ((closed (⟨17, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp18_0_ok : ClosedPF.check raw (closed (⟨18, by decide⟩ : Fin 1003)) qp18_0 = true := by decide +kernel

theorem qp18_1_ok : ClosedPF.check raw (closed (⟨18, by decide⟩ : Fin 1003)) qp18_1 = true := by decide +kernel

theorem qp18_2_ok : ClosedPF.check raw (closed (⟨18, by decide⟩ : Fin 1003)) qp18_2 = true := by decide +kernel

theorem cl18_h : ((closed (⟨18, by decide⟩ : Fin 1003)).ok (closedMin (⟨18, by decide⟩ : Fin 1003)) && chainF ((closed (⟨18, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp18.map (fun x => (x.lo, x.hi))) ((closed (⟨18, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp19_0_ok : ClosedPF.check raw (closed (⟨19, by decide⟩ : Fin 1003)) qp19_0 = true := by decide +kernel

theorem qp19_1_ok : ClosedPF.check raw (closed (⟨19, by decide⟩ : Fin 1003)) qp19_1 = true := by decide +kernel

theorem cl19_h : ((closed (⟨19, by decide⟩ : Fin 1003)).ok (closedMin (⟨19, by decide⟩ : Fin 1003)) && chainF ((closed (⟨19, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp19.map (fun x => (x.lo, x.hi))) ((closed (⟨19, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp20_0_ok : ClosedPF.check raw (closed (⟨20, by decide⟩ : Fin 1003)) qp20_0 = true := by decide +kernel

theorem cl20_h : ((closed (⟨20, by decide⟩ : Fin 1003)).ok (closedMin (⟨20, by decide⟩ : Fin 1003)) && chainF ((closed (⟨20, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp20.map (fun x => (x.lo, x.hi))) ((closed (⟨20, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp21_0_ok : ClosedPF.check raw (closed (⟨21, by decide⟩ : Fin 1003)) qp21_0 = true := by decide +kernel

theorem cl21_h : ((closed (⟨21, by decide⟩ : Fin 1003)).ok (closedMin (⟨21, by decide⟩ : Fin 1003)) && chainF ((closed (⟨21, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp21.map (fun x => (x.lo, x.hi))) ((closed (⟨21, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp22_0_ok : ClosedPF.check raw (closed (⟨22, by decide⟩ : Fin 1003)) qp22_0 = true := by decide +kernel

theorem qp22_1_ok : ClosedPF.check raw (closed (⟨22, by decide⟩ : Fin 1003)) qp22_1 = true := by decide +kernel

theorem cl22_h : ((closed (⟨22, by decide⟩ : Fin 1003)).ok (closedMin (⟨22, by decide⟩ : Fin 1003)) && chainF ((closed (⟨22, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp22.map (fun x => (x.lo, x.hi))) ((closed (⟨22, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp23_0_ok : ClosedPF.check raw (closed (⟨23, by decide⟩ : Fin 1003)) qp23_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
