import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D80

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp723_15_ok : ClosedPF.check raw (closed (⟨723, by decide⟩ : Fin 1003)) qp723_15 = true := by decide +kernel

theorem qp723_16_ok : ClosedPF.check raw (closed (⟨723, by decide⟩ : Fin 1003)) qp723_16 = true := by decide +kernel

theorem qp723_17_ok : ClosedPF.check raw (closed (⟨723, by decide⟩ : Fin 1003)) qp723_17 = true := by decide +kernel

theorem cl723_h : ((closed (⟨723, by decide⟩ : Fin 1003)).ok (closedMin (⟨723, by decide⟩ : Fin 1003)) && chainF ((closed (⟨723, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp723.map (fun x => (x.lo, x.hi))) ((closed (⟨723, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp724_0_ok : ClosedPF.check raw (closed (⟨724, by decide⟩ : Fin 1003)) qp724_0 = true := by decide +kernel

theorem qp724_1_ok : ClosedPF.check raw (closed (⟨724, by decide⟩ : Fin 1003)) qp724_1 = true := by decide +kernel

theorem qp724_2_ok : ClosedPF.check raw (closed (⟨724, by decide⟩ : Fin 1003)) qp724_2 = true := by decide +kernel

theorem qp724_3_ok : ClosedPF.check raw (closed (⟨724, by decide⟩ : Fin 1003)) qp724_3 = true := by decide +kernel

theorem qp724_4_ok : ClosedPF.check raw (closed (⟨724, by decide⟩ : Fin 1003)) qp724_4 = true := by decide +kernel

theorem cl724_h : ((closed (⟨724, by decide⟩ : Fin 1003)).ok (closedMin (⟨724, by decide⟩ : Fin 1003)) && chainF ((closed (⟨724, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp724.map (fun x => (x.lo, x.hi))) ((closed (⟨724, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp725_0_ok : ClosedPF.check raw (closed (⟨725, by decide⟩ : Fin 1003)) qp725_0 = true := by decide +kernel

theorem qp725_1_ok : ClosedPF.check raw (closed (⟨725, by decide⟩ : Fin 1003)) qp725_1 = true := by decide +kernel

theorem cl725_h : ((closed (⟨725, by decide⟩ : Fin 1003)).ok (closedMin (⟨725, by decide⟩ : Fin 1003)) && chainF ((closed (⟨725, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp725.map (fun x => (x.lo, x.hi))) ((closed (⟨725, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp726_0_ok : ClosedPF.check raw (closed (⟨726, by decide⟩ : Fin 1003)) qp726_0 = true := by decide +kernel

theorem cl726_h : ((closed (⟨726, by decide⟩ : Fin 1003)).ok (closedMin (⟨726, by decide⟩ : Fin 1003)) && chainF ((closed (⟨726, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp726.map (fun x => (x.lo, x.hi))) ((closed (⟨726, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp727_0_ok : ClosedPF.check raw (closed (⟨727, by decide⟩ : Fin 1003)) qp727_0 = true := by decide +kernel

theorem qp727_1_ok : ClosedPF.check raw (closed (⟨727, by decide⟩ : Fin 1003)) qp727_1 = true := by decide +kernel

theorem cl727_h : ((closed (⟨727, by decide⟩ : Fin 1003)).ok (closedMin (⟨727, by decide⟩ : Fin 1003)) && chainF ((closed (⟨727, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp727.map (fun x => (x.lo, x.hi))) ((closed (⟨727, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp728_0_ok : ClosedPF.check raw (closed (⟨728, by decide⟩ : Fin 1003)) qp728_0 = true := by decide +kernel

theorem cl728_h : ((closed (⟨728, by decide⟩ : Fin 1003)).ok (closedMin (⟨728, by decide⟩ : Fin 1003)) && chainF ((closed (⟨728, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp728.map (fun x => (x.lo, x.hi))) ((closed (⟨728, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp729_0_ok : ClosedPF.check raw (closed (⟨729, by decide⟩ : Fin 1003)) qp729_0 = true := by decide +kernel

theorem cl729_h : ((closed (⟨729, by decide⟩ : Fin 1003)).ok (closedMin (⟨729, by decide⟩ : Fin 1003)) && chainF ((closed (⟨729, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp729.map (fun x => (x.lo, x.hi))) ((closed (⟨729, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp730_0_ok : ClosedPF.check raw (closed (⟨730, by decide⟩ : Fin 1003)) qp730_0 = true := by decide +kernel

theorem qp730_1_ok : ClosedPF.check raw (closed (⟨730, by decide⟩ : Fin 1003)) qp730_1 = true := by decide +kernel

theorem cl730_h : ((closed (⟨730, by decide⟩ : Fin 1003)).ok (closedMin (⟨730, by decide⟩ : Fin 1003)) && chainF ((closed (⟨730, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp730.map (fun x => (x.lo, x.hi))) ((closed (⟨730, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp731_0_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_0 = true := by decide +kernel

theorem qp731_1_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_1 = true := by decide +kernel

theorem qp731_2_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_2 = true := by decide +kernel

theorem qp731_3_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_3 = true := by decide +kernel

theorem qp731_4_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_4 = true := by decide +kernel

theorem qp731_5_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_5 = true := by decide +kernel

theorem qp731_6_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_6 = true := by decide +kernel

theorem qp731_7_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_7 = true := by decide +kernel

theorem qp731_8_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_8 = true := by decide +kernel

theorem qp731_9_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_9 = true := by decide +kernel

theorem qp731_10_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_10 = true := by decide +kernel

theorem qp731_11_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_11 = true := by decide +kernel

theorem qp731_12_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_12 = true := by decide +kernel

theorem qp731_13_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_13 = true := by decide +kernel

theorem qp731_14_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_14 = true := by decide +kernel

theorem qp731_15_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_15 = true := by decide +kernel

theorem qp731_16_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_16 = true := by decide +kernel

theorem qp731_17_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_17 = true := by decide +kernel

theorem qp731_18_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_18 = true := by decide +kernel

theorem qp731_19_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_19 = true := by decide +kernel

theorem qp731_20_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_20 = true := by decide +kernel

theorem qp731_21_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_21 = true := by decide +kernel

theorem qp731_22_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_22 = true := by decide +kernel

theorem qp731_23_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_23 = true := by decide +kernel

theorem qp731_24_ok : ClosedPF.check raw (closed (⟨731, by decide⟩ : Fin 1003)) qp731_24 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
