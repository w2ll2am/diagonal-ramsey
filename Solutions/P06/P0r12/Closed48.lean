import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D79

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp256_24_ok : ClosedPF.check raw (closed (⟨256, by decide⟩ : Fin 1003)) qp256_24 = true := by decide +kernel

theorem qp256_25_ok : ClosedPF.check raw (closed (⟨256, by decide⟩ : Fin 1003)) qp256_25 = true := by decide +kernel

theorem cl256_h : ((closed (⟨256, by decide⟩ : Fin 1003)).ok (closedMin (⟨256, by decide⟩ : Fin 1003)) && chainF ((closed (⟨256, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp256.map (fun x => (x.lo, x.hi))) ((closed (⟨256, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp257_0_ok : ClosedPF.check raw (closed (⟨257, by decide⟩ : Fin 1003)) qp257_0 = true := by decide +kernel

theorem qp257_1_ok : ClosedPF.check raw (closed (⟨257, by decide⟩ : Fin 1003)) qp257_1 = true := by decide +kernel

theorem qp257_2_ok : ClosedPF.check raw (closed (⟨257, by decide⟩ : Fin 1003)) qp257_2 = true := by decide +kernel

theorem qp257_3_ok : ClosedPF.check raw (closed (⟨257, by decide⟩ : Fin 1003)) qp257_3 = true := by decide +kernel

theorem qp257_4_ok : ClosedPF.check raw (closed (⟨257, by decide⟩ : Fin 1003)) qp257_4 = true := by decide +kernel

theorem qp257_5_ok : ClosedPF.check raw (closed (⟨257, by decide⟩ : Fin 1003)) qp257_5 = true := by decide +kernel

theorem qp257_6_ok : ClosedPF.check raw (closed (⟨257, by decide⟩ : Fin 1003)) qp257_6 = true := by decide +kernel

theorem cl257_h : ((closed (⟨257, by decide⟩ : Fin 1003)).ok (closedMin (⟨257, by decide⟩ : Fin 1003)) && chainF ((closed (⟨257, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp257.map (fun x => (x.lo, x.hi))) ((closed (⟨257, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp258_0_ok : ClosedPF.check raw (closed (⟨258, by decide⟩ : Fin 1003)) qp258_0 = true := by decide +kernel

theorem cl258_h : ((closed (⟨258, by decide⟩ : Fin 1003)).ok (closedMin (⟨258, by decide⟩ : Fin 1003)) && chainF ((closed (⟨258, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp258.map (fun x => (x.lo, x.hi))) ((closed (⟨258, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp259_0_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_0 = true := by decide +kernel

theorem qp259_1_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_1 = true := by decide +kernel

theorem qp259_2_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_2 = true := by decide +kernel

theorem qp259_3_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_3 = true := by decide +kernel

theorem qp259_4_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_4 = true := by decide +kernel

theorem qp259_5_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_5 = true := by decide +kernel

theorem qp259_6_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_6 = true := by decide +kernel

theorem qp259_7_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_7 = true := by decide +kernel

theorem qp259_8_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_8 = true := by decide +kernel

theorem qp259_9_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_9 = true := by decide +kernel

theorem qp259_10_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_10 = true := by decide +kernel

theorem qp259_11_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_11 = true := by decide +kernel

theorem qp259_12_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_12 = true := by decide +kernel

theorem qp259_13_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_13 = true := by decide +kernel

theorem qp259_14_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_14 = true := by decide +kernel

theorem qp259_15_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_15 = true := by decide +kernel

theorem qp259_16_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_16 = true := by decide +kernel

theorem qp259_17_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_17 = true := by decide +kernel

theorem qp259_18_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_18 = true := by decide +kernel

theorem qp259_19_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_19 = true := by decide +kernel

theorem qp259_20_ok : ClosedPF.check raw (closed (⟨259, by decide⟩ : Fin 1003)) qp259_20 = true := by decide +kernel

theorem cl259_h : ((closed (⟨259, by decide⟩ : Fin 1003)).ok (closedMin (⟨259, by decide⟩ : Fin 1003)) && chainF ((closed (⟨259, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp259.map (fun x => (x.lo, x.hi))) ((closed (⟨259, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp260_0_ok : ClosedPF.check raw (closed (⟨260, by decide⟩ : Fin 1003)) qp260_0 = true := by decide +kernel

theorem qp260_1_ok : ClosedPF.check raw (closed (⟨260, by decide⟩ : Fin 1003)) qp260_1 = true := by decide +kernel

theorem qp260_2_ok : ClosedPF.check raw (closed (⟨260, by decide⟩ : Fin 1003)) qp260_2 = true := by decide +kernel

theorem cl260_h : ((closed (⟨260, by decide⟩ : Fin 1003)).ok (closedMin (⟨260, by decide⟩ : Fin 1003)) && chainF ((closed (⟨260, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp260.map (fun x => (x.lo, x.hi))) ((closed (⟨260, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp261_0_ok : ClosedPF.check raw (closed (⟨261, by decide⟩ : Fin 1003)) qp261_0 = true := by decide +kernel

theorem qp261_1_ok : ClosedPF.check raw (closed (⟨261, by decide⟩ : Fin 1003)) qp261_1 = true := by decide +kernel

theorem qp261_2_ok : ClosedPF.check raw (closed (⟨261, by decide⟩ : Fin 1003)) qp261_2 = true := by decide +kernel

theorem qp261_3_ok : ClosedPF.check raw (closed (⟨261, by decide⟩ : Fin 1003)) qp261_3 = true := by decide +kernel

theorem qp261_4_ok : ClosedPF.check raw (closed (⟨261, by decide⟩ : Fin 1003)) qp261_4 = true := by decide +kernel

theorem cl261_h : ((closed (⟨261, by decide⟩ : Fin 1003)).ok (closedMin (⟨261, by decide⟩ : Fin 1003)) && chainF ((closed (⟨261, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp261.map (fun x => (x.lo, x.hi))) ((closed (⟨261, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp262_0_ok : ClosedPF.check raw (closed (⟨262, by decide⟩ : Fin 1003)) qp262_0 = true := by decide +kernel

theorem qp262_1_ok : ClosedPF.check raw (closed (⟨262, by decide⟩ : Fin 1003)) qp262_1 = true := by decide +kernel

theorem qp262_2_ok : ClosedPF.check raw (closed (⟨262, by decide⟩ : Fin 1003)) qp262_2 = true := by decide +kernel

theorem qp262_3_ok : ClosedPF.check raw (closed (⟨262, by decide⟩ : Fin 1003)) qp262_3 = true := by decide +kernel

theorem qp262_4_ok : ClosedPF.check raw (closed (⟨262, by decide⟩ : Fin 1003)) qp262_4 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
