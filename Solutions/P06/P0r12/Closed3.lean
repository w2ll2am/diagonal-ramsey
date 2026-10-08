import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp23_1_ok : ClosedPF.check raw (closed (⟨23, by decide⟩ : Fin 1003)) qp23_1 = true := by decide +kernel

theorem qp23_2_ok : ClosedPF.check raw (closed (⟨23, by decide⟩ : Fin 1003)) qp23_2 = true := by decide +kernel

theorem cl23_h : ((closed (⟨23, by decide⟩ : Fin 1003)).ok (closedMin (⟨23, by decide⟩ : Fin 1003)) && chainF ((closed (⟨23, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp23.map (fun x => (x.lo, x.hi))) ((closed (⟨23, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp24_0_ok : ClosedPF.check raw (closed (⟨24, by decide⟩ : Fin 1003)) qp24_0 = true := by decide +kernel

theorem qp24_1_ok : ClosedPF.check raw (closed (⟨24, by decide⟩ : Fin 1003)) qp24_1 = true := by decide +kernel

theorem qp24_2_ok : ClosedPF.check raw (closed (⟨24, by decide⟩ : Fin 1003)) qp24_2 = true := by decide +kernel

theorem qp24_3_ok : ClosedPF.check raw (closed (⟨24, by decide⟩ : Fin 1003)) qp24_3 = true := by decide +kernel

theorem qp24_4_ok : ClosedPF.check raw (closed (⟨24, by decide⟩ : Fin 1003)) qp24_4 = true := by decide +kernel

theorem cl24_h : ((closed (⟨24, by decide⟩ : Fin 1003)).ok (closedMin (⟨24, by decide⟩ : Fin 1003)) && chainF ((closed (⟨24, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp24.map (fun x => (x.lo, x.hi))) ((closed (⟨24, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp25_0_ok : ClosedPF.check raw (closed (⟨25, by decide⟩ : Fin 1003)) qp25_0 = true := by decide +kernel

theorem cl25_h : ((closed (⟨25, by decide⟩ : Fin 1003)).ok (closedMin (⟨25, by decide⟩ : Fin 1003)) && chainF ((closed (⟨25, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp25.map (fun x => (x.lo, x.hi))) ((closed (⟨25, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp26_0_ok : ClosedPF.check raw (closed (⟨26, by decide⟩ : Fin 1003)) qp26_0 = true := by decide +kernel

theorem qp26_1_ok : ClosedPF.check raw (closed (⟨26, by decide⟩ : Fin 1003)) qp26_1 = true := by decide +kernel

theorem cl26_h : ((closed (⟨26, by decide⟩ : Fin 1003)).ok (closedMin (⟨26, by decide⟩ : Fin 1003)) && chainF ((closed (⟨26, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp26.map (fun x => (x.lo, x.hi))) ((closed (⟨26, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp27_0_ok : ClosedPF.check raw (closed (⟨27, by decide⟩ : Fin 1003)) qp27_0 = true := by decide +kernel

theorem qp27_1_ok : ClosedPF.check raw (closed (⟨27, by decide⟩ : Fin 1003)) qp27_1 = true := by decide +kernel

theorem cl27_h : ((closed (⟨27, by decide⟩ : Fin 1003)).ok (closedMin (⟨27, by decide⟩ : Fin 1003)) && chainF ((closed (⟨27, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp27.map (fun x => (x.lo, x.hi))) ((closed (⟨27, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp28_0_ok : ClosedPF.check raw (closed (⟨28, by decide⟩ : Fin 1003)) qp28_0 = true := by decide +kernel

theorem qp28_1_ok : ClosedPF.check raw (closed (⟨28, by decide⟩ : Fin 1003)) qp28_1 = true := by decide +kernel

theorem qp28_2_ok : ClosedPF.check raw (closed (⟨28, by decide⟩ : Fin 1003)) qp28_2 = true := by decide +kernel

theorem cl28_h : ((closed (⟨28, by decide⟩ : Fin 1003)).ok (closedMin (⟨28, by decide⟩ : Fin 1003)) && chainF ((closed (⟨28, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp28.map (fun x => (x.lo, x.hi))) ((closed (⟨28, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp29_0_ok : ClosedPF.check raw (closed (⟨29, by decide⟩ : Fin 1003)) qp29_0 = true := by decide +kernel

theorem qp29_1_ok : ClosedPF.check raw (closed (⟨29, by decide⟩ : Fin 1003)) qp29_1 = true := by decide +kernel

theorem cl29_h : ((closed (⟨29, by decide⟩ : Fin 1003)).ok (closedMin (⟨29, by decide⟩ : Fin 1003)) && chainF ((closed (⟨29, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp29.map (fun x => (x.lo, x.hi))) ((closed (⟨29, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp30_0_ok : ClosedPF.check raw (closed (⟨30, by decide⟩ : Fin 1003)) qp30_0 = true := by decide +kernel

theorem cl30_h : ((closed (⟨30, by decide⟩ : Fin 1003)).ok (closedMin (⟨30, by decide⟩ : Fin 1003)) && chainF ((closed (⟨30, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp30.map (fun x => (x.lo, x.hi))) ((closed (⟨30, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp31_0_ok : ClosedPF.check raw (closed (⟨31, by decide⟩ : Fin 1003)) qp31_0 = true := by decide +kernel

theorem qp31_1_ok : ClosedPF.check raw (closed (⟨31, by decide⟩ : Fin 1003)) qp31_1 = true := by decide +kernel

theorem qp31_2_ok : ClosedPF.check raw (closed (⟨31, by decide⟩ : Fin 1003)) qp31_2 = true := by decide +kernel

theorem qp31_3_ok : ClosedPF.check raw (closed (⟨31, by decide⟩ : Fin 1003)) qp31_3 = true := by decide +kernel

theorem cl31_h : ((closed (⟨31, by decide⟩ : Fin 1003)).ok (closedMin (⟨31, by decide⟩ : Fin 1003)) && chainF ((closed (⟨31, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp31.map (fun x => (x.lo, x.hi))) ((closed (⟨31, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp32_0_ok : ClosedPF.check raw (closed (⟨32, by decide⟩ : Fin 1003)) qp32_0 = true := by decide +kernel

theorem qp32_1_ok : ClosedPF.check raw (closed (⟨32, by decide⟩ : Fin 1003)) qp32_1 = true := by decide +kernel

theorem cl32_h : ((closed (⟨32, by decide⟩ : Fin 1003)).ok (closedMin (⟨32, by decide⟩ : Fin 1003)) && chainF ((closed (⟨32, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp32.map (fun x => (x.lo, x.hi))) ((closed (⟨32, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp33_0_ok : ClosedPF.check raw (closed (⟨33, by decide⟩ : Fin 1003)) qp33_0 = true := by decide +kernel

theorem qp33_1_ok : ClosedPF.check raw (closed (⟨33, by decide⟩ : Fin 1003)) qp33_1 = true := by decide +kernel

theorem qp33_2_ok : ClosedPF.check raw (closed (⟨33, by decide⟩ : Fin 1003)) qp33_2 = true := by decide +kernel

theorem qp33_3_ok : ClosedPF.check raw (closed (⟨33, by decide⟩ : Fin 1003)) qp33_3 = true := by decide +kernel

theorem cl33_h : ((closed (⟨33, by decide⟩ : Fin 1003)).ok (closedMin (⟨33, by decide⟩ : Fin 1003)) && chainF ((closed (⟨33, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp33.map (fun x => (x.lo, x.hi))) ((closed (⟨33, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp34_0_ok : ClosedPF.check raw (closed (⟨34, by decide⟩ : Fin 1003)) qp34_0 = true := by decide +kernel

theorem qp34_1_ok : ClosedPF.check raw (closed (⟨34, by decide⟩ : Fin 1003)) qp34_1 = true := by decide +kernel

theorem cl34_h : ((closed (⟨34, by decide⟩ : Fin 1003)).ok (closedMin (⟨34, by decide⟩ : Fin 1003)) && chainF ((closed (⟨34, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp34.map (fun x => (x.lo, x.hi))) ((closed (⟨34, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp35_0_ok : ClosedPF.check raw (closed (⟨35, by decide⟩ : Fin 1003)) qp35_0 = true := by decide +kernel

theorem cl35_h : ((closed (⟨35, by decide⟩ : Fin 1003)).ok (closedMin (⟨35, by decide⟩ : Fin 1003)) && chainF ((closed (⟨35, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp35.map (fun x => (x.lo, x.hi))) ((closed (⟨35, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp36_0_ok : ClosedPF.check raw (closed (⟨36, by decide⟩ : Fin 1003)) qp36_0 = true := by decide +kernel

theorem qp36_1_ok : ClosedPF.check raw (closed (⟨36, by decide⟩ : Fin 1003)) qp36_1 = true := by decide +kernel

theorem qp36_2_ok : ClosedPF.check raw (closed (⟨36, by decide⟩ : Fin 1003)) qp36_2 = true := by decide +kernel

theorem qp36_3_ok : ClosedPF.check raw (closed (⟨36, by decide⟩ : Fin 1003)) qp36_3 = true := by decide +kernel

theorem cl36_h : ((closed (⟨36, by decide⟩ : Fin 1003)).ok (closedMin (⟨36, by decide⟩ : Fin 1003)) && chainF ((closed (⟨36, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp36.map (fun x => (x.lo, x.hi))) ((closed (⟨36, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp37_0_ok : ClosedPF.check raw (closed (⟨37, by decide⟩ : Fin 1003)) qp37_0 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
