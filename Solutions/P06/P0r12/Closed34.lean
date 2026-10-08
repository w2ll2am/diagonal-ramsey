import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D78

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp182_2_ok : ClosedPF.check raw (closed (⟨182, by decide⟩ : Fin 1003)) qp182_2 = true := by decide +kernel

theorem qp182_3_ok : ClosedPF.check raw (closed (⟨182, by decide⟩ : Fin 1003)) qp182_3 = true := by decide +kernel

theorem qp182_4_ok : ClosedPF.check raw (closed (⟨182, by decide⟩ : Fin 1003)) qp182_4 = true := by decide +kernel

theorem cl182_h : ((closed (⟨182, by decide⟩ : Fin 1003)).ok (closedMin (⟨182, by decide⟩ : Fin 1003)) && chainF ((closed (⟨182, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp182.map (fun x => (x.lo, x.hi))) ((closed (⟨182, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp183_0_ok : ClosedPF.check raw (closed (⟨183, by decide⟩ : Fin 1003)) qp183_0 = true := by decide +kernel

theorem qp183_1_ok : ClosedPF.check raw (closed (⟨183, by decide⟩ : Fin 1003)) qp183_1 = true := by decide +kernel

theorem cl183_h : ((closed (⟨183, by decide⟩ : Fin 1003)).ok (closedMin (⟨183, by decide⟩ : Fin 1003)) && chainF ((closed (⟨183, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp183.map (fun x => (x.lo, x.hi))) ((closed (⟨183, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp184_0_ok : ClosedPF.check raw (closed (⟨184, by decide⟩ : Fin 1003)) qp184_0 = true := by decide +kernel

theorem cl184_h : ((closed (⟨184, by decide⟩ : Fin 1003)).ok (closedMin (⟨184, by decide⟩ : Fin 1003)) && chainF ((closed (⟨184, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp184.map (fun x => (x.lo, x.hi))) ((closed (⟨184, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp185_0_ok : ClosedPF.check raw (closed (⟨185, by decide⟩ : Fin 1003)) qp185_0 = true := by decide +kernel

theorem cl185_h : ((closed (⟨185, by decide⟩ : Fin 1003)).ok (closedMin (⟨185, by decide⟩ : Fin 1003)) && chainF ((closed (⟨185, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp185.map (fun x => (x.lo, x.hi))) ((closed (⟨185, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp186_0_ok : ClosedPF.check raw (closed (⟨186, by decide⟩ : Fin 1003)) qp186_0 = true := by decide +kernel

theorem qp186_1_ok : ClosedPF.check raw (closed (⟨186, by decide⟩ : Fin 1003)) qp186_1 = true := by decide +kernel

theorem cl186_h : ((closed (⟨186, by decide⟩ : Fin 1003)).ok (closedMin (⟨186, by decide⟩ : Fin 1003)) && chainF ((closed (⟨186, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp186.map (fun x => (x.lo, x.hi))) ((closed (⟨186, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp187_0_ok : ClosedPF.check raw (closed (⟨187, by decide⟩ : Fin 1003)) qp187_0 = true := by decide +kernel

theorem qp187_1_ok : ClosedPF.check raw (closed (⟨187, by decide⟩ : Fin 1003)) qp187_1 = true := by decide +kernel

theorem qp187_2_ok : ClosedPF.check raw (closed (⟨187, by decide⟩ : Fin 1003)) qp187_2 = true := by decide +kernel

theorem qp187_3_ok : ClosedPF.check raw (closed (⟨187, by decide⟩ : Fin 1003)) qp187_3 = true := by decide +kernel

theorem qp187_4_ok : ClosedPF.check raw (closed (⟨187, by decide⟩ : Fin 1003)) qp187_4 = true := by decide +kernel

theorem cl187_h : ((closed (⟨187, by decide⟩ : Fin 1003)).ok (closedMin (⟨187, by decide⟩ : Fin 1003)) && chainF ((closed (⟨187, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp187.map (fun x => (x.lo, x.hi))) ((closed (⟨187, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp188_0_ok : ClosedPF.check raw (closed (⟨188, by decide⟩ : Fin 1003)) qp188_0 = true := by decide +kernel

theorem qp188_1_ok : ClosedPF.check raw (closed (⟨188, by decide⟩ : Fin 1003)) qp188_1 = true := by decide +kernel

theorem cl188_h : ((closed (⟨188, by decide⟩ : Fin 1003)).ok (closedMin (⟨188, by decide⟩ : Fin 1003)) && chainF ((closed (⟨188, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp188.map (fun x => (x.lo, x.hi))) ((closed (⟨188, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp189_0_ok : ClosedPF.check raw (closed (⟨189, by decide⟩ : Fin 1003)) qp189_0 = true := by decide +kernel

theorem cl189_h : ((closed (⟨189, by decide⟩ : Fin 1003)).ok (closedMin (⟨189, by decide⟩ : Fin 1003)) && chainF ((closed (⟨189, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp189.map (fun x => (x.lo, x.hi))) ((closed (⟨189, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp190_0_ok : ClosedPF.check raw (closed (⟨190, by decide⟩ : Fin 1003)) qp190_0 = true := by decide +kernel

theorem cl190_h : ((closed (⟨190, by decide⟩ : Fin 1003)).ok (closedMin (⟨190, by decide⟩ : Fin 1003)) && chainF ((closed (⟨190, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp190.map (fun x => (x.lo, x.hi))) ((closed (⟨190, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp191_0_ok : ClosedPF.check raw (closed (⟨191, by decide⟩ : Fin 1003)) qp191_0 = true := by decide +kernel

theorem cl191_h : ((closed (⟨191, by decide⟩ : Fin 1003)).ok (closedMin (⟨191, by decide⟩ : Fin 1003)) && chainF ((closed (⟨191, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp191.map (fun x => (x.lo, x.hi))) ((closed (⟨191, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp192_0_ok : ClosedPF.check raw (closed (⟨192, by decide⟩ : Fin 1003)) qp192_0 = true := by decide +kernel

theorem qp192_1_ok : ClosedPF.check raw (closed (⟨192, by decide⟩ : Fin 1003)) qp192_1 = true := by decide +kernel

theorem cl192_h : ((closed (⟨192, by decide⟩ : Fin 1003)).ok (closedMin (⟨192, by decide⟩ : Fin 1003)) && chainF ((closed (⟨192, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp192.map (fun x => (x.lo, x.hi))) ((closed (⟨192, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp193_0_ok : ClosedPF.check raw (closed (⟨193, by decide⟩ : Fin 1003)) qp193_0 = true := by decide +kernel

theorem cl193_h : ((closed (⟨193, by decide⟩ : Fin 1003)).ok (closedMin (⟨193, by decide⟩ : Fin 1003)) && chainF ((closed (⟨193, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp193.map (fun x => (x.lo, x.hi))) ((closed (⟨193, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp194_0_ok : ClosedPF.check raw (closed (⟨194, by decide⟩ : Fin 1003)) qp194_0 = true := by decide +kernel

theorem qp194_1_ok : ClosedPF.check raw (closed (⟨194, by decide⟩ : Fin 1003)) qp194_1 = true := by decide +kernel

theorem cl194_h : ((closed (⟨194, by decide⟩ : Fin 1003)).ok (closedMin (⟨194, by decide⟩ : Fin 1003)) && chainF ((closed (⟨194, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp194.map (fun x => (x.lo, x.hi))) ((closed (⟨194, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp195_0_ok : ClosedPF.check raw (closed (⟨195, by decide⟩ : Fin 1003)) qp195_0 = true := by decide +kernel

theorem qp195_1_ok : ClosedPF.check raw (closed (⟨195, by decide⟩ : Fin 1003)) qp195_1 = true := by decide +kernel

theorem cl195_h : ((closed (⟨195, by decide⟩ : Fin 1003)).ok (closedMin (⟨195, by decide⟩ : Fin 1003)) && chainF ((closed (⟨195, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp195.map (fun x => (x.lo, x.hi))) ((closed (⟨195, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp196_0_ok : ClosedPF.check raw (closed (⟨196, by decide⟩ : Fin 1003)) qp196_0 = true := by decide +kernel

theorem qp196_1_ok : ClosedPF.check raw (closed (⟨196, by decide⟩ : Fin 1003)) qp196_1 = true := by decide +kernel

theorem qp196_2_ok : ClosedPF.check raw (closed (⟨196, by decide⟩ : Fin 1003)) qp196_2 = true := by decide +kernel

theorem cl196_h : ((closed (⟨196, by decide⟩ : Fin 1003)).ok (closedMin (⟨196, by decide⟩ : Fin 1003)) && chainF ((closed (⟨196, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp196.map (fun x => (x.lo, x.hi))) ((closed (⟨196, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp197_0_ok : ClosedPF.check raw (closed (⟨197, by decide⟩ : Fin 1003)) qp197_0 = true := by decide +kernel

theorem cl197_h : ((closed (⟨197, by decide⟩ : Fin 1003)).ok (closedMin (⟨197, by decide⟩ : Fin 1003)) && chainF ((closed (⟨197, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp197.map (fun x => (x.lo, x.hi))) ((closed (⟨197, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp198_0_ok : ClosedPF.check raw (closed (⟨198, by decide⟩ : Fin 1003)) qp198_0 = true := by decide +kernel

theorem qp198_1_ok : ClosedPF.check raw (closed (⟨198, by decide⟩ : Fin 1003)) qp198_1 = true := by decide +kernel

theorem qp198_2_ok : ClosedPF.check raw (closed (⟨198, by decide⟩ : Fin 1003)) qp198_2 = true := by decide +kernel

theorem qp198_3_ok : ClosedPF.check raw (closed (⟨198, by decide⟩ : Fin 1003)) qp198_3 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
