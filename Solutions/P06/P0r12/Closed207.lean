import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D80

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp838_2_ok : ClosedPF.check raw (closed (⟨838, by decide⟩ : Fin 1003)) qp838_2 = true := by decide +kernel

theorem qp838_3_ok : ClosedPF.check raw (closed (⟨838, by decide⟩ : Fin 1003)) qp838_3 = true := by decide +kernel

theorem cl838_h : ((closed (⟨838, by decide⟩ : Fin 1003)).ok (closedMin (⟨838, by decide⟩ : Fin 1003)) && chainF ((closed (⟨838, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp838.map (fun x => (x.lo, x.hi))) ((closed (⟨838, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp839_0_ok : ClosedPF.check raw (closed (⟨839, by decide⟩ : Fin 1003)) qp839_0 = true := by decide +kernel

theorem qp839_1_ok : ClosedPF.check raw (closed (⟨839, by decide⟩ : Fin 1003)) qp839_1 = true := by decide +kernel

theorem qp839_2_ok : ClosedPF.check raw (closed (⟨839, by decide⟩ : Fin 1003)) qp839_2 = true := by decide +kernel

theorem qp839_3_ok : ClosedPF.check raw (closed (⟨839, by decide⟩ : Fin 1003)) qp839_3 = true := by decide +kernel

theorem qp839_4_ok : ClosedPF.check raw (closed (⟨839, by decide⟩ : Fin 1003)) qp839_4 = true := by decide +kernel

theorem qp839_5_ok : ClosedPF.check raw (closed (⟨839, by decide⟩ : Fin 1003)) qp839_5 = true := by decide +kernel

theorem cl839_h : ((closed (⟨839, by decide⟩ : Fin 1003)).ok (closedMin (⟨839, by decide⟩ : Fin 1003)) && chainF ((closed (⟨839, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp839.map (fun x => (x.lo, x.hi))) ((closed (⟨839, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp840_0_ok : ClosedPF.check raw (closed (⟨840, by decide⟩ : Fin 1003)) qp840_0 = true := by decide +kernel

theorem qp840_1_ok : ClosedPF.check raw (closed (⟨840, by decide⟩ : Fin 1003)) qp840_1 = true := by decide +kernel

theorem qp840_2_ok : ClosedPF.check raw (closed (⟨840, by decide⟩ : Fin 1003)) qp840_2 = true := by decide +kernel

theorem cl840_h : ((closed (⟨840, by decide⟩ : Fin 1003)).ok (closedMin (⟨840, by decide⟩ : Fin 1003)) && chainF ((closed (⟨840, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp840.map (fun x => (x.lo, x.hi))) ((closed (⟨840, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp841_0_ok : ClosedPF.check raw (closed (⟨841, by decide⟩ : Fin 1003)) qp841_0 = true := by decide +kernel

theorem qp841_1_ok : ClosedPF.check raw (closed (⟨841, by decide⟩ : Fin 1003)) qp841_1 = true := by decide +kernel

theorem qp841_2_ok : ClosedPF.check raw (closed (⟨841, by decide⟩ : Fin 1003)) qp841_2 = true := by decide +kernel

theorem qp841_3_ok : ClosedPF.check raw (closed (⟨841, by decide⟩ : Fin 1003)) qp841_3 = true := by decide +kernel

theorem cl841_h : ((closed (⟨841, by decide⟩ : Fin 1003)).ok (closedMin (⟨841, by decide⟩ : Fin 1003)) && chainF ((closed (⟨841, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp841.map (fun x => (x.lo, x.hi))) ((closed (⟨841, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp842_0_ok : ClosedPF.check raw (closed (⟨842, by decide⟩ : Fin 1003)) qp842_0 = true := by decide +kernel

theorem qp842_1_ok : ClosedPF.check raw (closed (⟨842, by decide⟩ : Fin 1003)) qp842_1 = true := by decide +kernel

theorem cl842_h : ((closed (⟨842, by decide⟩ : Fin 1003)).ok (closedMin (⟨842, by decide⟩ : Fin 1003)) && chainF ((closed (⟨842, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp842.map (fun x => (x.lo, x.hi))) ((closed (⟨842, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp843_0_ok : ClosedPF.check raw (closed (⟨843, by decide⟩ : Fin 1003)) qp843_0 = true := by decide +kernel

theorem cl843_h : ((closed (⟨843, by decide⟩ : Fin 1003)).ok (closedMin (⟨843, by decide⟩ : Fin 1003)) && chainF ((closed (⟨843, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp843.map (fun x => (x.lo, x.hi))) ((closed (⟨843, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp844_0_ok : ClosedPF.check raw (closed (⟨844, by decide⟩ : Fin 1003)) qp844_0 = true := by decide +kernel

theorem qp844_1_ok : ClosedPF.check raw (closed (⟨844, by decide⟩ : Fin 1003)) qp844_1 = true := by decide +kernel

theorem cl844_h : ((closed (⟨844, by decide⟩ : Fin 1003)).ok (closedMin (⟨844, by decide⟩ : Fin 1003)) && chainF ((closed (⟨844, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp844.map (fun x => (x.lo, x.hi))) ((closed (⟨844, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp845_0_ok : ClosedPF.check raw (closed (⟨845, by decide⟩ : Fin 1003)) qp845_0 = true := by decide +kernel

theorem qp845_1_ok : ClosedPF.check raw (closed (⟨845, by decide⟩ : Fin 1003)) qp845_1 = true := by decide +kernel

theorem cl845_h : ((closed (⟨845, by decide⟩ : Fin 1003)).ok (closedMin (⟨845, by decide⟩ : Fin 1003)) && chainF ((closed (⟨845, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp845.map (fun x => (x.lo, x.hi))) ((closed (⟨845, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp846_0_ok : ClosedPF.check raw (closed (⟨846, by decide⟩ : Fin 1003)) qp846_0 = true := by decide +kernel

theorem cl846_h : ((closed (⟨846, by decide⟩ : Fin 1003)).ok (closedMin (⟨846, by decide⟩ : Fin 1003)) && chainF ((closed (⟨846, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp846.map (fun x => (x.lo, x.hi))) ((closed (⟨846, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp847_0_ok : ClosedPF.check raw (closed (⟨847, by decide⟩ : Fin 1003)) qp847_0 = true := by decide +kernel

theorem cl847_h : ((closed (⟨847, by decide⟩ : Fin 1003)).ok (closedMin (⟨847, by decide⟩ : Fin 1003)) && chainF ((closed (⟨847, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp847.map (fun x => (x.lo, x.hi))) ((closed (⟨847, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp848_0_ok : ClosedPF.check raw (closed (⟨848, by decide⟩ : Fin 1003)) qp848_0 = true := by decide +kernel

theorem cl848_h : ((closed (⟨848, by decide⟩ : Fin 1003)).ok (closedMin (⟨848, by decide⟩ : Fin 1003)) && chainF ((closed (⟨848, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp848.map (fun x => (x.lo, x.hi))) ((closed (⟨848, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp849_0_ok : ClosedPF.check raw (closed (⟨849, by decide⟩ : Fin 1003)) qp849_0 = true := by decide +kernel

theorem cl849_h : ((closed (⟨849, by decide⟩ : Fin 1003)).ok (closedMin (⟨849, by decide⟩ : Fin 1003)) && chainF ((closed (⟨849, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp849.map (fun x => (x.lo, x.hi))) ((closed (⟨849, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp850_0_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_0 = true := by decide +kernel

theorem qp850_1_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_1 = true := by decide +kernel

theorem qp850_2_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_2 = true := by decide +kernel

theorem qp850_3_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_3 = true := by decide +kernel

theorem qp850_4_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_4 = true := by decide +kernel

theorem qp850_5_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_5 = true := by decide +kernel

theorem qp850_6_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_6 = true := by decide +kernel

theorem qp850_7_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_7 = true := by decide +kernel

theorem qp850_8_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_8 = true := by decide +kernel

theorem qp850_9_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_9 = true := by decide +kernel

theorem qp850_10_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_10 = true := by decide +kernel

theorem qp850_11_ok : ClosedPF.check raw (closed (⟨850, by decide⟩ : Fin 1003)) qp850_11 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
