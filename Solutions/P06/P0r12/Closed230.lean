import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D81

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem qp910_3_ok : ClosedPF.check raw (closed (⟨910, by decide⟩ : Fin 1003)) qp910_3 = true := by decide +kernel

theorem cl910_h : ((closed (⟨910, by decide⟩ : Fin 1003)).ok (closedMin (⟨910, by decide⟩ : Fin 1003)) && chainF ((closed (⟨910, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp910.map (fun x => (x.lo, x.hi))) ((closed (⟨910, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp911_0_ok : ClosedPF.check raw (closed (⟨911, by decide⟩ : Fin 1003)) qp911_0 = true := by decide +kernel

theorem qp911_1_ok : ClosedPF.check raw (closed (⟨911, by decide⟩ : Fin 1003)) qp911_1 = true := by decide +kernel

theorem qp911_2_ok : ClosedPF.check raw (closed (⟨911, by decide⟩ : Fin 1003)) qp911_2 = true := by decide +kernel

theorem qp911_3_ok : ClosedPF.check raw (closed (⟨911, by decide⟩ : Fin 1003)) qp911_3 = true := by decide +kernel

theorem cl911_h : ((closed (⟨911, by decide⟩ : Fin 1003)).ok (closedMin (⟨911, by decide⟩ : Fin 1003)) && chainF ((closed (⟨911, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp911.map (fun x => (x.lo, x.hi))) ((closed (⟨911, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp912_0_ok : ClosedPF.check raw (closed (⟨912, by decide⟩ : Fin 1003)) qp912_0 = true := by decide +kernel

theorem qp912_1_ok : ClosedPF.check raw (closed (⟨912, by decide⟩ : Fin 1003)) qp912_1 = true := by decide +kernel

theorem qp912_2_ok : ClosedPF.check raw (closed (⟨912, by decide⟩ : Fin 1003)) qp912_2 = true := by decide +kernel

theorem qp912_3_ok : ClosedPF.check raw (closed (⟨912, by decide⟩ : Fin 1003)) qp912_3 = true := by decide +kernel

theorem qp912_4_ok : ClosedPF.check raw (closed (⟨912, by decide⟩ : Fin 1003)) qp912_4 = true := by decide +kernel

theorem cl912_h : ((closed (⟨912, by decide⟩ : Fin 1003)).ok (closedMin (⟨912, by decide⟩ : Fin 1003)) && chainF ((closed (⟨912, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp912.map (fun x => (x.lo, x.hi))) ((closed (⟨912, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp913_0_ok : ClosedPF.check raw (closed (⟨913, by decide⟩ : Fin 1003)) qp913_0 = true := by decide +kernel

theorem qp913_1_ok : ClosedPF.check raw (closed (⟨913, by decide⟩ : Fin 1003)) qp913_1 = true := by decide +kernel

theorem qp913_2_ok : ClosedPF.check raw (closed (⟨913, by decide⟩ : Fin 1003)) qp913_2 = true := by decide +kernel

theorem cl913_h : ((closed (⟨913, by decide⟩ : Fin 1003)).ok (closedMin (⟨913, by decide⟩ : Fin 1003)) && chainF ((closed (⟨913, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp913.map (fun x => (x.lo, x.hi))) ((closed (⟨913, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp914_0_ok : ClosedPF.check raw (closed (⟨914, by decide⟩ : Fin 1003)) qp914_0 = true := by decide +kernel

theorem qp914_1_ok : ClosedPF.check raw (closed (⟨914, by decide⟩ : Fin 1003)) qp914_1 = true := by decide +kernel

theorem cl914_h : ((closed (⟨914, by decide⟩ : Fin 1003)).ok (closedMin (⟨914, by decide⟩ : Fin 1003)) && chainF ((closed (⟨914, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp914.map (fun x => (x.lo, x.hi))) ((closed (⟨914, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp915_0_ok : ClosedPF.check raw (closed (⟨915, by decide⟩ : Fin 1003)) qp915_0 = true := by decide +kernel

theorem qp915_1_ok : ClosedPF.check raw (closed (⟨915, by decide⟩ : Fin 1003)) qp915_1 = true := by decide +kernel

theorem cl915_h : ((closed (⟨915, by decide⟩ : Fin 1003)).ok (closedMin (⟨915, by decide⟩ : Fin 1003)) && chainF ((closed (⟨915, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp915.map (fun x => (x.lo, x.hi))) ((closed (⟨915, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp916_0_ok : ClosedPF.check raw (closed (⟨916, by decide⟩ : Fin 1003)) qp916_0 = true := by decide +kernel

theorem cl916_h : ((closed (⟨916, by decide⟩ : Fin 1003)).ok (closedMin (⟨916, by decide⟩ : Fin 1003)) && chainF ((closed (⟨916, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp916.map (fun x => (x.lo, x.hi))) ((closed (⟨916, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp917_0_ok : ClosedPF.check raw (closed (⟨917, by decide⟩ : Fin 1003)) qp917_0 = true := by decide +kernel

theorem qp917_1_ok : ClosedPF.check raw (closed (⟨917, by decide⟩ : Fin 1003)) qp917_1 = true := by decide +kernel

theorem cl917_h : ((closed (⟨917, by decide⟩ : Fin 1003)).ok (closedMin (⟨917, by decide⟩ : Fin 1003)) && chainF ((closed (⟨917, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp917.map (fun x => (x.lo, x.hi))) ((closed (⟨917, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp918_0_ok : ClosedPF.check raw (closed (⟨918, by decide⟩ : Fin 1003)) qp918_0 = true := by decide +kernel

theorem qp918_1_ok : ClosedPF.check raw (closed (⟨918, by decide⟩ : Fin 1003)) qp918_1 = true := by decide +kernel

theorem cl918_h : ((closed (⟨918, by decide⟩ : Fin 1003)).ok (closedMin (⟨918, by decide⟩ : Fin 1003)) && chainF ((closed (⟨918, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp918.map (fun x => (x.lo, x.hi))) ((closed (⟨918, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp919_0_ok : ClosedPF.check raw (closed (⟨919, by decide⟩ : Fin 1003)) qp919_0 = true := by decide +kernel

theorem qp919_1_ok : ClosedPF.check raw (closed (⟨919, by decide⟩ : Fin 1003)) qp919_1 = true := by decide +kernel

theorem cl919_h : ((closed (⟨919, by decide⟩ : Fin 1003)).ok (closedMin (⟨919, by decide⟩ : Fin 1003)) && chainF ((closed (⟨919, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp919.map (fun x => (x.lo, x.hi))) ((closed (⟨919, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp920_0_ok : ClosedPF.check raw (closed (⟨920, by decide⟩ : Fin 1003)) qp920_0 = true := by decide +kernel

theorem cl920_h : ((closed (⟨920, by decide⟩ : Fin 1003)).ok (closedMin (⟨920, by decide⟩ : Fin 1003)) && chainF ((closed (⟨920, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp920.map (fun x => (x.lo, x.hi))) ((closed (⟨920, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp921_0_ok : ClosedPF.check raw (closed (⟨921, by decide⟩ : Fin 1003)) qp921_0 = true := by decide +kernel

theorem cl921_h : ((closed (⟨921, by decide⟩ : Fin 1003)).ok (closedMin (⟨921, by decide⟩ : Fin 1003)) && chainF ((closed (⟨921, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp921.map (fun x => (x.lo, x.hi))) ((closed (⟨921, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp922_0_ok : ClosedPF.check raw (closed (⟨922, by decide⟩ : Fin 1003)) qp922_0 = true := by decide +kernel

theorem cl922_h : ((closed (⟨922, by decide⟩ : Fin 1003)).ok (closedMin (⟨922, by decide⟩ : Fin 1003)) && chainF ((closed (⟨922, by decide⟩ : Fin 1003)).xs.headD FQ.zero) (qp922.map (fun x => (x.lo, x.hi))) ((closed (⟨922, by decide⟩ : Fin 1003)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem qp923_0_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_0 = true := by decide +kernel

theorem qp923_1_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_1 = true := by decide +kernel

theorem qp923_2_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_2 = true := by decide +kernel

theorem qp923_3_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_3 = true := by decide +kernel

theorem qp923_4_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_4 = true := by decide +kernel

theorem qp923_5_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_5 = true := by decide +kernel

theorem qp923_6_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_6 = true := by decide +kernel

theorem qp923_7_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_7 = true := by decide +kernel

theorem qp923_8_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_8 = true := by decide +kernel

theorem qp923_9_ok : ClosedPF.check raw (closed (⟨923, by decide⟩ : Fin 1003)) qp923_9 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
