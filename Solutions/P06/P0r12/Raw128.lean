import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp447_24_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_24 = true := by decide +kernel

theorem rp447_25_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_25 = true := by decide +kernel

theorem rp447_26_ok : RawF.check ctl A B pd i0 (raw (⟨447, by decide⟩ : Fin 1902)) rp447_26 = true := by decide +kernel

theorem raw447_h : ((raw (⟨447, by decide⟩ : Fin 1902)).ok (rawMin (⟨447, by decide⟩ : Fin 1902)) && chainF ((raw (⟨447, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp447.map (fun x => (x.lo, x.hi))) ((raw (⟨447, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp448_0_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_0 = true := by decide +kernel

theorem rp448_1_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_1 = true := by decide +kernel

theorem rp448_2_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_2 = true := by decide +kernel

theorem rp448_3_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_3 = true := by decide +kernel

theorem rp448_4_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_4 = true := by decide +kernel

theorem rp448_5_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_5 = true := by decide +kernel

theorem rp448_6_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_6 = true := by decide +kernel

theorem rp448_7_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_7 = true := by decide +kernel

theorem rp448_8_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_8 = true := by decide +kernel

theorem rp448_9_ok : RawF.check ctl A B pd i0 (raw (⟨448, by decide⟩ : Fin 1902)) rp448_9 = true := by decide +kernel

theorem raw448_h : ((raw (⟨448, by decide⟩ : Fin 1902)).ok (rawMin (⟨448, by decide⟩ : Fin 1902)) && chainF ((raw (⟨448, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp448.map (fun x => (x.lo, x.hi))) ((raw (⟨448, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp449_0_ok : RawF.check ctl A B pd i0 (raw (⟨449, by decide⟩ : Fin 1902)) rp449_0 = true := by decide +kernel

theorem rp449_1_ok : RawF.check ctl A B pd i0 (raw (⟨449, by decide⟩ : Fin 1902)) rp449_1 = true := by decide +kernel

theorem rp449_2_ok : RawF.check ctl A B pd i0 (raw (⟨449, by decide⟩ : Fin 1902)) rp449_2 = true := by decide +kernel

theorem rp449_3_ok : RawF.check ctl A B pd i0 (raw (⟨449, by decide⟩ : Fin 1902)) rp449_3 = true := by decide +kernel

theorem rp449_4_ok : RawF.check ctl A B pd i0 (raw (⟨449, by decide⟩ : Fin 1902)) rp449_4 = true := by decide +kernel

theorem rp449_5_ok : RawF.check ctl A B pd i0 (raw (⟨449, by decide⟩ : Fin 1902)) rp449_5 = true := by decide +kernel

theorem raw449_h : ((raw (⟨449, by decide⟩ : Fin 1902)).ok (rawMin (⟨449, by decide⟩ : Fin 1902)) && chainF ((raw (⟨449, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp449.map (fun x => (x.lo, x.hi))) ((raw (⟨449, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp450_0_ok : RawF.check ctl A B pd i0 (raw (⟨450, by decide⟩ : Fin 1902)) rp450_0 = true := by decide +kernel

theorem rp450_1_ok : RawF.check ctl A B pd i0 (raw (⟨450, by decide⟩ : Fin 1902)) rp450_1 = true := by decide +kernel

theorem rp450_2_ok : RawF.check ctl A B pd i0 (raw (⟨450, by decide⟩ : Fin 1902)) rp450_2 = true := by decide +kernel

theorem rp450_3_ok : RawF.check ctl A B pd i0 (raw (⟨450, by decide⟩ : Fin 1902)) rp450_3 = true := by decide +kernel

theorem rp450_4_ok : RawF.check ctl A B pd i0 (raw (⟨450, by decide⟩ : Fin 1902)) rp450_4 = true := by decide +kernel

theorem rp450_5_ok : RawF.check ctl A B pd i0 (raw (⟨450, by decide⟩ : Fin 1902)) rp450_5 = true := by decide +kernel

theorem rp450_6_ok : RawF.check ctl A B pd i0 (raw (⟨450, by decide⟩ : Fin 1902)) rp450_6 = true := by decide +kernel

theorem rp450_7_ok : RawF.check ctl A B pd i0 (raw (⟨450, by decide⟩ : Fin 1902)) rp450_7 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
