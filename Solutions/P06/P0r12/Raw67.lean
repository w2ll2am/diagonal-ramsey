import Solutions.P06.P0r12.T
import Solutions.P06.P0r12.D1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DiagRamsey.V5.P06_P0r12

open DiagRamsey.V5

theorem rp206_1_ok : RawF.check ctl A B pd i0 (raw (⟨206, by decide⟩ : Fin 1902)) rp206_1 = true := by decide +kernel

theorem raw206_h : ((raw (⟨206, by decide⟩ : Fin 1902)).ok (rawMin (⟨206, by decide⟩ : Fin 1902)) && chainF ((raw (⟨206, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp206.map (fun x => (x.lo, x.hi))) ((raw (⟨206, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp207_0_ok : RawF.check ctl A B pd i0 (raw (⟨207, by decide⟩ : Fin 1902)) rp207_0 = true := by decide +kernel

theorem rp207_1_ok : RawF.check ctl A B pd i0 (raw (⟨207, by decide⟩ : Fin 1902)) rp207_1 = true := by decide +kernel

theorem rp207_2_ok : RawF.check ctl A B pd i0 (raw (⟨207, by decide⟩ : Fin 1902)) rp207_2 = true := by decide +kernel

theorem rp207_3_ok : RawF.check ctl A B pd i0 (raw (⟨207, by decide⟩ : Fin 1902)) rp207_3 = true := by decide +kernel

theorem rp207_4_ok : RawF.check ctl A B pd i0 (raw (⟨207, by decide⟩ : Fin 1902)) rp207_4 = true := by decide +kernel

theorem raw207_h : ((raw (⟨207, by decide⟩ : Fin 1902)).ok (rawMin (⟨207, by decide⟩ : Fin 1902)) && chainF ((raw (⟨207, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp207.map (fun x => (x.lo, x.hi))) ((raw (⟨207, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp208_0_ok : RawF.check ctl A B pd i0 (raw (⟨208, by decide⟩ : Fin 1902)) rp208_0 = true := by decide +kernel

theorem rp208_1_ok : RawF.check ctl A B pd i0 (raw (⟨208, by decide⟩ : Fin 1902)) rp208_1 = true := by decide +kernel

theorem raw208_h : ((raw (⟨208, by decide⟩ : Fin 1902)).ok (rawMin (⟨208, by decide⟩ : Fin 1902)) && chainF ((raw (⟨208, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp208.map (fun x => (x.lo, x.hi))) ((raw (⟨208, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp209_0_ok : RawF.check ctl A B pd i0 (raw (⟨209, by decide⟩ : Fin 1902)) rp209_0 = true := by decide +kernel

theorem raw209_h : ((raw (⟨209, by decide⟩ : Fin 1902)).ok (rawMin (⟨209, by decide⟩ : Fin 1902)) && chainF ((raw (⟨209, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp209.map (fun x => (x.lo, x.hi))) ((raw (⟨209, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp210_0_ok : RawF.check ctl A B pd i0 (raw (⟨210, by decide⟩ : Fin 1902)) rp210_0 = true := by decide +kernel

theorem raw210_h : ((raw (⟨210, by decide⟩ : Fin 1902)).ok (rawMin (⟨210, by decide⟩ : Fin 1902)) && chainF ((raw (⟨210, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp210.map (fun x => (x.lo, x.hi))) ((raw (⟨210, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp211_0_ok : RawF.check ctl A B pd i0 (raw (⟨211, by decide⟩ : Fin 1902)) rp211_0 = true := by decide +kernel

theorem raw211_h : ((raw (⟨211, by decide⟩ : Fin 1902)).ok (rawMin (⟨211, by decide⟩ : Fin 1902)) && chainF ((raw (⟨211, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp211.map (fun x => (x.lo, x.hi))) ((raw (⟨211, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp212_0_ok : RawF.check ctl A B pd i0 (raw (⟨212, by decide⟩ : Fin 1902)) rp212_0 = true := by decide +kernel

theorem rp212_1_ok : RawF.check ctl A B pd i0 (raw (⟨212, by decide⟩ : Fin 1902)) rp212_1 = true := by decide +kernel

theorem raw212_h : ((raw (⟨212, by decide⟩ : Fin 1902)).ok (rawMin (⟨212, by decide⟩ : Fin 1902)) && chainF ((raw (⟨212, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp212.map (fun x => (x.lo, x.hi))) ((raw (⟨212, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp213_0_ok : RawF.check ctl A B pd i0 (raw (⟨213, by decide⟩ : Fin 1902)) rp213_0 = true := by decide +kernel

theorem raw213_h : ((raw (⟨213, by decide⟩ : Fin 1902)).ok (rawMin (⟨213, by decide⟩ : Fin 1902)) && chainF ((raw (⟨213, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp213.map (fun x => (x.lo, x.hi))) ((raw (⟨213, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp214_0_ok : RawF.check ctl A B pd i0 (raw (⟨214, by decide⟩ : Fin 1902)) rp214_0 = true := by decide +kernel

theorem rp214_1_ok : RawF.check ctl A B pd i0 (raw (⟨214, by decide⟩ : Fin 1902)) rp214_1 = true := by decide +kernel

theorem raw214_h : ((raw (⟨214, by decide⟩ : Fin 1902)).ok (rawMin (⟨214, by decide⟩ : Fin 1902)) && chainF ((raw (⟨214, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp214.map (fun x => (x.lo, x.hi))) ((raw (⟨214, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp215_0_ok : RawF.check ctl A B pd i0 (raw (⟨215, by decide⟩ : Fin 1902)) rp215_0 = true := by decide +kernel

theorem rp215_1_ok : RawF.check ctl A B pd i0 (raw (⟨215, by decide⟩ : Fin 1902)) rp215_1 = true := by decide +kernel

theorem raw215_h : ((raw (⟨215, by decide⟩ : Fin 1902)).ok (rawMin (⟨215, by decide⟩ : Fin 1902)) && chainF ((raw (⟨215, by decide⟩ : Fin 1902)).xs.headD FQ.zero) (rp215.map (fun x => (x.lo, x.hi))) ((raw (⟨215, by decide⟩ : Fin 1902)).xs.getLastD FQ.zero)) = true := by decide +kernel

theorem rp216_0_ok : RawF.check ctl A B pd i0 (raw (⟨216, by decide⟩ : Fin 1902)) rp216_0 = true := by decide +kernel

theorem rp216_1_ok : RawF.check ctl A B pd i0 (raw (⟨216, by decide⟩ : Fin 1902)) rp216_1 = true := by decide +kernel

end DiagRamsey.V5.P06_P0r12
