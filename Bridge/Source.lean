import RamseyCurrent.CurrentSourceGeometry
import Bridge.Data

/-! `DiagRamsey.luWangSource = RamseyCurrent.CurrentSourceGeometry.F` on `[0,1]`.

On each knot interval the project's Hermite cubic interpolates the values and slopes of
Lu--Wang's cubic piece at both endpoints (`endpoint_values`, `endpoint_derivatives`, kernel-checked
by Lu--Wang), so by uniqueness of cubic Hermite interpolation it *is* that piece. -/

set_option maxRecDepth 100000

namespace LuWangBridge

open Set DiagRamsey RamseyRefinement RamseyRefinement.ShapeCertificate RamseyCurrent
open RamseyCurrent.CurrentSourceGeometry (rationalData)

theorem hermite_cubic (a b t c0 c1 c2 c3 : ℝ) (hab : a ≠ b) :
    hermiteCubic a b (c0 + c1*a + c2*a^2 + c3*a^3) (c0 + c1*b + c2*b^2 + c3*b^3)
      (c1 + 2*c2*a + 3*c3*a^2) (c1 + 2*c2*b + 3*c3*b^2) t = c0 + c1*t + c2*t^2 + c3*t^3 := by
  have h : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [hermiteCubic]
  field_simp
  ring

/-- Counting the elements of `range n` satisfying a downward-closed predicate. -/
theorem filter_length_spec (P : ℕ → Prop) [DecidablePred P] (N : ℕ)
    (hP : ∀ i j, i ≤ j → j < N → P j → P i) : ∀ n ≤ N,
    ((∀ j < n, P j) ∧ ((List.range n).filter (fun j => P j)).length = n) ∨
    ∃ m < n, ((List.range n).filter (fun j => P j)).length = m ∧ (∀ j < m, P j) ∧ ¬ P m := by
  intro n
  induction n with
  | zero => intro _; left; simp
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.filter_append, List.length_append]
    rcases ih (by omega) with ⟨hall, hlen⟩ | ⟨m, hm, hlen, hall, hnot⟩
    · by_cases hPn : P n
      · left
        refine ⟨fun j hj => ?_, by simp [hlen, hPn]⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact hall j h
        · exact hPn
      · right; exact ⟨n, Nat.lt_succ_self n, by simp [hlen, hPn], hall, hPn⟩
    · right
      have hPn : ¬ P n := fun h => hnot (hP m n hm.le (by omega) h)
      exact ⟨m, Nat.lt_succ_of_lt hm, by simp [hlen, hPn], hall, hnot⟩

theorem knot_lt {i j : ℕ} (hij : i < j) (hj : j < 2280) : luWangKnot i < luWangKnot j := by
  rw [knot_eq i (by omega), knot_eq j hj]
  exact_mod_cast (RationalSourceData.knot_strict rationalData
    CurrentSourceGeometry.exact_checked) (show (⟨i, by omega⟩ : Fin 2280) < (⟨j, hj⟩ : Fin 2280) from hij)

theorem knot_zero : luWangKnot 0 = 0 := by
  rw [knot_eq 0 (by norm_num)]; exact_mod_cast CurrentSourceGeometry.first_knot

theorem knot_last : luWangKnot 2279 = 1 := by
  rw [knot_eq 2279 (by norm_num)]; exact_mod_cast CurrentSourceGeometry.last_knot

theorem piece_spec {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    luWangPiece t < 2279 ∧ luWangKnot (luWangPiece t) ≤ t ∧ t ≤ luWangKnot (luWangPiece t + 1) := by
  classical
  let P : ℕ → Prop := fun j => luWangKnot (j + 1) < t
  have hP : ∀ i j, i ≤ j → j < 2278 → P j → P i := by
    intro i j hij hj h
    rcases hij.lt_or_eq with hij | rfl
    · exact (knot_lt (by omega : i + 1 < j + 1) (by omega)).trans h
    · exact h
  have hp : luWangPiece t = ((List.range 2278).filter (fun j => P j)).length := by
    unfold luWangPiece; congr
  rw [hp]
  rcases filter_length_spec P 2278 hP 2278 le_rfl with ⟨hall, hlen⟩ | ⟨m, hm, hlen, hall, hnot⟩
  · rw [hlen]
    exact ⟨by norm_num, (hall 2277 (by norm_num)).le, by rw [knot_last]; exact ht.2⟩
  · rw [hlen]
    refine ⟨by omega, ?_, not_lt.mp hnot⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [knot_zero]; exact ht.1
    · have := hall (m - 1) (by omega)
      simp only [P, Nat.sub_add_cancel hm0] at this
      exact this.le

theorem horner4_eval (c0 c1 c2 c3 : ℚ) (x : ℝ) :
    (hornerPoly [c0, c1, c2, c3]).eval x = (c0 : ℝ) + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 := by
  simp [hornerPoly]; ring

theorem horner4_deriv (c0 c1 c2 c3 : ℚ) (x : ℝ) :
    (hornerPoly [c0, c1, c2, c3]).derivative.eval x = (c1 : ℝ) + 2 * c2 * x + 3 * c3 * x ^ 2 := by
  simp [hornerPoly]; ring

theorem correction_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin 2279,
      t ∈ Icc (rationalData.knot i.castSucc : ℝ) (rationalData.knot i.succ : ℝ) ∧
      luWangCorrection t = (hornerPoly (rationalData.coefficients i)).eval t := by
  obtain ⟨hp, hlo, hhi⟩ := piece_spec ht
  set p := luWangPiece t with hpdef
  refine ⟨⟨p, hp⟩, ?_, ?_⟩
  · rw [knot_eq p (by omega)] at hlo
    rw [knot_eq (p + 1) (by omega)] at hhi
    exact ⟨hlo, hhi⟩
  · have hv := RationalSourceData.endpoint_values rationalData
      CurrentSourceGeometry.exact_checked ⟨p, hp⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hv
    have hlen := coefficients_length ⟨p, hp⟩
    have hne : (rationalData.knot ⟨p, by omega⟩ : ℝ) ≠ (rationalData.knot ⟨p + 1, by omega⟩ : ℝ) := by
      rw [← knot_eq p (by omega), ← knot_eq (p + 1) (by omega)]
      exact (knot_lt (Nat.lt_succ_self p) (by omega)).ne
    simp only [luWangCorrection, ← hpdef]
    rw [knot_eq p (by omega), knot_eq (p + 1) (by omega), value_eq p (by omega),
      value_eq (p + 1) (by omega), deriv_eq p (by omega), deriv_eq (p + 1) (by omega)]
    revert hv
    generalize rationalData.coefficients ⟨p, hp⟩ = cs at hlen ⊢
    match cs, hlen with
    | [c0, c1, c2, c3], _ =>
      rintro ⟨h1, h2, h3, h4⟩
      rw [← h1, ← h2, ← h3, ← h4]
      simp only [horner4_eval, horner4_deriv]
      exact hermite_cubic _ _ _ _ _ _ _ hne

theorem source_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    luWangSource t = CurrentSourceGeometry.F t := by
  obtain ⟨i, hi, hc⟩ := correction_eq ht
  rw [CurrentSourceGeometry.F_piece hi, luWangSource, hc]
  simp only [profile, correction, RamseyLean.entropy]

theorem source_eqOn : EqOn luWangSource CurrentSourceGeometry.F (Icc (0 : ℝ) 1) :=
  fun _ ht => source_eq ht

end LuWangBridge
