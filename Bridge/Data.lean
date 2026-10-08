import RamseyCurrent.CurrentSourceGeometryData
import Bridge.ParseRat
import Bridge.DataKnots
import Bridge.DataValues
import Bridge.DataDerivs

/-! The project's string data (`luWangKnotData`, `luWangValueData`, `luWangDerivData`) is, entry by entry,
the decimal rendering of Lu--Wang's rational data `RamseyCurrent.CurrentSourceData.{knots,values,derivatives}`.
The three list equalities are checked by the kernel. -/

set_option maxRecDepth 100000

namespace LuWangBridge

open DiagRamsey RamseyCurrent.CurrentSourceGeometry

theorem knotData_eq : luWangKnotData = RamseyCurrent.CurrentSourceData.knots.map fmt := by
  rw [← fmtS_eq_fmt]; exact knotsData_eqS

theorem valueData_eq : luWangValueData = RamseyCurrent.CurrentSourceData.values.map fmt := by
  rw [← fmtS_eq_fmt]; exact valuesData_eqS

theorem derivData_eq : luWangDerivData = RamseyCurrent.CurrentSourceData.derivatives.map fmt := by
  rw [← fmtS_eq_fmt]; exact derivativesData_eqS

set_option maxHeartbeats 0 in
theorem pieces_lengths :
    RamseyCurrent.CurrentSourceData.pieces.map (fun p => p.coefficients.length) =
      List.replicate 2279 4 := by
  kernel_rfl

theorem coefficients_length : ∀ i : Fin 2279, (rationalData.coefficients i).length = 4 := by
  intro i
  have hlen : RamseyCurrent.CurrentSourceData.pieces.length = 2279 := by
    simpa using congrArg List.length pieces_lengths
  have hi : i.val < RamseyCurrent.CurrentSourceData.pieces.length := by rw [hlen]; exact i.isLt
  have h := congrArg (fun l => l[i.val]?) pieces_lengths
  simp only [List.getElem?_map, List.getElem?_replicate, i.isLt, if_true,
    List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at h
  simp only [rationalData, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h

theorem fmt_zero : fmt 0 = "0/1" := by decide +kernel

theorem getD_map_fmt (L : List ℚ) (i : ℕ) : (L.map fmt).getD i (fmt 0) = fmt (L.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> rfl

theorem datum_map (L : List ℚ) (i : ℕ) : luWangDatum (L.map fmt) i = ((L.getD i 0 : ℚ) : ℝ) := by
  rw [luWangDatum, ← fmt_zero, getD_map_fmt, fmt, parseRat_fmt]

theorem getElem!_eq_getD (L : List ℚ) (i : ℕ) : L[i]! = L.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, getElem!_def]
  cases L[i]? <;> rfl

theorem knot_eq (i : ℕ) (h : i < 2280) : luWangKnot i = (rationalData.knot ⟨i, h⟩ : ℝ) := by
  rw [luWangKnot, knotData_eq, datum_map]
  simp only [rationalData, getElem!_eq_getD]

theorem value_eq (i : ℕ) (h : i < 2280) :
    luWangDatum luWangValueData i = (rationalData.value ⟨i, h⟩ : ℝ) := by
  rw [valueData_eq, datum_map]
  simp only [rationalData, getElem!_eq_getD]

theorem deriv_eq (i : ℕ) (h : i < 2280) :
    luWangDatum luWangDerivData i = (rationalData.derivative ⟨i, h⟩ : ℝ) := by
  rw [derivData_eq, datum_map]
  simp only [rationalData, getElem!_eq_getD]

end LuWangBridge
