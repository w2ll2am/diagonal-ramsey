import RamseyCurrent.CurrentSourceGeometry
import Bridge.Source

/-! B3: the project's source-concavity statement, verbatim, from Lu--Wang's
`RamseyCurrent.CurrentSourceGeometry.concave_closed`. -/

namespace DiagRamsey

theorem lu_wang_source_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) luWangSource :=
  RamseyCurrent.CurrentSourceGeometry.concave_closed.congr LuWangBridge.source_eqOn.symm

end DiagRamsey
