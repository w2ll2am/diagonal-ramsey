import RamseyCurrent.CurrentSourceData
import Definitions.Def_DiagRamsey_LuWangSource
import Bridge.KernelRfl

set_option maxRecDepth 100000

namespace LuWangBridge

set_option maxHeartbeats 0 in
/-- Checked by the kernel, entry by entry. -/
theorem valuesData_eqS :
    DiagRamsey.luWangValueData = RamseyCurrent.CurrentSourceData.values.map fmtS := by
  kernel_rfl

end LuWangBridge
