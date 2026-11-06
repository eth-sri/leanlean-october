module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction

@[expose] public section

namespace Glennie.Compact.NativeFlatColumnsA

open Glennie.Compact.NativeDictionary Glennie.Compact.FlatBase Glennie.Compact.FlowFamily
  Glennie.Compact.Rank20 Glennie.Compact.Rank20Certificate

set_option maxHeartbeats 0

flat_cols 0 1 2 3 4

end Glennie.Compact.NativeFlatColumnsA
