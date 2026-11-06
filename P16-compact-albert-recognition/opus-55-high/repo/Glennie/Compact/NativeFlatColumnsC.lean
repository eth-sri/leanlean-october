module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction

@[expose] public section

namespace Glennie.Compact.NativeFlatColumnsC

open Glennie.Compact.NativeDictionary Glennie.Compact.FlatBase Glennie.Compact.FlowFamily
  Glennie.Compact.Rank20 Glennie.Compact.Rank20Certificate

set_option maxHeartbeats 0

flat_cols 10 11 12 13 14

end Glennie.Compact.NativeFlatColumnsC
