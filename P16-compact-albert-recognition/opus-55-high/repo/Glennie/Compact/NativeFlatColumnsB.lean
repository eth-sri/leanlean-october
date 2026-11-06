module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction

@[expose] public section

namespace Glennie.Compact.NativeFlatColumnsB

open Glennie.Compact.NativeDictionary Glennie.Compact.FlatBase Glennie.Compact.FlowFamily
  Glennie.Compact.Rank20 Glennie.Compact.Rank20Certificate

set_option maxHeartbeats 0

flat_cols 5 6 7 8 9

end Glennie.Compact.NativeFlatColumnsB
