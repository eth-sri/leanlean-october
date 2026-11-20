module

public import Chazelle.Core.GranTop
public import Chazelle.Core.NFBuildMain

/-!
# WP-F: granularity enforcement, unconditionally

`Gran.granularize'` needs `BuildNFSpec`, proved as `buildNF` (WP-C).
-/

namespace Chazelle.Core

public section

/-- **WP-F: granularity enforcement** (§3.3), unconditionally. -/
theorem granularize : GranularizeSpec := Gran.granularize' buildNF

end

end Chazelle.Core
