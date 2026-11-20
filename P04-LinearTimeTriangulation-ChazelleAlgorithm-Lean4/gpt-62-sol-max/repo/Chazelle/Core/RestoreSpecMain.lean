module

public import Chazelle.Core.RestoreDrvMain

/-!
# WP-E: `RestoreSpec` from the splitting step

`restoreSpec_of_find : BuildNFSpec → Restore.FindSpec → RestoreSpec`: the restoration driver
(`Restore.restoreSpecLocal_of_find`), for memory contexts with a local capacity
(`MemCtx.CapLocal`, finding E4, now a hypothesis of `RestoreSpec`).
-/

namespace Chazelle.Core

@[expose] public section

/-- **WP-E: restoring conformality** (Lemmas 3.3, 3.4 and the driver), from the construction of
normal forms and the splitting step of Lemma 3.2. -/
theorem restoreSpec_of_find (hB : BuildNFSpec) (hF : Restore.FindSpec) : RestoreSpec := by
  obtain ⟨mk, κ, cR, h⟩ := Restore.restoreSpecLocal_of_find hB hF
  exact ⟨mk, κ, cR, fun sh cu Bs Bc F G H X Ok hloc hhalf hOkM hBs hBc hsh hcu =>
    h sh cu Bs Bc F G H X Ok hloc hhalf hOkM hBs hBc hsh hcu⟩

end

end Chazelle.Core
