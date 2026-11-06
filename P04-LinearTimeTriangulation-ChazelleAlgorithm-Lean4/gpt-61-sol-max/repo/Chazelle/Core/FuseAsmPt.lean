module

public import Chazelle.Core.FuseAsmQuery
public import Chazelle.Core.SweepPrimArr

/-!
# WP-F fusion assembly, part 8: queries at points

A point query (the shared vertex, a top, the cap origin) is placed by `arrivalPos`: it reports a
position of the point whose left sector contains the direction, or that there is none.  In the
first case the position, with the height code of the point when `arrivalPos` returns a vertex
position (`code = 0`), is a valid sweep query at the point (`query_of_arr`); in the second the
direction is not free for `C` (`not_free_of_none`), so the query can be dropped.
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open Chazelle.Chain (sidePt)

/-- **No departure position: the direction is not free.** -/
theorem not_free_of_none (J : Merge.Junction) (hP : J.P.Simple) (i : ℕ) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hz : z ∈ (sideChain J i).set) (hz2 : z.2 ≤ (sideChain J i).top.2)
    (hnone : ∀ p t, ¬ Sweep.Arrival (chainModel (sideChain J i)).W z (-σ) p t) :
    ¬ Merge.FreeAt J.whole z σ := fun hf => by
  obtain ⟨p, t, h⟩ := arrival_of_free J hP i hσ hz hz2 hf
  simp_all

end

end FuseAsm

end Chazelle.Core
