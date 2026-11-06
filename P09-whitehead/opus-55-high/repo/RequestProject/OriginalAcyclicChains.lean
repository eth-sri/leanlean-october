import RequestProject.ClassicalCWCanonicalPresentation
import RequestProject.AcyclicPresentationOriginalChains


/-! Original-cell-preserving chains for every acyclic connected CW
two-complex. The finite theorem is precisely the finite acyclic clause
of Whitehead.MainClaim. The original CW model, matrix condition, and
initial comparison are all supplied by constructions. This source has
not yet undergone the final Lean verification. -/

noncomputable section
open scoped Classical

namespace Whitehead
open FiniteChains FiniteChains.ClassicalCW FiniteChains.RelativeNormalForm

theorem hasFiniteChain_of_acyclic K (hfinite : FiniteCells K)
    (hK : Acyclic K) n (hn : 1 ≤ n) : HasChain K n true := by
  letI := canonicalGen_finite K hfinite
  letI := canonicalRel_finite K hfinite
  cases n with
  | zero => omega
  | succ n =>
      exact actual_hasOriginalFiniteChain_of_acyclic _ K hfinite hK
        _ (originalClassicalPresWordDiskEquiv K).symm n
