module

public import ImprovedExponents.HostMid.Time
public import ThreeSumApsp.Lang.Lib.Copy

@[expose] public section

/-!
# The variant host: the program, assembled

The common procedures used by the all-edges host, assembled behind the solver.
-/

namespace ImprovedExponents.HostMid

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-- Common callees, starting at `o`. -/
def et17Procs' (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [sqrtBody,
    scanBody,
    primesBody ν.ch.pSqrt ν.ch.pSieve,
    bitLenBody,
    dblTableBody,
    residBody,
    residuesBody ν.pResid,
    powTableBody, Trace.Grid.code Trace.mixCell, Trace.Kernel.body ν.ch.cp.mix ν.ch.cp.kernel,
    Trace.Grid.code Trace.maskCell, Trace.Pair.body ν.ch.cp.mask ν.ch.cp.kernel,
    Trace.Sum.body ν.ch.cp.pair, fillBody, Trace.Sum.body ν.ch.cp.inner,
    countPrimeBody ν.ch.cp,
    choosePrimeBody ν.ch,
    queryCapNatBody,
    ceilDivBody,
    classesBody,
    chunksBody,
    writeXBody,
    writeYBody,
    sieveBody]

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Host/Program.lean
/-- **The context of the top procedure**, in the assembled program of the variant with anything
appended to it. -/
theorem et17Ctx_assembled' (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    Et17Ctx P₀ (et17Procs' pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length) Tn need Dfun
      Gfun tD tG wD wG := by
  -- Procedure number `i` of the list.
  have L : ∀ {i } {body }, (et17Procs' pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (et17Procs' pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  constructor <;> first | exact hpos | apply hD | apply hG | apply L rfl |
    repeat' first | exact hsol | exact L rfl | exact L (i := 0) rfl | constructor

end ImprovedExponents.HostMid
