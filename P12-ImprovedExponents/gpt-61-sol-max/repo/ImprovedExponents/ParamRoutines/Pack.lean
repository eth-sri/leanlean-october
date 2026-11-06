module

public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.NeedPolynomial
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Program
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Total

@[expose] public section

/-!
# Theorem 17 for programs, from any pair of parameter routines

Upstream's host of Theorem 17 (`et17`) takes the procedures that compute `D` from `n` and `g` from
`D` as parameters, and upstream instantiates it with two fixed choices, by an assembly that is
private (`ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean`).  This file states that
assembly once, for arbitrary routines.

* `ParamPack D g` bundles everything that is specific to the two routines: the list of procedures,
  the functions they compute, their times and word bounds, and the facts about them.  Nothing in
  it mentions a host.  The times are bounded by the monomial `n² (√D)²` of upstream's scale
  (`StepsMon _ 2 2 0`), which is the largest that `Scale.SoftO.withinBuild` accepts; so they are
  within the bound of Theorem 17 (`ParamPack.stepsD_budget`, `ParamPack.stepsG_budget`), and
  within every other bound that contains `n² D`.
* `ParamPack.host_of_solves` is the part of the assembly that does not depend on which host is
  used: it places the routines behind the solver's program and hands them to a host that is given
  as a hypothesis of the shape of `et17_solves`.
* `claim17_of_paramProcs` is the instance for upstream's host.  Its proof names the four
  host-specific theorems (`et17_solves`, `hostNeed_poly`, `obeysBound17_hostTime`,
  `claim17_of_host`) and the time and the need of the host (`hostTime`, `hostNeed`), and nothing
  else.  A variant of the host with theorems of the same shapes is instantiated by the same term
  with these six names replaced.
-/

namespace ImprovedExponents.ParamRoutines

open Light Light.Sec3

/-- The procedure number `i` of a list `L` that is placed behind a program `Q` stands at the place
`Q.length + i` of every program that continues `Q ++ L`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/ClaimAtParameters.lean
-- (`paramProcs_get`, private there; here for an arbitrary list)
theorem getElem?_behind (Q L R : Program) {i} {body} (h : L[i]? = some body) :
    (Q ++ L ++ R)[Q.length + i]? = some body := by
  grind

/-- **The routine-specific part of Theorem 17 for programs**: two parameter routines for the
parameters `D n` and `g n` of the claim, with everything that a host of Theorem 17 needs to know
about them. -/
structure ParamPack (D g : ℕ → ℕ) where
  /-- The procedures to place behind a program of length `o`, as a function of `o`. -/
  procs : ℕ → Program
  /-- The place of the routine for `D` in `procs`. -/
  iD : ℕ
  /-- The place of the routine for `g` in `procs`. -/
  iG : ℕ
  /-- What the routine for `D` computes from `n`. -/
  (Dfun Gfun tD tG wD wG : ℕ → ℕ)
  /-- The routine for `D` is a parameter procedure in every program that contains `procs`. -/
  procD : ParamFamily procs iD Dfun tD wD
  /-- The routine for `g` is a parameter procedure in every program that contains `procs`. -/
  procG : ParamFamily procs iG Gfun tG wG
  /-- `D ≥ 1`. -/
  D_pos : ∀ n, 1 ≤ n → 1 ≤ Dfun n
  /-- `D` is polynomially bounded. -/
  polyD : PolyBounded fun n _ => Dfun n
  /-- `g` is polynomially bounded. -/
  polyG : PolyBounded fun n _ => Gfun (Dfun n)
  /-- The numbers of the routine for `D` are polynomially bounded. -/
  polyWD : PolyBounded fun n _ => wD n
  /-- The numbers of the routine for `g` are polynomially bounded. -/
  polyWG : PolyBounded fun n _ => wG (Dfun n)
  /-- The routine for `D` computes the parameter `D` of the claim. -/
  D_eq : ∀ n, Dfun n = D n
  /-- The routine for `g` computes the parameter `g` of the claim. -/
  G_eq : ∀ n, 1 ≤ n → Gfun (D n) = g n
  /-- The routine for `D` takes `O(n² D)` steps, uniformly in all parameters of Theorem 17 (`θ.D`
  is any `D` with `16 ≤ D ≤ n`, not the value of the routine). -/
  stepsD : StepsMon (fun θ => tD θ.n) 2 2 0
  /-- The routine for `g` takes `O(n² D)` steps, uniformly in all parameters of Theorem 17. -/
  stepsG : StepsMon (fun θ => tG θ.D) 2 2 0

namespace ParamPack

variable {D g : ℕ → ℕ} (pk : ParamPack D g)

/-- The routine for `D` runs within the bound of Theorem 17 (within the term `n² D g`). -/
def stepsD_budget := pk.stepsD.withinBuild

/-- The routine for `g` runs within the bound of Theorem 17 (within the term `n² D g`). -/
def stepsG_budget := pk.stepsG.withinBuild

end ParamPack

end ImprovedExponents.ParamRoutines
