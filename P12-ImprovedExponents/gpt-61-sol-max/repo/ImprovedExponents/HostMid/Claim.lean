module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ImprovedExponents.HostMid.NeedPolynomial
public import ImprovedExponents.Pipeline.HostBound
public import ThreeSumApsp.Programs.Sec3.Theorem17.Claim

@[expose] public section

/-!
# Theorem 17 with the solver charged at the smaller inner dimension, as a claim about programs

`Claim17Mid M MM D g` is upstream's `Claim.Theorem_17 M MM D g` with one change: the solver of
Lop-AE-SparseTri is charged `T n (midSize (D n) (g n)) ⌊n²/√D⌋` for an instance, not
`T n (D n) ⌊n²/√D⌋`.  The middle part of an instance of the reduction has only
`midSize D g = ⌈⌊√D⌋/g⌉ ⌊√D⌋` vertices, about `D/g`.  All other terms are upstream's.

As upstream's `Claim.lean`, this file reduces the claim, for programs of the light language, to two
facts about a host: it turns solvers into solvers and keeps their need polynomial, and its time
obeys the bound (`ObeysBound17Mid`, `claim17Mid_of_host`).
-/

namespace ImprovedExponents.HostMid

open Light ThreeSumApsp

/-- **Theorem 17 with the inner dimension of the instances made explicit**: upstream's
`Claim.Theorem_17`, except that the instances of Lop-AE-SparseTri have the inner dimension
`midSize (D n) (g n) = ⌈⌊√D⌋/g⌉ ⌊√D⌋` (the number of vertices of the middle part `piece × ℤ_p`)
and the solver is charged accordingly.  The additional time is unchanged. -/
def Claim17Mid M MM D g :=
  HostBound M MM D g fun n => midSize (D n) (g n)

/-- The right-hand side of `Claim17Mid`. -/
noncomputable def bound17Mid MM (D g : ℕ → ℕ) C (T : ℕ → ℕ → ℕ → ℝ) (n : ℕ)
     κ :=
  Light.Sec3.bound17 MM D g C (fun m _ w => T m (midSize (D m) (g m)) w) n κ

/-- The time of a host, as a function `time` of the time of the solver, obeys the bound of
`Claim17Mid` with some constant: whenever `T` bounds the time `Tn` of the solver, `bound17Mid` with
`T` bounds `time Tn`, under the hypotheses of the theorem. -/
def ObeysBound17Mid MM D g time :=
  Light.Sec3.ObeysBound17With D g (bound17Mid MM D g) time

-- adapted from upstream ThreeSumApsp/Programs/Sec3/Theorem17/Claim.lean
/-- **From a host to the claim.**  `time` and `need` are the host's time and need as functions of
those of the solver.  A program has a natural number `U` as the bound on the weights and the claim a
real number `u`; the time for `u` is the largest time for a `U ≤ u`. -/
theorem claim17Mid_of_host {task } MM D g time
    (need : Light.InputNeed → Light.NeedFn)
    (host : ∀ (Q ) (pS ) (Tn ) (r ), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves task (Q ++ R) p' (time Tn) (need r) ∧ PolyNeed (need r))
    (bound : ObeysBound17Mid MM D g time) :
    Claim17Mid { lightModel with exactTriangle := SolvedIn task } MM D g := by
  obtain ⟨C, hC, bound⟩ := bound
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs, hp⟩ := host Q pS Tn r hpoly hsolves
  exact ⟨_, hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

end ImprovedExponents.HostMid
