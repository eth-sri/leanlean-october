/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.PoissonCollarValue
import DOZZ.GFFStructure.MarkovAssembly
import Batteries.Tactic.Alias

/-! The statement `DOZZ.exists_exteriorPinned_markov_uniform`,
proved by `DOZZ.Proofs.exists_exteriorPinned_markov_uniform`. -/

public section


universe u

namespace DOZZ

/-- Exterior-pin Markov decomposition with all-order uniform harmonic moments, for the separated
two-insertion joint tail [KRV, Lemma 7.3] (erratum K9, see docs/ERRATA-AND-DEVIATIONS.md). For this
application take `n = 2`, `ρ = 5/4`, `a = 1` and a fixed positive separation margin. The bound
precedes every realization and center choice. Neither the pin scalar nor the exterior field of `X`
is asserted independent. The circle-cutoff conjuncts (with a `σ(Dᵢ) ⊗ Borel`-measurable version
`Dc`) are the form needed for that tail estimate; the test-level conjuncts alone do not reach it. -/
alias exists_exteriorPinned_markov_uniform := DOZZ.Proofs.exists_exteriorPinned_markov_uniform

end DOZZ
