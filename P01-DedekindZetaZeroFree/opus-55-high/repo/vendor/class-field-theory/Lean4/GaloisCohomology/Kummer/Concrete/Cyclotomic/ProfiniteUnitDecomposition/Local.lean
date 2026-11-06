module

public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Compiled local stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open LocalFieldTheory.Padic

/-- The product of the local finite/free decompositions, compiled separately
from the global coordinate-reassembly stages. -/
def localDecomposition :
    ((p : Nat.Primes) →
      padicUnitFiniteFactor p.1 × Multiplicative ℤ_[p.1]) ≃ₜ*
    ((p : Nat.Primes) → ℤ_[p.1]ˣ) :=
  continuousMulEquivPiCongr fun p =>
    padicUnitDecomposition p.1
