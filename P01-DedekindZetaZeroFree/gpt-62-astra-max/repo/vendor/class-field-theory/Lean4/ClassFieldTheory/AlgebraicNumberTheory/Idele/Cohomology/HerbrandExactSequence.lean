module

public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Index
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The final cardinal step in the idele-class Herbrand calculation

This file isolates the final cardinality argument in the idele-class Herbrand calculation. The
Herbrand quotients of the supported ideles and of the corresponding
principal ideles have a common nonzero local-degree factor.  Cancelling
that factor in the exact-sequence identity gives

`h(G, C_L) = |G|`.

The degree-zero Tate group is the actual idele-class norm quotient, so
its cardinality, and hence the norm index, is at least `|G| = [L : K]`.
-/

open scoped NumberField
open NumberField

noncomputable section

open RelativeIdeleGroup.Cohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

end
