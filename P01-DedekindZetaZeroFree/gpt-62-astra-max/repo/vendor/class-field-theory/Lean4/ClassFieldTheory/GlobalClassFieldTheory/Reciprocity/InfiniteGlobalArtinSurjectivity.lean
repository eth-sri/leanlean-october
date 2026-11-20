module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Surjectivity of the infinite global Artin homomorphism

The absolute idele norm is split, up to inversion, by an idele supported at
one infinite place.  Its local component is positive, so every finite global
Artin homomorphism, and hence the infinite global Artin homomorphism, kills
it.  Multiplication by this section therefore replaces any idele by a
norm-one idele without changing its Artin symbol.
-/

open scoped Classical IsMulCommutative NNReal NumberField Topology
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K : Type} [Field K] [NumberField K]

end Reciprocity
end GlobalClassFieldTheory

end
