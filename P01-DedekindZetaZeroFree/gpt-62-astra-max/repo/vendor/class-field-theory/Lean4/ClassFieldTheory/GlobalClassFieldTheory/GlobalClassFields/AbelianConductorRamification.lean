module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianNormConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Ramification support of abelian narrow finite norm conductors

For a finite abelian extension, the modulus constructed from the actual
local norm groups is zero exactly when every chosen finite completion is
unramified.  Its support therefore gives the exact chosen-completion
ramification locus, while the minimal narrow finite conductor has support
contained in that locus.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Every prime in the minimal narrow finite norm conductor is ramified
in the chosen completed extension above that prime. -/
theorem
    mem_ideleClassNorm_narrowFiniteConductor_support_imp_chosenFinitePlace_ramified
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∈ (ideleClassNormNarrowFiniteConductor
        (K := K) (L := L)).support) :
    ¬ _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v := by
  exact
    (mem_ideleClassNormDefiningModulus_support_iff_not_chosenFinitePlaceIsUnramified
        v).1 (ideleClassNorm_narrowFiniteConductor_support_subset_normDefiningModulus_support
        hv)

end GlobalClassFields
end GlobalClassFieldTheory

end
