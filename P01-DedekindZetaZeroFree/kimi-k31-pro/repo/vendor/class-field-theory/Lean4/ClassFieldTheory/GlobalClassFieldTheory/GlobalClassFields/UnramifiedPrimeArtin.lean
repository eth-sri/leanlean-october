module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Prime Artin elements at unramified finite places

For a finite abelian extension of number fields, the global Artin image
of the normalized one-place prime idèle is the chosen local Artin image
of an element of normalized order one.

At a chosen unramified finite place, integral units lie in the local norm
group.  Consequently the local Artin symbol depends only on normalized
order, the prime Artin element generates the full decomposition group,
and its order is the local degree.  This gives the genuine
decomposition law: the prime Artin element is trivial exactly when the
place splits completely.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The actual global Artin element of the normalized one-place prime
idèle at a finite place. -/
def finitePlacePrimeArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    L ≃ₐ[K] L :=
  Reciprocity.globalArtinMonoidHom
    (K := K) (L := L) (finitePrimeIdele v)

/-- The global prime Artin element is the chosen local Artin image of
the normalized order-one local element. -/
@[simp]
theorem finitePlacePrimeArtin_eq_chosenFinitePlaceArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    finitePlacePrimeArtin (K := K) (L := L) v =
      Reciprocity.chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) := by
  rw [finitePlacePrimeArtin, finitePrimeIdele,
    Reciprocity.globalArtinMonoidHom_finitePlaceIdele]











end GlobalClassFields
end GlobalClassFieldTheory

end
