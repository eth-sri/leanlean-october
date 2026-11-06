module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Uniqueness of arithmetic Frobenius from its residue action

For an unramified finite abelian extension, the arithmetic `q`-power action
on residues determines the Galois automorphism uniquely.  The canonical local
Artin map takes an inverse uniformizer to this automorphism.
-/

open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

 noncomputable instance : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
  LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L

 noncomputable instance : Module.Finite 𝒪[K] 𝒪[L] :=
  LocalFieldTheory.localCompleteDVF_integerRing_moduleFinite K L



end ClassFieldTheory

end
