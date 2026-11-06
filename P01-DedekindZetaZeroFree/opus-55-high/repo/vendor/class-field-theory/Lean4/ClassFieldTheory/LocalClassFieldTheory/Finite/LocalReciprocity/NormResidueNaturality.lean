module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntermediateFieldNormResidueNaturality

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Restriction naturality of the actual abelian local Artin map

The actual algebraic and continuous Artin maps commute with restriction
between finite abelian intermediate fields of the fixed separable closure.
-/


namespace LocalClassFieldTheory

open LocalFieldTheory
open RamificationTheory

variable (K : Type) [Field K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Finite Artin homomorphisms commute with restriction along a
tower of finite abelian intermediate fields. -/
theorem abelianLocalArtinMonoidHom_restrict
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] :
    (intermediateFieldRestrictNormalHom E F hEF).comp
        (abelianLocalArtinMonoidHom K F) =
      abelianLocalArtinMonoidHom K E := by
  apply MonoidHom.ext
  intro a
  exact localArtinAutomorphism_restrict K E F hEF a
