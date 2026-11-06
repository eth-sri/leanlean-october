module

public import Mathlib

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Principal ideles and their Galois module structure

This module exposes the diagonal embedding and idele class group, identifies
field units with principal relative ideles, and transports low-degree Tate
cohomology across that identification.
-/

noncomputable section

open RelativeIdeleGroup.Cohomology


open LocalClassFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The field-unit group is multiplicatively equivalent to the actual
subgroup of principal relative ideles. -/
noncomputable def fieldUnitsEquivPrincipalIdeles  :=
  MulEquiv.ofBijective
    (RelativeIdeleGroup.principalIdele K L).rangeRestrict
    ⟨fun _ _ h ↦
        RelativeIdeleGroup.principalIdele_injective K L
          (congrArg Subtype.val h),
      (RelativeIdeleGroup.principalIdele K L).rangeRestrict_surjective⟩

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem fieldUnitsEquivPrincipalIdeles_coe
    (x : Lˣ) :
    ((fieldUnitsEquivPrincipalIdeles K L x) :
      RelativeIdeleGroup K L) =
        RelativeIdeleGroup.principalIdele K L x :=
  rfl































































































































































end
