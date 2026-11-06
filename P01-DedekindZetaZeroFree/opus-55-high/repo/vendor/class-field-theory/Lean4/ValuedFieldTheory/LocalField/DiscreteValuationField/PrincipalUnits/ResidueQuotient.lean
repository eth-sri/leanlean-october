module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# The first principal-unit quotient

Identifies valuation-ring units modulo first principal units with residue-field units and
records compatibility with valuation-preserving automorphisms.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The kernel of the residue map on valuation-ring units is the first
principal-unit subgroup. -/
theorem residueUnitHom_ker_eq :
    (higherPrincipalUnitGroup.residueUnitHom F).ker =
      higherPrincipalUnitGroup F 1 := by
  ext u
  rw [MonoidHom.mem_ker, higherPrincipalUnitGroup.residueUnitHom_eq_one_iff]

/-- The first-isomorphism form of the residue map on valuation-ring units:
`O_K^* / U_K^1` is the unit group of the residue field. -/
def unitsModOneEquivResidueFieldUnits :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F 1 ≃* F.residueFieldˣ :=
  QuotientGroup.liftEquiv
    (higherPrincipalUnitGroup F 1)
    (by
      simpa [higherPrincipalUnitGroup.residueUnitHom] using
        (IsLocalRing.surjective_units_map_of_local_ringHom
          F.residueMap F.residue_surjective
          (inferInstanceAs (IsLocalHom F.residueMap))))
    (higherPrincipalUnitGroup.residueUnitHom_ker_eq F).symm
