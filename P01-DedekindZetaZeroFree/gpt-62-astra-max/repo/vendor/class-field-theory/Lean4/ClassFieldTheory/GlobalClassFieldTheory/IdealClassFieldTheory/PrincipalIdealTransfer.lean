module

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.AbstractCapitulation
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFixedFieldBaseChange
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FieldSpine
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Representatives
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Compatibility
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.Quotient
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.MembershipTypes
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.ZeroTransport
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFiniteNormTransfer.FiniteNormClass
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerUnramified

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Transfer input for the principal ideal theorem

At the generic level, the Galois correspondence realizes a subgroup
`S ≤ Gal(M / K)` as an intermediate field, while the transfer construction
independently realizes `Gal(M / M^S)` inside `Gal(M / K)`.  Identifying these
subgroups puts the commutator transfer in the form covered by Witt's theorem.
This generic input assumes neither a class-field realization nor a
norm-subgroup equality.

The theorems below specialize that input to the selected actual two-stage
small Hilbert tower and transport it to genuine idèle-class extension and
norm maps.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open GlobalClassFields
open KummerTheory
open LocalClassFieldTheory
open Reciprocity

variable (K : Type) [Field K] [NumberField K]

local instance
    principalIdealTransferIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance
    principalIdealTransferIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

/-- The selected two-stage tower supplies a canonical zero finite-norm class
for every idele class over its base fixed field. -/
@[irreducible]
 noncomputable def
    smallHilbertClassFieldCanonicalFiniteNormClassZeroStatement : Prop :=
  let K₀ :=
    numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let N := smallHilbertTowerSecondSubextension K
  let H := L.field
  let hMH : N.field.toSubgroup ≤ H.toSubgroup := N.below
  let hHK : H.toSubgroup ≤ K₀.field.toSubgroup := L.below
  letI hHMfinite : Finite
      (H.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H N.field hMH) :=
    N.finite
  ∀ c : rationalFiniteNormTransferBaseIdeleClass
      (hKfinite := K₀.finite) K₀.field,
    rationalFiniteNormTransferCanonicalFiniteNormClassZero
      (hKfinite := K₀.finite) (hHLfinite := hHMfinite)
      K₀.field H N.field hHK hMH c

/-- The named proposition underlying the fixed-field-base form of the
two-stage transfer containment.  Keeping the dependent idele maps behind one
opaque boundary prevents every consumer from reconstructing their instance
towers while elaborating a theorem signature. -/
@[irreducible]
noncomputable def smallHilbertClassFieldBaseSecondNormRangeContainment : Prop :=
  (ideleClassExtension
    (smallHilbertClassFieldBase K)
    (smallHilbertClassField K)).range ≤
      smallHilbertClassFieldNormSubgroup
        (K := smallHilbertClassField K)

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
