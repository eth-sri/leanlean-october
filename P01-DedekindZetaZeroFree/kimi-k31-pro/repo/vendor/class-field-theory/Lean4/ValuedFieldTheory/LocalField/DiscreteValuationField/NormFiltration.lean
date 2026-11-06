module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Norm compatibility with unit filtrations

A compatibility hypothesis for a norm and two unit filtrations immediately
produces homomorphisms on every filtration level.
-/

noncomputable section

universe u v

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)
variable (UG : AntitoneSubgroupFiltration G) (UH : AntitoneSubgroupFiltration H)
variable (targetLevel : ℕ → ℕ)

/-- A compatibility hypothesis for the norm and two filtrations. -/
abbrev MapsFiltrationLevels : Prop :=
  ∀ n {x : H}, x ∈ UH.principalUnitSubgroup n →
    N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n)

/-- The norm map restricted to a filtration level. -/
def mapLevelOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ) :
    UH.principalUnitSubgroup n →* UG.principalUnitSubgroup (targetLevel n) where
  toFun x := ⟨N.toHom x.1, hN n x.2⟩
  map_one' := by
    apply Subtype.ext
    exact N.toHom.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact N.toHom.map_mul x.1 y.1

/--
The defining evaluation formula for `mapLevelOfMapsFiltrationLevels` is
`(mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x : G) = N.toHom x.1`.
-/
@[simp] theorem mapLevelOfMapsFiltrationLevels_apply
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (x : UH.principalUnitSubgroup n) :
    (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x : G) =
      N.toHom x.1 :=
  rfl











/-- A compatible norm descends to the quotient by a filtration level. -/
def quotientMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    H ⧸ UH.principalUnitSubgroup n →*
      G ⧸ UG.principalUnitSubgroup (targetLevel n) :=
  QuotientGroup.map (UH.principalUnitSubgroup n)
    (UG.principalUnitSubgroup (targetLevel n)) N.toHom (by
      intro x hx
      exact hN n hx)

/--
The defining evaluation formula for `quotientMapOfMapsFiltrationLevels` is
`quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n (QuotientGroup.mk x) =
QuotientGroup.mk (N.toHom x)`.
-/
@[simp] theorem quotientMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk x) =
      QuotientGroup.mk (N.toHom x) :=
  rfl

/--
Establishes the identity `quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
(QuotientGroup.mk' (UH.principalUnitSubgroup n) x) = QuotientGroup.mk' (UG.principalUnitSubgroup
(targetLevel n)) (N.toHom x)`.
-/
@[simp] theorem quotientMapOfMapsFiltrationLevels_apply_mk'
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
        (N.toHom x) :=
  rfl

/-- The preimage of the target filtration subgroup under the valued norm. -/
def filtrationPreimageSubgroup (n : ℕ) : Subgroup H :=
  (UG.principalUnitSubgroup (targetLevel n)).comap N.toHom

/--
Characterizes `x ∈ N.filtrationPreimageSubgroup UG targetLevel n` by the equivalent condition
`N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n)`.
-/
@[simp] theorem mem_filtrationPreimageSubgroup_iff (n : ℕ) (x : H) :
    x ∈ N.filtrationPreimageSubgroup UG targetLevel n ↔
      N.toHom x ∈ UG.principalUnitSubgroup (targetLevel n) :=
  Iff.rfl



/-- The subgroup appearing in `(N.filtrationPreimageSubgroup UG targetLevel n).Normal` is normal. -/
instance filtrationPreimageSubgroup_normal
    (n : ℕ) [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (N.filtrationPreimageSubgroup UG targetLevel n).Normal := by
  dsimp [filtrationPreimageSubgroup]
  infer_instance

/-- The class of the norm-preimage of the target filtration subgroup inside
the source quotient `H ⧸ U_H^n`. -/
def filtrationPreimageClassInQuotient (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal] :
    Subgroup (H ⧸ UH.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (UH.principalUnitSubgroup n))
    (N.filtrationPreimageSubgroup UG targetLevel n)

/--
The subgroup appearing in `(N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal` is
normal.
-/
instance filtrationPreimageClassInQuotient_normal
    (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (N.filtrationPreimageClassInQuotient UG UH targetLevel n).Normal := by
  dsimp [filtrationPreimageClassInQuotient]
  infer_instance







/-- The kernel of the quotient norm map is the class of the preimage of the
target filtration subgroup in the source quotient. -/
theorem quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).ker =
      N.filtrationPreimageClassInQuotient UG UH targetLevel n := by
  exact QuotientGroup.ker_map (UH.principalUnitSubgroup n)
    (UG.principalUnitSubgroup (targetLevel n)) N.toHom (fun _ hx => hN n hx)

































/-- First-isomorphism form of the filtration quotient norm map, with codomain
the actual range when no surjectivity hypothesis is available. -/
noncomputable def quotientModuloFiltrationPreimageClassEquivRange
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    (H ⧸ UH.principalUnitSubgroup n) ⧸
        N.filtrationPreimageClassInQuotient UG UH targetLevel n ≃*
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
        UG UH targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN n
(QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
(quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q :=
  rfl

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN n
(QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)) = (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN
n).rangeRestrict (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) :=
  rfl

/--
Establishes the identity `((N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
(quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) : G ⧸ UG.principalUnitSubgroup
(targetLevel n)) = quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q`.
-/
@[simp] theorem coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
  rw [N.quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n q]
  rfl

/--
Establishes the identity `((N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)) : (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN
n).range) : G ⧸ UG.principalUnitSubgroup (targetLevel n)) = QuotientGroup.mk'
(UG.principalUnitSubgroup (targetLevel n)) (N.toHom x)`.
-/
@[simp] theorem coe_quotientModuloFiltrationPreimageClassEquivRange_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    ((N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) :
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).range) :
        G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
        (N.toHom x) := by
  rw [N.coe_quotientModuloFiltrationPreimageClassEquivRange_mk
    UG UH targetLevel hN n
    (QuotientGroup.mk' (UH.principalUnitSubgroup n) x),
    N.quotientMapOfMapsFiltrationLevels_apply_mk' UG UH targetLevel hN n x]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n).symm ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q) =
QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (q : H ⧸ UH.principalUnitSubgroup n) :
    (N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n).symm
        ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q := by
  apply (N.quotientModuloFiltrationPreimageClassEquivRange
    UG UH targetLevel hN n).injective
  calc
    N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        ((N.quotientModuloFiltrationPreimageClassEquivRange
          UG UH targetLevel hN n).symm
          ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q)) =
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict q := by
        exact
          (N.quotientModuloFiltrationPreimageClassEquivRange
            UG UH targetLevel hN n).apply_symm_apply _
    _ =
      N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) := by
        rw [N.quotientModuloFiltrationPreimageClassEquivRange_mk
          UG UH targetLevel hN n q]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivRange UG UH targetLevel hN
n).symm ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
(QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) = QuotientGroup.mk'
(N.filtrationPreimageClassInQuotient UG UH targetLevel n) (QuotientGroup.mk'
(UH.principalUnitSubgroup n) x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] (x : H) :
    (N.quotientModuloFiltrationPreimageClassEquivRange
        UG UH targetLevel hN n).symm
        ((quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n).rangeRestrict
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) := by
  rw [N.quotientModuloFiltrationPreimageClassEquivRange_symm_rangeRestrict
    UG UH targetLevel hN n]

/-- First-isomorphism form of a surjective filtration quotient norm map. -/
noncomputable def quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) :
    (H ⧸ UH.principalUnitSubgroup n) ⧸
        N.filtrationPreimageClassInQuotient UG UH targetLevel n ≃*
      G ⧸ UG.principalUnitSubgroup (targetLevel n) :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
        UG UH targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) hSurj)

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel
n) q) = quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))
    (q : H ⧸ UH.principalUnitSubgroup n) :
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
  change QuotientGroup.kerLift
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)
      ((QuotientGroup.quotientMulEquivOfEq
        (N.quotientMapOfMapsFiltrationLevels_ker_eq_filtrationPreimageClass
          UG UH targetLevel hN n).symm) (QuotientGroup.mk q)) =
    quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk
    (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n) q

/--
Establishes the identity `N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj (QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel
n) (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) = QuotientGroup.mk'
(UG.principalUnitSubgroup (targetLevel n)) (N.toHom x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) (x : H) :
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
          (QuotientGroup.mk' (UH.principalUnitSubgroup n) x)) =
      QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
        (N.toHom x) := by
  rw [N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
    UG UH targetLevel hN n hSurj,
    N.quotientMapOfMapsFiltrationLevels_apply_mk' UG UH targetLevel hN n x]



/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj).symm (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q) =
QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_map
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n))
    (q : H ⧸ UH.principalUnitSubgroup n) :
    (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj).symm
        (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q := by
  apply (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
    UG UH targetLevel hN n hSurj).injective
  calc
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        ((N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
          UG UH targetLevel hN n hSurj).symm
          (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n q := by
        exact
          (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
            UG UH targetLevel hN n hSurj).apply_symm_apply _
    _ =
      N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj
        (QuotientGroup.mk'
          (N.filtrationPreimageClassInQuotient UG UH targetLevel n) q) := by
        rw [N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_mk
          UG UH targetLevel hN n hSurj q]

/--
Establishes the identity `(N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective UG UH
targetLevel hN n hSurj).symm (QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
(N.toHom x)) = QuotientGroup.mk' (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
(QuotientGroup.mk' (UH.principalUnitSubgroup n) x)`.
-/
@[simp] theorem quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n)) (x : H) :
    (N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective
        UG UH targetLevel hN n hSurj).symm
        (QuotientGroup.mk' (UG.principalUnitSubgroup (targetLevel n))
          (N.toHom x)) =
      QuotientGroup.mk'
        (N.filtrationPreimageClassInQuotient UG UH targetLevel n)
        (QuotientGroup.mk' (UH.principalUnitSubgroup n) x) := by
  rw [← N.quotientMapOfMapsFiltrationLevels_apply_mk'
    UG UH targetLevel hN n x,
    N.quotientModuloFiltrationPreimageClassEquivTargetOfSurjective_symm_map
      UG UH targetLevel hN n hSurj]



























/-- A filtration-compatible norm induces maps on principal-unit subquotients:
`U_H^m/U_H^n → U_G^(targetLevel m)/U_G^(targetLevel n)`. -/
def principalUnitSubquotientMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (_hmn : m ≤ n) (_htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal] :
    UH.principalUnitSubquotient m n →*
      UG.principalUnitSubquotient (targetLevel m) (targetLevel n) :=
  UH.principalUnitSubquotientLift m n
    ((UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)).comp
      (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m))
    (by
      intro x hx
      change UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)
          (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) = 1
      rw [UG.principalUnitSubquotient_mk_eq_one_iff]
      exact hN n hx)

/--
The defining evaluation formula for `principalUnitSubquotientMapOfMapsFiltrationLevels` is
`N.principalUnitSubquotientMapOfMapsFiltrationLevels UG UH targetLevel hN hmn htarget
(UH.principalUnitSubquotientMk m n x) = UG.principalUnitSubquotientMk (targetLevel m) (targetLevel
n) (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x)`.
-/
@[simp] theorem principalUnitSubquotientMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (x : UH.principalUnitSubgroup m) :
    N.principalUnitSubquotientMapOfMapsFiltrationLevels
        UG UH targetLevel hN hmn htarget
        (UH.principalUnitSubquotientMk m n x) =
      UG.principalUnitSubquotientMk (targetLevel m) (targetLevel n)
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN m x) :=
  rfl

/-- The subquotient norm map agrees with the ambient quotient norm map under
the canonical embeddings of subquotients as classes in ambient quotients. -/
@[simp] theorem coe_principalUnitSubquotientEquivClassInQuotient_map
    (hN : MapsFiltrationLevels N UG UH targetLevel) {m n : ℕ}
    (hmn : m ≤ n) (htarget : targetLevel m ≤ targetLevel n)
    [(UH.principalUnitSubgroup n).Normal]
    [(UG.principalUnitSubgroup (targetLevel n)).Normal]
    (z : UH.principalUnitSubquotient m n) :
    ((UG.principalUnitSubquotientEquivClassInQuotientOfLe htarget
        (N.principalUnitSubquotientMapOfMapsFiltrationLevels
          UG UH targetLevel hN hmn htarget z) :
      UG.principalUnitSubgroupClassInQuotient (targetLevel m)
        (targetLevel n)) :
      G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
      quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
        ((UH.principalUnitSubquotientEquivClassInQuotientOfLe hmn z :
          UH.principalUnitSubgroupClassInQuotient m n) :
          H ⧸ UH.principalUnitSubgroup n) := by
  refine
    AntitoneSubgroupFiltration.principalUnitSubquotient.inductionOn
      UH m n
        (motive := fun z' ↦
          ((UG.principalUnitSubquotientEquivClassInQuotientOfLe htarget
              (N.principalUnitSubquotientMapOfMapsFiltrationLevels
                UG UH targetLevel hN hmn htarget z') :
            UG.principalUnitSubgroupClassInQuotient (targetLevel m)
              (targetLevel n)) :
            G ⧸ UG.principalUnitSubgroup (targetLevel n)) =
          quotientMapOfMapsFiltrationLevels N UG UH targetLevel hN n
            ((UH.principalUnitSubquotientEquivClassInQuotientOfLe hmn z' :
              UH.principalUnitSubgroupClassInQuotient m n) :
              H ⧸ UH.principalUnitSubgroup n)) z ?_
  intro x
  simp

/-- The graded-piece form of
`principalUnitSubquotientMapOfMapsFiltrationLevels`. -/
def principalUnitGradedPieceMapOfMapsFiltrationLevels
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.principalUnitSubgroup (n + 1)).Normal]
    [(UG.principalUnitSubgroup (targetLevel (n + 1))).Normal] :
    UH.principalUnitGradedPiece n →*
      UG.principalUnitSubquotient (targetLevel n) (targetLevel (n + 1)) :=
  (N.principalUnitSubquotientMapOfMapsFiltrationLevels
    UG UH targetLevel hN (Nat.le_succ n) htarget).comp
      (UH.principalUnitGradedPieceEquivSubquotient n).toMonoidHom

/--
The defining evaluation formula for `principalUnitGradedPieceMapOfMapsFiltrationLevels` is
`N.principalUnitGradedPieceMapOfMapsFiltrationLevels UG UH targetLevel hN n htarget
(UH.principalUnitGradedPieceMk n x) = UG.principalUnitSubquotientMk (targetLevel n) (targetLevel
(n + 1)) (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x)`.
-/
@[simp] theorem principalUnitGradedPieceMapOfMapsFiltrationLevels_apply_mk
    (hN : MapsFiltrationLevels N UG UH targetLevel) (n : ℕ)
    (htarget : targetLevel n ≤ targetLevel (n + 1))
    [(UH.principalUnitSubgroup (n + 1)).Normal]
    [(UG.principalUnitSubgroup (targetLevel (n + 1))).Normal]
    (x : UH.principalUnitSubgroup n) :
    N.principalUnitGradedPieceMapOfMapsFiltrationLevels
        UG UH targetLevel hN n htarget
        (UH.principalUnitGradedPieceMk n x) =
      UG.principalUnitSubquotientMk (targetLevel n) (targetLevel (n + 1))
        (mapLevelOfMapsFiltrationLevels N UG UH targetLevel hN n x) :=
  rfl









































end ValuedNorm
end DiscreteValuationField

end

end LocalFieldTheory
