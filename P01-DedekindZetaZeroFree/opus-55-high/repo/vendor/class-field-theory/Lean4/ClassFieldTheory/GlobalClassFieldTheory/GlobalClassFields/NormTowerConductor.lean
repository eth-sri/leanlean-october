module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Norm quotients and narrow finite conductors in a field tower

For a finite tower `K ⊂ M ⊂ L`, norm transitivity places the actual
idele-class norms from `L` inside those from `M`.  This produces the
canonical quotient transition

`C_K / N_{L/K} C_L → C_K / N_{M/K} C_M`.

The transition is surjective, its kernel is the image of
`N_{M/K} C_M` modulo `N_{L/K} C_L`, and its orders satisfy the
corresponding exact factorization.  When both extensions over `K` are
Galois, the narrow finite conductor is contravariant under this
inclusion and the conductor support of the intermediate extension is
contained in that of the top extension.  This is the finite part in the
all-real-positive convention, not a claim about the full archimedean
conductor.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

/-- The canonical commutativity witness used to form ordinary norm quotients. -/
theorem normTowerIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) := by apply normIdeleClassGroup_isMulCommutative <;> assumption

attribute [local instance] normTowerIdeleClassIsMulCommutative

/-- Quotient commutativity follows by lifting representatives through the
canonical quotient map, without constructing another group dictionary. -/
theorem normTowerQuotientIsMulCommutative
    {G : Type*} [Group G] [IsMulCommutative G]
    (N : Subgroup G) : IsMulCommutative (G ⧸ N) := by
  refine IsMulCommutative.of_comm ?_
  intro a b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
  calc
    QuotientGroup.mk' N x * QuotientGroup.mk' N y =
        QuotientGroup.mk' N (x * y) :=
      ((QuotientGroup.mk' N).map_mul x y).symm
    _ = QuotientGroup.mk' N (y * x) :=
      congrArg (QuotientGroup.mk' N) (mul_comm' x y)
    _ = QuotientGroup.mk' N y * QuotientGroup.mk' N x :=
      (QuotientGroup.mk' N).map_mul y x

/-- A quotient of the idele class group is commutative, so its norm-image
subgroups are normal when forming the second quotient. -/
theorem normTowerIdeleClassQuotientIsMulCommutative
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) :
    IsMulCommutative (IdeleClassGroup F ⧸ N) :=
  normTowerQuotientIsMulCommutative N

attribute [local instance] normTowerIdeleClassQuotientIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

section Tower

variable
    {M L : Type}
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M] [IsGalois K L]

omit [IsGalois K M] [IsGalois K L] in
/-- Norm transitivity puts every idele-class norm from the top field
inside the idele-class norm subgroup of the intermediate field. -/
theorem ideleClassNorm_range_le_of_tower :
    (_root_.ideleClassNorm K L).range ≤
      (_root_.ideleClassNorm K M).range := by
  calc
    (_root_.ideleClassNorm K L).range =
        (RelativeIdeleGroup.classNorm K L).range :=
      ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := L)
    _ ≤
        (RelativeIdeleGroup.classNorm K M).range := by
      rw [← towerCompositeClassNorm_range_eq K M L]
      rintro _ ⟨c, rfl⟩
      exact
        ⟨TowerRelativeIdeleGroup.classNorm K M L c, rfl⟩
    _ = (_root_.ideleClassNorm K M).range :=
      (ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := M)).symm
