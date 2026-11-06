module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Evaluation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The equal-characteristic completed-unramified construction: the completed maximal-unramified field in equal characteristic

For a finite field `k`, the equal-characteristic model of the completion of
the maximal unramified extension of `k((T))` is
`(AlgebraicClosure k)((T))`.  This file equips that field with the genuine
coefficientwise arithmetic Frobenius over `k((T))`.

This is the equal-characteristic specialization of the completed-unramified
source in the equal-characteristic completed-unramified construction.  In particular, the Frobenius below is an actual algebra
equivalence; it is not a theorem-shaped replacement for later theta
evaluation or norm-subgroup arguments.
-/

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries PowerSeries.WithPiTopology
  Topology Valued WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

variable (k : Type u) [Field k] [Finite k]

omit [Finite k] in
noncomputable local instance equalCharacteristicCoefficientUniformSpace :
    UniformSpace (AlgebraicClosure k) := ⊥

/-- The equal-characteristic model of the completed maximal unramified
extension of `k((T))`. -/
def equalCharacteristicCompletedUnramifiedField :=
  (AlgebraicClosure k)⸨X⸩

/-- The completed unramified Laurent-series model is a field. -/
instance equalCharacteristicCompletedUnramifiedField_field :
    Field (equalCharacteristicCompletedUnramifiedField k) := by
  change Field ((AlgebraicClosure k)⸨X⸩)
  infer_instance

/-- The completed unramified field carries its Laurent-series valuation. -/
instance equalCharacteristicCompletedUnramifiedField_valued :
    Valued (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰ := by
  change Valued ((AlgebraicClosure k)⸨X⸩) ℤᵐ⁰
  infer_instance

/-- The completed unramified Laurent-series field is complete. -/
instance equalCharacteristicCompletedUnramifiedField_completeSpace :
    CompleteSpace (equalCharacteristicCompletedUnramifiedField k) := by
  change CompleteSpace ((AlgebraicClosure k)⸨X⸩)
  infer_instance

/-- Comparison with the Laurent-series model underlying the completed
unramified field. -/
def equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries :
    equalCharacteristicCompletedUnramifiedField k ≃+*
      (AlgebraicClosure k)⸨X⸩ :=
  RingEquiv.refl _

/-- Embed a Laurent series into the named completed-unramified field. -/
def equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries :
    (AlgebraicClosure k)⸨X⸩ →+*
      equalCharacteristicCompletedUnramifiedField k :=
  (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries k).symm.toRingHom

/-- Read a named completed-unramified element in its Laurent-series model. -/
def equalCharacteristicCompletedUnramifiedFieldToLaurentSeries :
    equalCharacteristicCompletedUnramifiedField k →+*
      (AlgebraicClosure k)⸨X⸩ :=
  (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries k).toRingHom

omit [Finite k] in
/-- Converting a Laurent series into the named field and back returns the series. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFieldToLaurentSeries_ofLaurentSeries
    (x : (AlgebraicClosure k)⸨X⸩) :
    equalCharacteristicCompletedUnramifiedFieldToLaurentSeries k
        (equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries k x) = x :=
  rfl

/-- A single Laurent monomial in the named completed-unramified field. -/
def equalCharacteristicCompletedUnramifiedFieldSingle
    (m : ℤ) (a : AlgebraicClosure k) :
    equalCharacteristicCompletedUnramifiedField k :=
  equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries k
    (HahnSeries.single m a)

/-- The coefficient of a named completed-unramified Laurent element. -/
def equalCharacteristicCompletedUnramifiedFieldCoeff
    (x : equalCharacteristicCompletedUnramifiedField k) (m : ℤ) :
    AlgebraicClosure k :=
  (equalCharacteristicCompletedUnramifiedFieldToLaurentSeries k x).coeff m

omit [Finite k] in
/-- Coefficients of an imported Laurent series agree with its original coefficients. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFieldCoeff_ofLaurentSeries
    (x : (AlgebraicClosure k)⸨X⸩) (m : ℤ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k
        (equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries k x) m =
      x.coeff m :=
  rfl

omit [Finite k] in
/-- Two named completed-unramified elements are equal when all Laurent
coefficients agree. -/
@[ext]
theorem equalCharacteristicCompletedUnramifiedField_ext
    {x y : equalCharacteristicCompletedUnramifiedField k}
    (h : ∀ m, equalCharacteristicCompletedUnramifiedFieldCoeff k x m =
      equalCharacteristicCompletedUnramifiedFieldCoeff k y m) :
    x = y := by
  apply (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries k).injective
  ext m
  exact h m

/-- The completed unramified field is an algebra over algebraic-closure power series. -/
instance equalCharacteristicCompletedUnramifiedPowerSeriesAlgebra :
    Algebra (AlgebraicClosure k)⟦X⟧
      (equalCharacteristicCompletedUnramifiedField k) := by
  change Algebra (AlgebraicClosure k)⟦X⟧ (AlgebraicClosure k)⸨X⸩
  infer_instance

/-- The completed unramified field is an algebra over the residue base field. -/
instance equalCharacteristicCompletedUnramifiedCoefficientAlgebra :
    Algebra k (equalCharacteristicCompletedUnramifiedField k) := by
  change Algebra k (AlgebraicClosure k)⸨X⸩
  infer_instance

/-- The completed unramified field is an algebra over the Laurent-series base. -/
instance equalCharacteristicCompletedUnramifiedAlgebra :
    Algebra k⸨X⸩ (equalCharacteristicCompletedUnramifiedField k) :=
  laurentSeriesCoefficientAlgebra

/-- The named completed-unramified Laurent field is the fraction field of its
power-series integer ring. -/
instance equalCharacteristicCompletedUnramifiedIsFractionRing :
    IsFractionRing (AlgebraicClosure k)⟦X⟧
      (equalCharacteristicCompletedUnramifiedField k) := by
  change IsFractionRing (AlgebraicClosure k)⟦X⟧
    (AlgebraicClosure k)⸨X⸩
  infer_instance

omit [Finite k] in
/-- A mapped power series has its original nonnegative coefficients. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFieldCoeff_algebraMap_powerSeries
    (f : (AlgebraicClosure k)⟦X⟧) (n : ℕ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k
        (algebraMap (AlgebraicClosure k)⟦X⟧
          (equalCharacteristicCompletedUnramifiedField k) f) n =
      PowerSeries.coeff n f := by
  change ((f : (AlgebraicClosure k)⸨X⸩).coeff (Int.ofNat n)) =
    PowerSeries.coeff n f
  simp

omit [Finite k] in
/-- A mapped base Laurent series has coefficients embedded into the algebraic closure. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFieldCoeff_algebraMap_laurentSeries
    (f : k⸨X⸩) (m : ℤ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k
        (algebraMap k⸨X⸩
          (equalCharacteristicCompletedUnramifiedField k) f) m =
      algebraMap k (AlgebraicClosure k) (f.coeff m) := by
  rfl

/-- Arithmetic Frobenius on the completed maximal-unramified Laurent field,
acting coefficientwise and fixing the Laurent-series base `k((T))`. -/
def equalCharacteristicCompletedUnramifiedFrobenius :
    equalCharacteristicCompletedUnramifiedField k ≃ₐ[k⸨X⸩]
      equalCharacteristicCompletedUnramifiedField k :=
  laurentSeriesCoefficientAlgEquiv
    (equalCharacteristicCoefficientFrobenius k)
