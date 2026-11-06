module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import Mathlib.RingTheory.PowerSeries.Evaluation

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

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

section
variable {K : Type u} {Γ : Type v} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
include K Γ
/-- The valuation balls in a valued integer ring, expressed as genuine
ideals, form its neighbourhood basis at zero. -/
theorem valuedInteger_hasBasis_ltIdeal
      :
    (𝓝 (0)).HasBasis
      (fun _ : (MonoidWithZeroHom.ValueGroup₀
        ((Valued.v : Valuation K Γ) : K →*₀ Γ))ˣ ↦ True)
      (fun γ ↦ (Valuation.ltIdeal (Valued.v : Valuation K Γ)
        (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
          (f := ((Valued.v : Valuation K Γ) : K →*₀ Γ))) γ) :
        Set (Valued.integer K))) := by
  rw [nhds_subtype]
  refine ((Valued.hasBasis_nhds_zero K Γ).comap
    ((↑) : Valued.integer K → K)).congr (fun _ ↦ Iff.rfl) ?_
  intro γ _
  ext x
  change (Valued.v : Valuation K Γ).restrict x < (γ.1) ↔
    (Valued.v : Valuation K Γ) (x : K) <
      ((Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := ((Valued.v : Valuation K Γ) : K →*₀ Γ))) γ : Γˣ) : Γ)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simp

/-- The native topology on a valued integer ring is linear: its valuation
balls are ideals. -/
theorem valuedIntegerLinearTopology
      :
    IsLinearTopology (Valued.integer K) (Valued.integer K) :=
  IsLinearTopology.mk_of_hasBasis (Valued.integer K)
    (valuedInteger_hasBasis_ltIdeal (K := K))

/-- A closed valued integer ring inherits completeness from its fraction
field. -/
theorem valuedIntegerCompleteSpace
      [CompleteSpace K] :
    CompleteSpace (Valued.integer K) :=
  (Valued.isClosed_integer K).completeSpace_coe

/-- The induced uniformity on a valued integer ring is compatible with its
additive group. -/
theorem valuedIntegerIsUniformAddGroup
      :
    IsUniformAddGroup (Valued.integer K) :=
  (Valued.integer K).toAddSubgroup.isUniformAddGroup
end
























/-- The fixed elements of arithmetic Frobenius in the algebraic closure are
exactly the embedded elements of the finite coefficient field. -/
theorem equalCharacteristicCoefficientFrobenius_fixed_iff
    (x : AlgebraicClosure k) :
    equalCharacteristicCoefficientFrobenius k x = x ↔
      x ∈ (algebraMap k (AlgebraicClosure k)).range := by
  constructor
  · intro hx
    have hxpow : x ^ Nat.card k = x := by
      simpa [equalCharacteristicCoefficientFrobenius_apply] using hx
    let  := Fintype.ofFinite k
    have hxint : IsIntegral k x :=
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hroot : Polynomial.aeval x
        (Polynomial.X ^ Nat.card k - Polynomial.X : k[X]) = 0 := by
      simpa using sub_eq_zero.mpr hxpow
    have hdiv : minpoly k x ∣
        (Polynomial.X ^ Nat.card k - Polynomial.X) :=
      minpoly.dvd k x hroot
    have hsplit :
        (Polynomial.X ^ Nat.card k - Polynomial.X : k[X]).Splits := by
      rw [Nat.card_eq_fintype_card]
      simpa using (FiniteField.isSplittingField_sub k k).splits
    have hpolyne :
        (Polynomial.X ^ Nat.card k - Polynomial.X : k[X]) ≠ 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hminsplit  :=
      hsplit.of_dvd hpolyne hdiv
    apply hxint.mem_range_algebraMap_of_minpoly_splits <;> aesop
  · rintro ⟨a, rfl⟩
    exact (equalCharacteristicCoefficientFrobenius k).commutes a

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
noncomputable instance equalCharacteristicCompletedUnramifiedField_valued :
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
def equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries  :=
  (equalCharacteristicCompletedUnramifiedFieldEquivLaurentSeries k).symm.toRingHom

/-- Read a named completed-unramified element in its Laurent-series model. -/
def equalCharacteristicCompletedUnramifiedFieldToLaurentSeries  :=
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
    (m : ℤ) (a : AlgebraicClosure k)  :=
  equalCharacteristicCompletedUnramifiedFieldOfLaurentSeries k
    (HahnSeries.single m a)

/-- The coefficient of a named completed-unramified Laurent element. -/
def equalCharacteristicCompletedUnramifiedFieldCoeff
    (x : equalCharacteristicCompletedUnramifiedField k) (m : ℤ)  :=
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
noncomputable instance equalCharacteristicCompletedUnramifiedPowerSeriesAlgebra :
    Algebra (AlgebraicClosure k)⟦X⟧
      (equalCharacteristicCompletedUnramifiedField k) := by
  change Algebra (AlgebraicClosure k)⟦X⟧ (AlgebraicClosure k)⸨X⸩
  infer_instance

/-- The completed unramified field is an algebra over the residue base field. -/
noncomputable instance equalCharacteristicCompletedUnramifiedCoefficientAlgebra :
    Algebra k (equalCharacteristicCompletedUnramifiedField k) := by
  change Algebra k (AlgebraicClosure k)⸨X⸩
  infer_instance

/-- The completed unramified field is an algebra over the Laurent-series base. -/
noncomputable instance equalCharacteristicCompletedUnramifiedAlgebra :
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
noncomputable def equalCharacteristicCompletedUnramifiedFrobenius :
    equalCharacteristicCompletedUnramifiedField k ≃ₐ[k⸨X⸩]
      equalCharacteristicCompletedUnramifiedField k :=
  laurentSeriesCoefficientAlgEquiv
    (equalCharacteristicCoefficientFrobenius k)

/-- Completed Frobenius applies coefficient Frobenius at every Laurent exponent. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFrobenius_coeff
    (x : equalCharacteristicCompletedUnramifiedField k) (m : ℤ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k
        (equalCharacteristicCompletedUnramifiedFrobenius k x) m =
  equalCharacteristicCompletedUnramifiedFieldCoeff k x m ^
        Nat.card k := by
  change
    (laurentSeriesCoefficientAlgEquiv
        (equalCharacteristicCoefficientFrobenius k)
        (equalCharacteristicCompletedUnramifiedFieldToLaurentSeries k x)).coeff m =
      (equalCharacteristicCompletedUnramifiedFieldToLaurentSeries k x).coeff m ^
        Nat.card k
  rw [laurentSeriesCoefficientAlgEquiv_coeff,
    equalCharacteristicCoefficientFrobenius_apply]

/-- Coefficient Frobenius preserves the native Laurent valuation. -/
theorem equalCharacteristicCompletedUnramifiedFrobenius_valuation
    (x : equalCharacteristicCompletedUnramifiedField k) :
    Valued.v (equalCharacteristicCompletedUnramifiedFrobenius k x) =
      Valued.v x := by
  apply le_antisymm
  · by_cases hx : x = 0
    · simp [hx]
    have hxval : Valued.v x ≠ (0 : ℤᵐ⁰) :=
      (Valuation.ne_zero_iff Valued.v).2 hx
    apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero
      (AlgebraicClosure k) hxval).2
    intro n hn
    have hcoeff :=
      (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero
        (AlgebraicClosure k) hxval).1 (le_refl (Valued.v x)) n hn
    change equalCharacteristicCompletedUnramifiedFieldCoeff k x n = 0 at hcoeff
    change equalCharacteristicCompletedUnramifiedFieldCoeff k
      (equalCharacteristicCompletedUnramifiedFrobenius k x) n = 0
    rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff, hcoeff]
    exact zero_pow Nat.card_pos.ne'
  · by_cases hx : x = 0
    · simp [hx]
    have hfxne : equalCharacteristicCompletedUnramifiedFrobenius k x ≠ 0 :=
      (map_ne_zero (equalCharacteristicCompletedUnramifiedFrobenius k)).2 hx
    have hfxval :
        Valued.v (equalCharacteristicCompletedUnramifiedFrobenius k x) ≠
          (0 : ℤᵐ⁰) :=
      (Valuation.ne_zero_iff Valued.v).2 hfxne
    apply (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero
      (AlgebraicClosure k) hfxval).2
    intro n hn
    have hcoeff :=
      (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero
        (AlgebraicClosure k) hfxval).1
          (le_refl (Valued.v
            (equalCharacteristicCompletedUnramifiedFrobenius k x))) n hn
    change equalCharacteristicCompletedUnramifiedFieldCoeff k
      (equalCharacteristicCompletedUnramifiedFrobenius k x) n = 0 at hcoeff
    rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff] at hcoeff
    exact eq_zero_of_pow_eq_zero hcoeff

























/-- On the integer ring `(AlgebraicClosure k)[[T]]`, Laurent Frobenius is
the coefficientwise power-series Frobenius constructed for theta. -/
theorem equalCharacteristicCompletedUnramifiedFrobenius_algebraMap_powerSeries
    (f : (AlgebraicClosure k)⟦X⟧) :
    equalCharacteristicCompletedUnramifiedFrobenius k
        (algebraMap ((AlgebraicClosure k)⟦X⟧)
          (equalCharacteristicCompletedUnramifiedField k) f) =
      algebraMap ((AlgebraicClosure k)⟦X⟧)
        (equalCharacteristicCompletedUnramifiedField k)
        (equalCharacteristicPowerSeriesFrobenius k f) := by
  have hcard : Nat.card k ≠ 0 := Nat.card_pos.ne'
  ext m
  cases m with
  | ofNat n =>
      simp_all
  | negSucc n =>
      rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff]
      change
        ((f : (AlgebraicClosure k)⸨X⸩).coeff (Int.negSucc n)) ^
            Nat.card k =
          ((equalCharacteristicPowerSeriesFrobenius k f) :
              (AlgebraicClosure k)⸨X⸩).coeff (Int.negSucc n)
      rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
      simp [hcard]

section
variable (x : equalCharacteristicCompletedUnramifiedField k)
    (hx : equalCharacteristicCompletedUnramifiedFrobenius k x = x)
include x hx
/-- Every coefficient of a Frobenius-fixed completed Laurent series comes
from the original finite coefficient field. -/
theorem equalCharacteristicCompletedUnramified_fixed_coeff_mem_range
     
    (m : ℤ) :
    equalCharacteristicCompletedUnramifiedFieldCoeff k x m ∈
      (algebraMap k (AlgebraicClosure k)).range := by
  apply (equalCharacteristicCoefficientFrobenius_fixed_iff k
    (equalCharacteristicCompletedUnramifiedFieldCoeff k x m)).1
  rw [equalCharacteristicCoefficientFrobenius_apply]
  have hcoeff := congrArg
    (fun y : equalCharacteristicCompletedUnramifiedField k ↦
      equalCharacteristicCompletedUnramifiedFieldCoeff k y m) hx
  change equalCharacteristicCompletedUnramifiedFieldCoeff k
      (equalCharacteristicCompletedUnramifiedFrobenius k x) m =
    equalCharacteristicCompletedUnramifiedFieldCoeff k x m at hcoeff
  rw [equalCharacteristicCompletedUnramifiedFrobenius_coeff] at hcoeff
  exact hcoeff

/-- A chosen coefficient in `k` lifting one coefficient of a
Frobenius-fixed completed Laurent series. -/
noncomputable def equalCharacteristicCompletedUnramifiedFixedCoeff
     
    (m : ℤ)  :=
  Classical.choose
    (equalCharacteristicCompletedUnramified_fixed_coeff_mem_range k x hx m)

/-- The chosen base coefficient embeds to the coefficient of the fixed series. -/
@[simp]
theorem algebraMap_equalCharacteristicCompletedUnramifiedFixedCoeff
     
    (m : ℤ) :
    algebraMap k (AlgebraicClosure k)
        (equalCharacteristicCompletedUnramifiedFixedCoeff k x hx m) =
      equalCharacteristicCompletedUnramifiedFieldCoeff k x m :=
  Classical.choose_spec
    (equalCharacteristicCompletedUnramified_fixed_coeff_mem_range k x hx m)

/-- A Frobenius-fixed series, descended coefficientwise to `k((T))`. -/
noncomputable def equalCharacteristicCompletedUnramifiedFixedPreimage
      :
    k⸨X⸩ :=
  HahnSeries.ofSuppBddBelow
    (fun m : ℤ ↦
      equalCharacteristicCompletedUnramifiedFixedCoeff k x hx m)
    (by
      refine ⟨x.order, ?_⟩
      intro m hm
      by_contra hnot
      have hxzero :
          equalCharacteristicCompletedUnramifiedFieldCoeff k x m = 0 := by
        apply HahnSeries.coeff_eq_zero_of_lt_order <;> aesop
      apply hm
      apply (algebraMap k (AlgebraicClosure k)).injective
      rw [map_zero,
        algebraMap_equalCharacteristicCompletedUnramifiedFixedCoeff,
        hxzero])
end













/-- The fixed field of coefficientwise Frobenius is exactly the embedded
Laurent-series base `k((T))`. -/
theorem equalCharacteristicCompletedUnramifiedFrobenius_fixed_iff
    (x : equalCharacteristicCompletedUnramifiedField k) :
    equalCharacteristicCompletedUnramifiedFrobenius k x = x ↔
      x ∈ (algebraMap k⸨X⸩
        (equalCharacteristicCompletedUnramifiedField k)).range := by
  constructor
  · intro hx
    refine ⟨equalCharacteristicCompletedUnramifiedFixedPreimage k x hx, ?_⟩
    ext m
    apply algebraMap_equalCharacteristicCompletedUnramifiedFixedCoeff <;> assumption
  · rintro ⟨y, rfl⟩
    exact (equalCharacteristicCompletedUnramifiedFrobenius k).commutes y

/-- The Frobenius fixes the Laurent uniformizer `T`. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFrobenius_uniformizer :
    equalCharacteristicCompletedUnramifiedFrobenius k
        (equalCharacteristicCompletedUnramifiedFieldSingle k 1 1) =
      equalCharacteristicCompletedUnramifiedFieldSingle k 1 1 := by
  have hcard : Nat.card k ≠ 0 := Nat.card_pos.ne'
  ext m
  by_cases h : m = 1
  · subst m
    simp [equalCharacteristicCompletedUnramifiedFieldSingle]
  · simp [equalCharacteristicCompletedUnramifiedFieldSingle, h, hcard]

/-- Evaluation of an outer power series with coefficients in
`(AlgebraicClosure k)[[T]]` at a topologically nilpotent point of the
completed-unramified integer ring.  This is the analytic evaluation map
needed for the theta series in the completed theta-intertwining theorem. -/
noncomputable def equalCharacteristicPowerSeriesToCompletedInteger :
    (AlgebraicClosure k)⟦X⟧ →+*
      Valued.integer (equalCharacteristicCompletedUnramifiedField k) := by
  change (AlgebraicClosure k)⟦X⟧ →+*
    Valued.integer ((AlgebraicClosure k)⸨X⸩)
  exact
    (powerSeriesEquivLaurentInteger (AlgebraicClosure k)).toRingHom



































































end EqualCharacteristic
end LubinTate

end
