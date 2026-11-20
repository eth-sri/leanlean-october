module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Torsion and rank sources for `S`-units

This file supplies the algebraic rank and torsion input for `S`-units.
The finite set `S` contains the finite places; all infinite places are
understood to be present.
-/

noncomputable section

open IsDedekindDomain
open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

namespace SUnitGroup

/-- The group of ordinary units, expressed as `S`-units for the empty set. -/
noncomputable def emptyEquivNumberFieldUnits :
    ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) ≃* (𝓞 K)ˣ :=
  let eInteger :
      ((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K)ˣ ≃*
        (⊥ : Subalgebra (𝓞 K) K)ˣ :=
    Units.mapEquiv
      ((Subalgebra.equivOfEq
        ((∅ : Set (HeightOneSpectrum (𝓞 K))).integer K)
        (⊥ : Subalgebra (𝓞 K) K)
        (IsDedekindDomain.integer_empty (𝓞 K) K) : _ ≃ₐ[𝓞 K] _) : _ ≃* _)
  let eBot :
      (⊥ : Subalgebra (𝓞 K) K)ˣ ≃* (𝓞 K)ˣ :=
    Units.mapEquiv
      ((Algebra.botEquivOfInjective
        (IsFractionRing.injective (𝓞 K) K) : _ ≃ₐ[𝓞 K] _) : _ ≃* _)
  (Set.unitEquivUnitsInteger
    (∅ : Set (HeightOneSpectrum (𝓞 K))) K).trans
      (eInteger.trans eBot)

section

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The canonical embedding of ordinary units into the `S`-unit group. -/
noncomputable def fromNumberFieldUnits :
    (𝓞 K)ˣ →* SUnitGroup (K := K) S where
  toFun u :=
    ⟨((emptyEquivNumberFieldUnits (K := K)).symm u : Kˣ),
      fun v _ =>
        Set.unit_valuation_eq_one
          (∅ : Set (HeightOneSpectrum (𝓞 K))) K
          ((emptyEquivNumberFieldUnits (K := K)).symm u) (by simp)⟩
  map_one' := by
    ext
    simp
  map_mul' u v := by
    ext
    simp

theorem fromNumberFieldUnits_injective :
    Function.Injective (fromNumberFieldUnits S) := by
  intro u v huv
  apply (emptyEquivNumberFieldUnits).symm.injective
  ext
  exact congrArg (fun x : SUnitGroup S => ((x : Kˣ) : K)) huv

end

/-- Torsion in an `S`-unit group consists exactly of the ordinary roots of
unity. -/
theorem torsion_eq_rootsOfUnity_range
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    CommGroup.torsion (SUnitGroup S) =
      Subgroup.map (fromNumberFieldUnits S)
        (NumberField.Units.torsion K) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hnpos, hxpow⟩ := ((CommGroup.mem_torsion x).mp hx).exists_pow_eq_one
    have hxK : (((x : Kˣ) : K) ^ n) = 1 := by
      exact congrArg
        (fun y : SUnitGroup S => ((y : Kˣ) : K)) hxpow
    let y : ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
      ⟨(x : Kˣ), fun v _ => by
        refine (pow_eq_one_iff_left

          (Nat.ne_of_gt hnpos)).mp ?_
        rw [← map_pow, hxK, map_one]⟩
    let u := emptyEquivNumberFieldUnits y
    have hufin := (emptyEquivNumberFieldUnits).toMonoidHom.isOfFinOrder
        ((show IsOfFinOrder y from by
          refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hnpos, ?_⟩
          ext
          exact hxK))
    refine ⟨u, ?_, ?_⟩
    · assumption
    · ext
      change
        (((emptyEquivNumberFieldUnits).symm
          (emptyEquivNumberFieldUnits y) : Kˣ) : K) =
            ((x : Kˣ) : K)
      rw [MulEquiv.symm_apply_apply]
  · rintro ⟨u, hu, rfl⟩
    exact (CommGroup.mem_torsion

      (fromNumberFieldUnits S u)).2
        ((fromNumberFieldUnits S).isOfFinOrder
          ((CommGroup.mem_torsion u).1 hu))

section DivisorMap

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The exponent of the principal fractional ideal of an `S`-unit at a
finite place in `S`. -/
noncomputable def divisorCoordinate
    (x : SUnitGroup (K := K) S) (v : S) : ℤ :=
  FractionalIdeal.count K (v : HeightOneSpectrum (𝓞 K))
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K))

/-- The valuation of a localization fraction is the exponential of the
negative exponent of its principal fractional ideal. -/
theorem valuation_mk'_eq_exp_neg_count
    (v : HeightOneSpectrum (𝓞 K)) {n : 𝓞 K} (hn : n ≠ 0)
    (d : (𝓞 K)⁰) :
    v.valuation K (IsLocalization.mk' K n d) =
      WithZero.exp
        (-FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (IsLocalization.mk' K n d))) := by
  let spanSingleton₀ := FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K n d)
  classical
  have hI :
      spanSingleton₀ =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            ((algebraMap (𝓞 K) K) d)⁻¹ *
          ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hx :
      spanSingleton₀ ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff,
      IsFractionRing.mk'_eq_div, ne_eq, div_eq_zero_iff, not_or]
    exact
      ⟨(map_ne_zero_iff (algebraMap (𝓞 K) K)
          (IsFractionRing.injective (𝓞 K) K)).mpr hn,
        map_ne_zero_of_mem_nonZeroDivisors _
          (IsFractionRing.injective (𝓞 K) K) d.property⟩
  have hcount :
      FractionalIdeal.count K v
          (spanSingleton₀) =
        ((Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {n} : Ideal (𝓞 K))).factors -
          (Associates.mk v.asIdeal).count
            (Associates.mk
              (Ideal.span {(d : 𝓞 K)} : Ideal (𝓞 K))).factors : ℤ) := FractionalIdeal.count_well_defined (K := K) v hx hI
  rw [v.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d), hcount]
  rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr
  simp [sub_eq_add_neg, add_comm]

section

variable (x : Kˣ) (v : HeightOneSpectrum (𝓞 K))

/-- The adic valuation of a field unit is the exponential of the
negative exponent of its principal fractional ideal. -/
theorem valuation_eq_exp_neg_count :
    v.valuation K (x : K) =
      WithZero.exp
        (-FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))) := by
  obtain ⟨n, d, hnd⟩ :=
    IsLocalization.exists_mk'_eq (𝓞 K)⁰ (x : K)
  rw [← hnd]
  refine valuation_mk'_eq_exp_neg_count v ?_ d
  intro hn0
  apply Units.ne_zero x
  rw [← hnd, hn0, IsFractionRing.mk'_eq_div, map_zero, zero_div]

/-- A field unit has valuation one exactly when its principal fractional
ideal has exponent zero at the place. -/
theorem valuation_eq_one_iff_count_eq_zero :
    v.valuation K (x : K) = 1 ↔
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
  simp [valuation_eq_exp_neg_count]

end

theorem divisorCoordinate_eq_zero_iff
    (x : SUnitGroup S) (v : S) :
    divisorCoordinate S x v = 0 ↔
      (v : HeightOneSpectrum (𝓞 K)).valuation K ((x : Kˣ) : K) = 1 := (valuation_eq_one_iff_count_eq_zero
     (x : Kˣ) v).symm

theorem divisorCoordinate_mul
    (x y : SUnitGroup S) (v : S) :
    divisorCoordinate S (x * y) v =
      divisorCoordinate S x v +
        divisorCoordinate S y v := by
  change
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰
          ((((x : Kˣ) : K) * ((y : Kˣ) : K)))) =
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K)) +
        FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : Kˣ) : K))
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul]
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (Units.ne_zero (x : Kˣ))
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (Units.ne_zero (y : Kˣ))

theorem divisorCoordinate_one (v : S) :
    divisorCoordinate S 1 v = 0 := by
  simp [divisorCoordinate, FractionalIdeal.count_one]

/-- The additive principal-divisor map on `S`-units. -/
noncomputable def divisor :
    Additive (SUnitGroup (K := K) S) →+
      (S → ℤ) where
  toFun x v := divisorCoordinate (K := K) S (Additive.toMul x) v
  map_zero' := by
    ext v
    exact divisorCoordinate_one (K := K) S v
  map_add' x y := by
    ext v
    exact divisorCoordinate_mul (K := K) S
      (Additive.toMul x) (Additive.toMul y) v

/-- The `ℤ`-linear principal-divisor map on `S`-units. -/
noncomputable def divisorLinearMap :
    Additive (SUnitGroup (K := K) S) →ₗ[ℤ] (S → ℤ) :=
  (divisor (K := K) S).toIntLinearMap

/-- The additive linearization of the ordinary-unit embedding. -/
noncomputable def fromNumberFieldUnitsLinearMap :
    Additive (𝓞 K)ˣ →ₗ[ℤ]
      Additive (SUnitGroup (K := K) S) :=
  (MonoidHom.toAdditive
    (fromNumberFieldUnits (K := K) S)).toIntLinearMap

theorem fromNumberFieldUnitsLinearMap_injective :
    Function.Injective (fromNumberFieldUnitsLinearMap S) := by
  apply fromNumberFieldUnits_injective

/-- An `S`-unit in the kernel of the divisor map has valuation one at every
finite place. -/
theorem valuation_eq_one_of_mem_ker_divisorLinearMap
    {x : Additive (SUnitGroup S)}
    (hx : x ∈ LinearMap.ker (divisorLinearMap S))
    (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K
      ((((Additive.toMul x :
        SUnitGroup S) : Kˣ) : K)) = 1 := by
  by_cases hv : v ∈ S
  · exact (divisorCoordinate_eq_zero_iff S (Additive.toMul x) ⟨v, hv⟩).mp (congrFun (LinearMap.mem_ker.mp hx) ⟨v, hv⟩)
  · exact (Additive.toMul x).property v hv

/-- An `S`-unit in the divisor kernel, regarded as an `S`-unit for the
empty set. -/
noncomputable def kerDivisorToEmptySUnits
    (x : LinearMap.ker (divisorLinearMap (K := K) S)) :
    ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K) :=
  ⟨((Additive.toMul (x : Additive (SUnitGroup (K := K) S)) :
      SUnitGroup (K := K) S) : Kˣ),
    fun v _ =>
      valuation_eq_one_of_mem_ker_divisorLinearMap
        (K := K) S x.property v⟩

/-- Ordinary units are exactly the kernel of the `S`-unit divisor map. -/
theorem range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap :
    LinearMap.range (fromNumberFieldUnitsLinearMap S) =
      LinearMap.ker (divisorLinearMap S) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    apply LinearMap.mem_ker.mpr
    ext v
    apply (divisorCoordinate_eq_zero_iff S
      (fromNumberFieldUnits S (Additive.toMul u)) v).2
    exact Set.unit_valuation_eq_one
      (∅ : Set (HeightOneSpectrum (𝓞 K))) K
      ((emptyEquivNumberFieldUnits).symm (Additive.toMul u))
      (by simp)
  · intro hx
    let u := emptyEquivNumberFieldUnits (kerDivisorToEmptySUnits S ⟨x, hx⟩)
    refine ⟨Additive.ofMul u, ?_⟩
    apply Additive.toMul.injective
    change
      fromNumberFieldUnits S u = Additive.toMul x
    apply Subtype.ext
    change
      ((emptyEquivNumberFieldUnits).symm u : Kˣ) =
        ((Additive.toMul x : SUnitGroup S) : Kˣ)
    dsimp [u]
    simp
    rfl

end DivisorMap

section PrimePowerSources

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section

variable (v : S)

local notation "FinitePlace" => HeightOneSpectrum (𝓞 K)

/-- The class-number power of a prime ideal is principal. -/
theorem primeIdealPower_classNumber_isPrincipal :
    ((v : FinitePlace).asIdeal ^
      NumberField.classNumber K).IsPrincipal := by
  have hv0 :
      (v : FinitePlace).asIdeal ^
          NumberField.classNumber K ≠ 0 :=
    pow_ne_zero _ (v : FinitePlace).ne_bot
  apply (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hv0)).mp
  let mpr₀ := mem_nonZeroDivisors_iff_ne_zero.mpr (v : FinitePlace).ne_bot
  have hpow :
      (ClassGroup.mk0
        ⟨(v : FinitePlace).asIdeal,
          mpr₀⟩) ^
          Fintype.card (ClassGroup (𝓞 K)) = 1 :=
    pow_card_eq_one
  let I : (Ideal (𝓞 K))⁰ :=
    ⟨(v : FinitePlace).asIdeal,
      mpr₀⟩
  have hsub :
      (⟨(v : FinitePlace).asIdeal ^
          NumberField.classNumber K,
        mem_nonZeroDivisors_iff_ne_zero.mpr hv0⟩ :
          (Ideal (𝓞 K))⁰) =
        I ^ NumberField.classNumber K := rfl
  simp [hsub]
  exact hpow

/-- A generator of the principal `classNumber K`-th power of a prime ideal. -/
 noncomputable def primePowerGenerator : 𝓞 K :=
  let I :=
    (v : FinitePlace).asIdeal ^
      NumberField.classNumber K
  letI : I.IsPrincipal :=
    primeIdealPower_classNumber_isPrincipal (K := K) S v
  Submodule.IsPrincipal.generator I

private theorem span_primePowerGenerator :
    Ideal.span {primePowerGenerator S v} =
      (v : FinitePlace).asIdeal ^
        NumberField.classNumber K := by
  simp [primePowerGenerator]

 theorem primePowerGenerator_ne_zero :
    primePowerGenerator S v ≠ 0 := by
  intro hzero
  have hv0 :
      (v : FinitePlace).asIdeal ^
          NumberField.classNumber K ≠ 0 :=
    pow_ne_zero _ (v : FinitePlace).ne_bot
  apply hv0
  rw [← span_primePowerGenerator S v, hzero]
  simp

 theorem spanSingleton_primePowerGenerator :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K (primePowerGenerator S v)) =
      ((v : FinitePlace).asIdeal :
        FractionalIdeal (𝓞 K)⁰ K) ^ NumberField.classNumber K := by
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    span_primePowerGenerator S v,
    FractionalIdeal.coeIdeal_pow]

/-- An `S`-unit whose divisor is `classNumber K` times the basis divisor at
`v`. -/
 noncomputable def primePowerSUnit :
    SUnitGroup (K := K) S :=
  ⟨Units.mk0
      (algebraMap (𝓞 K) K (primePowerGenerator (K := K) S v))
      ((map_ne_zero_iff (algebraMap (𝓞 K) K)
        (IsFractionRing.injective (𝓞 K) K)).mpr
          (primePowerGenerator_ne_zero (K := K) S v)),
    fun w hw => by
      apply (valuation_eq_one_iff_count_eq_zero
        (Units.mk0
          (algebraMap (𝓞 K) K (primePowerGenerator S v))
          ((map_ne_zero_iff (algebraMap (𝓞 K) K)
            (IsFractionRing.injective (𝓞 K) K)).mpr
              (primePowerGenerator_ne_zero S v))) w).2
      change
        FractionalIdeal.count K w
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (primePowerGenerator S v))) = 0
      rw [spanSingleton_primePowerGenerator S v,
        FractionalIdeal.count_pow]
      have hwv :
          v ≠ w := fun hvw => hw (hvw ▸ v.property)
      rw [FractionalIdeal.count_maximal_coprime K w hwv]
      simp⟩

 noncomputable def classNumberBasisVector : S → ℤ := by
  classical
  exact fun w =>
    if w = v then (NumberField.classNumber K : ℤ) else 0

end

 theorem divisorCoordinate_primePowerSUnit
    (v w : S) :
    divisorCoordinate (K := K) S (primePowerSUnit S v) w =
      classNumberBasisVector S v w := by
  classical
  change
    FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (primePowerGenerator S v))) =
      classNumberBasisVector S v w
  simp only [classNumberBasisVector]
  rw [spanSingleton_primePowerGenerator S v]
  split_ifs with hwv
  · subst w
    simpa using
      FractionalIdeal.count_pow_self K
        (v : HeightOneSpectrum (𝓞 K))
        (NumberField.classNumber K)
  · rw [FractionalIdeal.count_pow]
    have hvw :
        (v : HeightOneSpectrum (𝓞 K)) ≠
          (w : HeightOneSpectrum (𝓞 K)) := fun h => hwv (Subtype.ext h.symm)
    rw [FractionalIdeal.count_maximal_coprime K
      (w : HeightOneSpectrum (𝓞 K)) hvw]
    simp

end PrimePowerSources

section Rank

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

 noncomputable def divisorRangeVector (v : S) :
    LinearMap.range (divisorLinearMap (K := K) S) :=
  ⟨classNumberBasisVector (K := K) S v,
    ⟨Additive.ofMul (primePowerSUnit (K := K) S v), by
      ext w
      exact divisorCoordinate_primePowerSUnit S v w⟩⟩

private theorem divisorRangeVector_linearIndependent :
    LinearIndependent ℤ (divisorRangeVector S) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have hv := congrArg
    (fun z : LinearMap.range (divisorLinearMap (K := K) S) =>
      ((z : S → ℤ) v)) hg
  simp [divisorRangeVector, classNumberBasisVector] at hv
  exact hv.resolve_right (NumberField.classNumber_ne_zero K)

/-- The divisor-map range on `S`-units has rank equal to the number of
places in `S`. -/
theorem finrank_divisor_range :
    Module.finrank ℤ
        (LinearMap.range (divisorLinearMap S)) =
      S.card := by
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  let :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap S)))
  apply le_antisymm
  · simpa using Submodule.finrank_le (LinearMap.range (divisorLinearMap S))
  · simpa using
      (divisorRangeVector_linearIndependent S).fintype_card_le_finrank

/-- The additive group of `S`-units is finitely generated over `ℤ`. -/
theorem moduleFinite :
    Module.Finite ℤ (Additive (SUnitGroup S)) := by
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  have :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap S)))
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (divisorLinearMap S) ?_ ?_
  · apply IsNoetherian.noetherian
  · rw [inf_of_le_right le_top,
      ← range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
         S]
    apply Submodule.fg_range

/-- The kernel of the `S`-unit divisor map has the ordinary unit rank. -/
theorem finrank_divisor_ker :
    Module.finrank ℤ
        (LinearMap.ker (divisorLinearMap S)) =
      NumberField.Units.rank K := by
  calc
    Module.finrank ℤ
        (LinearMap.ker (divisorLinearMap S)) =
        Module.finrank ℤ
          (LinearMap.range
            (fromNumberFieldUnitsLinearMap S)) :=
      (LinearEquiv.ofEq _ _
        (range_fromNumberFieldUnitsLinearMap_eq_ker_divisorLinearMap
           S).symm).finrank_eq
    _ = Module.finrank ℤ (Additive (𝓞 K)ˣ) :=
      (LinearEquiv.ofInjective
        (fromNumberFieldUnitsLinearMap S)
        (fromNumberFieldUnitsLinearMap_injective S)).symm.finrank_eq
    _ = NumberField.Units.rank K :=
      NumberField.Units.finrank_eq K

/-- The free rank of the `S`-unit group is the ordinary Dirichlet rank plus
the number of finite places in `S`. -/
theorem finrank :
    Module.finrank ℤ (Additive (SUnitGroup S)) =
      NumberField.Units.rank K + S.card := by
  let :=
    moduleFinite S
  let : Module.Finite ℤ (S → ℤ) := inferInstance
  let :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.range (divisorLinearMap S)))
  let :=
    Module.Finite.of_fg
      (IsNoetherian.noetherian
        (LinearMap.ker (divisorLinearMap S)))
  have hrank :
      Module.rank ℤ (Additive (SUnitGroup S)) =
        Module.rank ℤ
            (LinearMap.range (divisorLinearMap S)) +
          Module.rank ℤ
            (LinearMap.ker (divisorLinearMap S)) := by
    have h :=
      LinearMap.rank_eq_of_surjective

        (divisorLinearMap S).surjective_rangeRestrict
    rw [LinearMap.ker_rangeRestrict] at h
    exact h
  have hcard :
      (Module.finrank ℤ
          (Additive (SUnitGroup S)) : Cardinal) =
        (Module.finrank ℤ
            (LinearMap.range (divisorLinearMap S)) : Cardinal) +
          (Module.finrank ℤ
            (LinearMap.ker (divisorLinearMap S)) : Cardinal) := by
    rw [Module.finrank_eq_rank, Module.finrank_eq_rank,
      (LinearMap.ker (divisorLinearMap S)).finrank_eq_rank]
    exact hrank
  rw [← Nat.cast_inj (R := Cardinal), Nat.cast_add]
  calc
    (Module.finrank ℤ
        (Additive (SUnitGroup S)) : Cardinal) =
      (Module.finrank ℤ
          (LinearMap.range (divisorLinearMap S)) : Cardinal) +
        (Module.finrank ℤ
          (LinearMap.ker (divisorLinearMap S)) : Cardinal) :=
      hcard
    _ = (S.card : Cardinal) +
        (NumberField.Units.rank K : Cardinal) := by
      rw [finrank_divisor_range S,
        finrank_divisor_ker S]
    _ = (NumberField.Units.rank K : Cardinal) +
        (S.card : Cardinal) := by rw [add_comm]

end Rank

end SUnitGroup

end
