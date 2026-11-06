module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Rational quadratic reciprocity from global class field theory

The dyadic correction specializes power-residue reciprocity over `ℚ` and
derives Gauss's quadratic reciprocity law.
-/

open scoped BigOperators Classical NumberField NumberTheorySymbols ValuativeRel WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

-- Specializing the generic completion construction to `ℚ` must keep the
-- `Algebra.id` owner fixed.  Otherwise the rational-field algebra path is
-- underdetermined during instance synthesis.
@[reducible] noncomputable local instance
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (HeightOneSpectrum.adicAbv ℚ v).Completion := by
  letI : Algebra ℚ ℚ := Algebra.id ℚ
  let hWith : Algebra ℚ
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) :=
    WithAbs.instAlgebra _
  let hUniform : UniformContinuousConstSMul ℚ
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) :=
    WithAbs.instUniformContinuousConstSMulReal _
  exact
    @UniformSpace.Completion.algebra
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) _ _ _ _
      ℚ _ hWith hUniform

open KummerTheory
open AlgebraicNumberTheory.PowerResidueSymbols
open LocalClassFieldTheory.Kummer
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

 

/-! ## Dyadic correction and Gauss reciprocity -/



 



/-- A natural number in the rational ring of integers. -/
noncomputable def rationalNatInteger (m : ℕ) : 𝓞 ℚ :=
  Rat.ringOfIntegersEquiv.symm (m : ℤ)

@[simp]
theorem rationalNatInteger_equiv (m : ℕ) :
    Rat.ringOfIntegersEquiv (rationalNatInteger m) = (m : ℤ) :=
  Rat.ringOfIntegersEquiv.apply_symm_apply (m : ℤ)

@[simp]
theorem rationalNatInteger_coe (m : ℕ) :
    (rationalNatInteger m : ℚ) = (m : ℚ) := by
  exact Rat.ringOfIntegersEquiv_symm_apply_coe (m : ℤ)

/-- A positive natural number, regarded canonically as a rational field unit. -/
noncomputable def rationalNaturalFieldUnit
    (m : ℕ) (hm : m ≠ 0) : ℚˣ :=
  nonzeroIntegralFieldUnit ℚ (rationalNatInteger m) (by
    intro h
    apply Int.ofNat_ne_zero.mpr hm
    simpa [rationalNatInteger_equiv] using
      congrArg Rat.ringOfIntegersEquiv h)

@[simp]
theorem rationalNaturalFieldUnit_coe
    (m : ℕ) (hm : m ≠ 0) :
    (rationalNaturalFieldUnit m hm : ℚ) = (m : ℚ) := by
  exact rationalNatInteger_coe m

/-- The negative quadratic integral root of unity over `ℚ`. -/
def rationalQuadraticNegOneRoot : rootsOfUnity 2 (𝓞 ℚ) :=
  ⟨-1, by norm_num⟩

@[simp]
theorem rationalQuadraticRootValue_negOneRoot :
    rationalQuadraticRootValue rationalQuadraticNegOneRoot = -1 := by
  simp [rationalQuadraticRootValue, rationalQuadraticNegOneRoot]





/-- The sign-normalized odd integer used in the dyadic square-class
calculation, regarded as a unit of `ℚ₂`. -/
noncomputable def rationalTwoAdicSignedOddUnit
    (m : ℕ) (hm : Odd m) : ℚ_[2]ˣ :=
  Units.mk0
    ((((-1 : ℤ) ^ (m / 2) * (m : ℤ)) : ℤ) : ℚ_[2]) (by
      exact_mod_cast
        mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0))
          (Int.ofNat_ne_zero.mpr (by
            intro hm0
            subst m
            norm_num at hm)))

@[simp]
theorem rationalTwoAdicSignedOddUnit_coe
    (m : ℕ) (hm : Odd m) :
    (rationalTwoAdicSignedOddUnit m hm : ℚ_[2]) =
      (((-1 : ℤ) ^ (m / 2) * (m : ℤ) : ℤ) : ℚ_[2]) :=
  rfl









private theorem localHilbertSymbol_mul_left
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (x y z : Fˣ) :
    localHilbertSymbol F n hnF hmu (x * y) z =
      localHilbertSymbol F n hnF hmu x z *
        localHilbertSymbol F n hnF hmu y z := by
  change
    localHilbertSymbolHom F n hnF hmu z (x * y) =
      localHilbertSymbolHom F n hnF hmu z x *
        localHilbertSymbolHom F n hnF hmu z y
  exact map_mul (localHilbertSymbolHom F n hnF hmu z) x y















/-- The rational global field unit represented by `-1`. -/
def rationalQuadraticNegOneFieldUnit : ℚˣ :=
  nonzeroIntegralFieldUnit ℚ (-1 : 𝓞 ℚ) (by norm_num)

@[simp]
theorem rationalQuadraticNegOneFieldUnit_coe :
    (rationalQuadraticNegOneFieldUnit : ℚ) = -1 :=
  rfl























end Reciprocity
end GlobalClassFieldTheory

end
