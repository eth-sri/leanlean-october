module
public import OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
public import OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic
open ActualEisensteinCubic
open EisensteinEmbedding ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic

open scoped Classical SchwartzMap FourierTransform
namespace EisensteinSchwartzPoisson

open ActualEisensteinCubic

open ActualEisensteinCubic QuadraticInitialBound

end EisensteinSchwartzPoisson

namespace FirstPassCubeLabels
open ActualEisensteinCubic MixedCrossSeparation FirstCauchyArithmetic RayFourExpansion

section
variable {ι : Type*} (p : ι → ActualEisensteinCubic.O)
include ι p
theorem supportRay_star (χ : RayCharacter) (S : Finset ι) :
    supportRay p (star χ) S = star (supportRay p χ S) := by aesop

theorem supportRay_mul (χ η : RayCharacter) (S : Finset ι) :
    supportRay p (χ * η) S = supportRay p χ S * supportRay p η S := by aesop
end

theorem columnG_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnG p hp hcop hg S = ∑ χ : RayCharacter, gCoeff χ * supportRay p χ S := by
  have h := canonicalProductG_character_expansion (fun i : S => p i.val)
    (fun i => hp i.val) (columnPrimeCoprime p hcop S) (fun i => hg i.val)
    (fun i => hc i.val) (fun i => hpr i.val)
  simpa only [columnG, supportRay, Finset.prod_coe_sort] using h

def coreRayCharacter (negative : Bool) (χ ξ : RayCharacter) : RayCharacter :=
  (if negative then star χ else χ) * ξ

def coreRayCoefficient {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) : ℂ :=
  (if negative then star (crossCoeff χ η * supportRay p η F)
    else crossCoeff χ η * supportRay p η F) * gCoeff ξ

section
variable {ι : Type*}
include ι
theorem core_phase_ray_expansion [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F S : Finset ι) (negative : Bool) :
    (if negative then star (fixedRayExpansion p F S) else fixedRayExpansion p F S) *
        columnG p hp hcop hg S =
      ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        coreRayCoefficient p F negative χ η ξ * supportRay p (coreRayCharacter negative χ ξ) S := by
  rw [columnG_ray_expansion p hp hcop hg hc hpr S]
  cases negative <;> simp only [Bool.false_eq_true,  ite_false, ite_true,
    fixedRayExpansion, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
    coreRayCoefficient, coreRayCharacter, supportRay_mul, supportRay_star]
  pm_3247
  pm_3247

theorem coreRayCoefficient_norm_le (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) :
    ‖coreRayCoefficient p F negative χ η ξ‖ ≤ ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
  have hη : ‖supportRay p η F‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one η _
  have hmul : ‖crossCoeff χ η‖ * ‖supportRay p η F‖ ≤ ‖crossCoeff χ η‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hη
  cases negative <;> simp only [coreRayCoefficient, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star]
  all_goals exact mul_le_mul_of_nonneg_right hmul (norm_nonneg _)

theorem coreRayCoefficient_mass (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
      ‖coreRayCoefficient p F negative χ η ξ‖) ≤ 32 * 512 := by
  calc
    _ ≤ ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
      gcongr with χ _ η _ ξ _
      exact coreRayCoefficient_norm_le p F negative χ η ξ
    _ = (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ ξ : RayCharacter, ‖gCoeff ξ‖) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ 512 * 32 := mul_le_mul crossCoeff_sum_norm_le gCoeff_sum_norm_le (by positivity) (by norm_num)
    _ = 32 * 512 := by ring
end

def coreRayTwist (negative : Bool) (χ ξ : RayCharacter) : ActualEisensteinCubic.O →* ℂ where
  toFun a := rayCharacter (coreRayCharacter negative χ ξ) a
  map_one' := by simp [rayCharacter]
  map_mul' a b := rayCharacter_mul _ a b

@[simp] theorem coreRayTwist_prod {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (S : Finset ι) (negative : Bool) (χ ξ : RayCharacter) :
    coreRayTwist negative χ ξ (∏ i ∈ S, p i) =
      supportRay p (coreRayCharacter negative χ ξ) S := rfl

end FirstPassCubeLabels

open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)

section FixedColumn
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
  (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
  (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)

def dilatedCoreRow (t : ℝ) (z : O) : ℂ :=
  dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
    negative χ p B v ε₁ ε₂ c d z

end FixedColumn

end FirstPassCubeLabels

end

end OAI
