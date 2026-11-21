module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalIncompleteSeries
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.Domain

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PoissonKernel

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rawRowFactor (u : D.Row) (ξ w z : ℂ) : ℂ :=
  comparisonEulerPoissonSeries F D.recipe.A D.recipe.probe.coefficients (FixedData.Row.u u) ξ w z

def rowFactor (u : D.Row) (ξ w z : ℂ) : ℂ :=
  D.zetaSCont (6 * z) * D.Lpsi u w / D.Llam u ξ * EulerDomain.Hu D u ξ w z

section RowFactorAux

open DedekindZetaZeroFree.MaskedHeckeMeromorphic LocalFiniteSums CorrectionFactors FrequencyCharacterMasks
open IsDedekindDomain Filter
open scoped NumberField Topology

variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η' : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η' hS}

private lemma rf_row_matches (U : Frequency C) (s : ℂ) :
    incompleteL U .principal s = InitialSeparatedEuler.zetaS A s ∧
    incompleteL U .plus s = InitialSeparatedEuler.plusL U s ∧
    incompleteL U .minus s = InitialSeparatedEuler.minusL U s := by
  have hsupport (i : Row) : Function.support (fun I : Ideal (𝓞 F) =>
      coefficient U i I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
    intro I hI
    by_contra hn
    change ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) at hn
    apply hI
    cases i <;> simp [coefficient, principalCoefficient, plusCoefficient, minusCoefficient, hn]
  have he (i : Row) := (tsum_subtype_eq_of_support_subset (hsupport i)).symm
  refine ⟨?_, ?_, ?_⟩
  · change incompleteL U .principal s = _
    rw [show incompleteL U .principal s = _ from he .principal]
    unfold InitialSeparatedEuler.zetaS
    apply tsum_congr
    intro I
    simp [coefficient, principalCoefficient, I.property.1, I.property.2]
  · change incompleteL U .plus s = _
    rw [show incompleteL U .plus s = _ from he .plus]
    unfold InitialSeparatedEuler.plusL InitialSeparatedEuler.dirichletSeries
    apply tsum_congr
    intro I
    simp [coefficient, plusCoefficient, I.property.1, I.property.2, InitialSeparatedEuler.plusL,
      InitialSeparatedEuler.dirichletSeries, ExteriorIdealEuler.summand]
  · change incompleteL U .minus s = _
    rw [show incompleteL U .minus s = _ from he .minus]
    unfold InitialSeparatedEuler.minusL InitialSeparatedEuler.dirichletSeries
    apply tsum_congr
    intro I
    simp [coefficient, plusCoefficient, minusCoefficient, I.property.1, I.property.2,
      minusExteriorCoefficient, ExteriorIdealEuler.summand]

end RowFactorAux

theorem rowFactor_eq_raw (u : D.Row) (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re)
    (hz : 2 < z.re) : rowFactor D u ξ w z = rawRowFactor D u ξ w z := by
  have hξ1 : 1 < ξ.re := by linarith
  have hw1 : 1 < w.re := by linarith
  have hz1 : 1 < (6 * z).re := by simp; linarith
  have hD := DedekindZetaZeroFree.PrincipalMellinComparison.principal_arithmetic_compatibility D.recipe D.context rfl
  have hQ := InitialSeparatedEuler.initial_separated_euler_quotient u.toFrequency
    D.recipe.probe.coefficients hD ξ w z hξ hw hz
  have hL := D.recipe.L_eq_zeta (6 * z) hz1
  have hP : D.Lpsi u w = InitialSeparatedEuler.plusL u.toFrequency w := by
    rw [FixedData.Lpsi_eq_raw D u w hw1]
    exact (rf_row_matches u.toFrequency w).2.1
  have hM : D.Llam u ξ = InitialSeparatedEuler.minusL u.toFrequency ξ := by
    rw [FixedData.Llam_eq_raw D u ξ hξ1]
    exact (rf_row_matches u.toFrequency ξ).2.2
  unfold rowFactor rawRowFactor
  rw [show FixedData.Row.u u = u.toFrequency.u from rfl, hQ]
  unfold FixedData.zetaSCont EulerDomain.Hu CorrectionFactors.H_u
  rw [hL, hP, hM]
  ring

def kernelWith (Fu : D.Row → ℂ → ℂ → ℂ → ℂ) (u : D.Row) (ξ w z : ℂ) (Z : ℝ) : ℂ :=
  (Z : ℂ) ^ ((Scales.xExponent / 2 : ℝ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z + (Scales.yExponent : ℂ) * (w - 1)) *
    Complex.exp ((ξ + z - 1) ^ 2) * D.M z * D.W1Hat w * (D.q u : ℂ) ^ (-z) * Fu u ξ w z

def K (u : D.Row) (ξ w z : ℂ) (Z : ℝ) : ℂ := kernelWith D (rowFactor D) u ξ w z Z

def wzIntegral (u : D.Row) (ξ : ℂ) (y v Z : ℝ) : ℂ :=
  comparisonVerticalIntegral y (fun w =>
    comparisonVerticalIntegral v (fun z => K D u ξ w z Z))

def J (C : Set D.Row) (x y v Z : ℝ) : ℂ :=
  ∑ᶠ u ∈ C, comparisonVerticalIntegral x (fun ξ => wzIntegral D u ξ y v Z)

def principalRows : Set D.Row := {u | FixedData.Row.u u = 1}

def Jpr (Z : ℝ) : ℂ := J D (principalRows D) 4 4 2 Z




end

end DedekindZetaZeroFree.Quantitative.PoissonKernel
