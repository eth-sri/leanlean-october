/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Defs.Rho
public import DOZZ.Statements.Defs.ExtendedSeiberg3
public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.GMC.Construction.RootedCircleMassLimit
import DOZZ.Correlations.Residue.ChartMass
import DOZZ.ShiftEquations.Mobius.InversionMoment
@[expose] public section
open MeasureTheory Set
open scoped Distributions ENNReal
namespace DOZZ.Proofs
section
variable (γ α₁ α₂ α₃ : ℝ)


end

/-- Every GMC version has the rho/Coulomb identity almost surely. -/
theorem gmc_rho_eq_coulombMass_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) :
    ∀ᵐ ω ∂P, rho γ (M ω) α₁ α₂ α₃ =
      coulombMass γ (M ω) ![α₁, α₂] ![0, 1] α₃ := by
  filter_upwards [DOZZ.Proofs.gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 0,
    DOZZ.Proofs.gmc_atomless_of_isGMCOf P X hX γ hγ hγ2 M hM 1] with ω h0 h1
  exact DOZZ.Proofs.residue_rho_eq_coulombMass γ α₁ α₂ α₃ (M ω) h0 h1
/-- The three-charge domain supplies every hypothesis of the global moment theorem. -/
theorem extendedSeiberg3_coulomb_parameters (γ α₁ α₂ α₃ : ℝ)
    (hα : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    (Function.Injective (![0, 1] : Fin 2 → ℂ)) ∧
    (∀ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k < Q γ) ∧ α₃ < Q γ ∧
    ((2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ =
      -sExp γ α₁ α₂ α₃) ∧
    ((2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ < 4 / γ ^ 2) ∧
    (∀ k : Fin 2, (2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ <
      2 / γ * (Q γ - (![α₁, α₂] : Fin 2 → ℝ) k)) ∧
    ((2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ <
      2 / γ * (Q γ - α₃)) := by
  obtain ⟨h₁, h₂, h₃, hp⟩ := hα
  have he : (2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂]) k) + α₃)) / γ =
      -sExp γ α₁ α₂ α₃ := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sExp]
    ring
  simp_all

/-- The target rho moment is exactly the specialized global Coulomb moment. -/
theorem rho_moment_eq_coulomb_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) :
    (∫⁻ ω, ENNReal.rpow (rho γ (M ω) α₁ α₂ α₃) (-sExp γ α₁ α₂ α₃) ∂P) =
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α₁, α₂] ![0, 1] α₃)
      ((2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ) ∂P := by
  have he : (2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂]) k) + α₃)) / γ =
      -sExp γ α₁ α₂ α₃ := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sExp]
    ring
  apply lintegral_congr_ae
  filter_upwards [gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃] with ω hω
  simp_all
end DOZZ.Proofs
