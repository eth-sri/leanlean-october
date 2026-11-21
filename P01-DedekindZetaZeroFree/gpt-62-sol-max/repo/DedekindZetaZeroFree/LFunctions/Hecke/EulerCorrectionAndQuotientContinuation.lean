module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalIncompleteSeries
public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalMaskedRowInducers
public import DedekindZetaZeroFree.Nonvanishing.Mellin.InitialFrequencyDecomposition
public import DedekindZetaZeroFree.Moments.Principal.EulerCorrectionsAndDoubleResidue
public import DedekindZetaZeroFree.Moments.Comparison.PoissonMellinKernelData
public import DedekindZetaZeroFree.Moments.Comparison.TripleMellinKernel

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open scoped Classical NumberField Topology
open IsDedekindDomain Filter
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem principal_coefficient_field_trace
    (R : PrincipalMellin.ActualRecipe S η) (x : F) :
    R.probe.coefficients.additiveCharacter x = (R.A.fieldTraceCharacter x : ℂ) := by
  rw [R.probe.sameTrace, PrincipalProbeConstruction.Inputs.fieldTrace_phase]
  congr 1
  funext v
  exact R.normalization.sameFiniteTrace v

private theorem principal_arithmetic_binding (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    PrincipalProbeConstruction.ArithmeticBinding R.A R.σ R.target R.traceBad
      C R.probe.allowed R.probe.coefficients := by
  refine ⟨R.probe.sameComplement.trans (congrArg (fun D => D.B) hC),
    R.probe.sameGenerator, R.probe.exteriorCharacters, ?_, R.probe.gammaTwo_recipe,
    R.probe.sixthUnitCharacters, principal_coefficient_field_trace R, ?_⟩
  · intro m
    rw [R.probe.theta_principal, hC]
  · intro x
    rw [principal_coefficient_field_trace R,
      PrincipalProbeConstruction.Inputs.fieldTrace_phase]

private theorem principal_arithmetic_compatibility (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (hC : R.probe.correction = C.correction) :
    WeightedFiniteCoefficient.ArithmeticCompatibility R.A R.probe.coefficients
      R.σ R.target R.traceBad C.correction := by
  exact PrincipalCorrection.probe_arithmetic_compatibility C R.probe hC
    (principal_arithmetic_binding R C hC)

theorem initial_continuation_agreement
    (R : PrincipalMellin.ActualRecipe S η)
    (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (plus minus : Frequency R → ℂ → ℂ)
    (hC : R.probe.correction = C.correction)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hplusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s)
    (hminusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      minus u s = AllRowEuler.InitialSeparation.minusL R.σ R.target (U u) s)
    (u : Frequency R) (ξ w z : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) (hz : z.re = 2) :
    separatedSeries R u ξ w z =
      (R.L (6 * z) * plus u w *
        AllRowEuler.InitialSeparation.correctionProduct C (U u) ξ w z) / minus u ξ := by
  have hD := principal_arithmetic_compatibility R C hC
  have h := AllRowEuler.InitialSeparation.initial_euler_quotient C R.probe.coefficients hD
    (U u) ξ w z hξ hw hz
  rw [hU u] at h
  rw [← R.L_eq_zeta (6 * z) (by norm_num [Complex.mul_re, hz])] at h
  rw [← hplusSeries u w (by rw [hw]; norm_num)] at h
  rw [← hminusSeries u ξ (by rw [hξ]; norm_num)] at h
  simpa only [separatedSeries, NormalizedProbe.principalSeparatedMellinSeries,
    NormalizedProbe.separatedMellinSeries] using h

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
open scoped Classical NumberField
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor
noncomputable section
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.Corridor

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
noncomputable section
open scoped Classical
open Filter Set Metric

set_option maxHeartbeats 1500000

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

variable (R : PrincipalMellin.ActualRecipe S η)
  (C : R.A.GeneralArithmeticContext R.σ R.target R.traceBad)
  (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
  (plus minus : Frequency R → ℂ → ℂ)

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation

end
