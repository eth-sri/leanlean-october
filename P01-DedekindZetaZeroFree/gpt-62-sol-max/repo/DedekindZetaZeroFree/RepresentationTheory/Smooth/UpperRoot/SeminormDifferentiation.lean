module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.ComplexIntertwinerImageAndHarmonicExtraction

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.OrbitDifferentiation

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxUpperRootSeminormDifferentiation

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open Filter Topology
open scoped Matrix.Norms.Elementwise

private lemma upper_zero : upperUnipotent 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent]
theorem upperRoot_differenceQuotient_chartSeminorm_of_pointwise
    (β : ℂˣ) (e : Theta β) (v : ℂ)
    (D : PrincipalSeries negativeParameter)
    (hD : ∀ g : ComplexGL2,
      HasDerivAt (fun t : ℝ => (e : PrincipalSeries negativeParameter)
        (g * upperUnipotent ((t : ℂ) * v))) (D g) 0)
    (n : ℕ) :
    Tendsto (fun t : ℝ => chartSeminorm negativeParameter n
      ((((t⁻¹ : ℂ) •
        (imageAction β (Matrix.ProjGenLinGroup.mk
          (upperUnipotent ((t : ℂ) * v))) e - e) : Theta β) :
          PrincipalSeries negativeParameter) - D))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let γ := fun t : ℝ => upperUnipotent ((t : ℂ) * v)
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)) :=
    KPCplxLoweringOrbitDifferentiation.contDiff_upperUnipotent.comp
      (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hz : γ 0 = 1 := by simp [γ, upper_zero]
  simpa only [Submodule.coe_smul_of_tower, Submodule.coe_sub, imageAction_coe, pi_mk] using
    KPCplxLoweringOrbitDifferentiation.orbit_quotient_seminorm_tendsto
      negativeParameter γ hγ hz e D hD n

end DedekindZetaZeroFree.KPCplxUpperRootSeminormDifferentiation
