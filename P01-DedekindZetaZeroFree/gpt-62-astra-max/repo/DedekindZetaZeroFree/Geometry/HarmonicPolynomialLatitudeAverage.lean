module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.LatitudeDisintegration
public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.SmoothPolynomialDensity

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
open MeasureTheory KPCplxIntertwinerEigenvalues
open scoped BigOperators

private lemma shift (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) (θ : ℝ) :
    (∫ t, f (θ + t) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.shift <;> assumption
noncomputable def moment (i j : ℕ) : ℂ :=
  ∫ θ : ℝ, (Real.cos θ : ℂ)^i * (Real.sin θ : ℂ)^j ∂angleMeasure
private lemma moment_odd (i j : ℕ) (h : Odd (i+j)) : moment i j = 0 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.moment_odd <;> assumption
section

variable (d : Fin 3 →₀ ℕ) (a : ℂ)

private lemma mono_formula (u θ : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    polynomialSphere (MvPolynomial.monomial d a) (latitudePoint (.refl ℝ Ambient) u θ) =
      a * ((1-2*u : ℝ):ℂ)^(d 0) * (Real.sqrt (4*u*(1-u)) : ℂ)^(d 1+d 2) *
        ((Real.cos θ : ℂ)^(d 1) * (Real.sin θ : ℂ)^(d 2)) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.mono_formula <;> assumption
private lemma mono_integral (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere (MvPolynomial.monomial d a)
      (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) =
      a * ((1-2*u : ℝ):ℂ)^(d 0) * (Real.sqrt (4*u*(1-u)) : ℂ)^(d 1+d 2) * moment (d 1) (d 2) := by
  simp_rw [mono_formula d a u _ hu]
  exact integral_const_mul _ _

end
variable (p : MvPolynomial (Fin 3) ℂ)

private lemma poly_integrable (u : ℝ)
    (hu : u ∈ Set.Icc (0:ℝ) 1) :
    Integrable (fun θ => polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ)) angleMeasure := by
  have hc : Continuous (fun θ => polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ)) := by
    simp only [polynomialSphere, latitudePoint_val _ _ _ hu]
    apply (MvPolynomial.continuous_eval p).comp
    apply continuous_pi
    intro i
    fin_cases i <;> change Continuous _ <;> dsimp [latitudeAmbient]
    all_goals fun_prop
  exact (hc.integrableOn_Icc).smul_measure (by simp [ENNReal.inv_ne_top]; positivity)
private lemma exists_profile :
    ∃ Q : Polynomial ℂ, ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere p (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u:ℂ) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.exists_profile <;> assumption

theorem latitude_average_polynomial :
    ∃ Q : Polynomial ℂ,
      (∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
        (∫ θ : ℝ, polynomialSphere p
          (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u : ℂ)) ∧
      Q.eval 0 = polynomialSphere p
        ⟨north, mem_sphere_zero_iff_norm.mpr north_norm⟩ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.latitude_average_polynomial <;> assumption

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
