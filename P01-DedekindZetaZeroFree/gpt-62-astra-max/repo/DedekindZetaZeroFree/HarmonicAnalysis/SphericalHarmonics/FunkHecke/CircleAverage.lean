module

public import DedekindZetaZeroFree.Geometry.HarmonicPolynomialLatitudeAverage
public import DedekindZetaZeroFree.Geometry.ZonalHarmonicLegendreEquation

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke
open MeasureTheory KPCplxIntertwinerEigenvalues
open scoped RealInnerProductSpace

instance angleMeasure_isProbabilityMeasure : IsProbabilityMeasure angleMeasure := by
  constructor
  rw [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc]
  simp only [sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr
    (mul_pos (by norm_num) Real.pi_pos))) ENNReal.ofReal_ne_top

@[simp] theorem latitudePoint_zero_val (g : Ambient ≃ₗᵢ[ℝ] Ambient) (θ : ℝ) :
    (latitudePoint g 0 θ : Ambient) = g north := by
  rw [latitudePoint_val _ _ _ (by norm_num)]
  apply congrArg g
  rw [WithLp.ext_iff]
  funext i
  fin_cases i <;> simp [latitudeAmbient, north, PiLp.single_apply]

theorem harmonic_latitude_average_north (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    (∫ θ : ℝ, polynomialSphere p (latitudePoint g 0 θ) ∂angleMeasure) =
      ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) 0 : ℝ) *
        polynomialSphere p ⟨g north,
          mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩ := by
  simp [polynomialSphere, integral_const, Polynomial.coeff_shiftedLegendre]

section

variable (A : Matrix (Fin 3) (Fin 3) ℂ)

noncomputable def linearSubstitution :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)

theorem pderiv_linearSubstitution
    (p : MvPolynomial (Fin 3) ℂ) (j : Fin 3) :
    MvPolynomial.pderiv j (linearSubstitution A p) =
      ∑ i, MvPolynomial.C (A i j) * linearSubstitution A (MvPolynomial.pderiv i p) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.pderiv_linearSubstitution <;> assumption

theorem polynomialLaplacian_linearSubstitution
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (linearSubstitution A p) = linearSubstitution A (polynomialLaplacian p) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.polynomialLaplacian_linearSubstitution <;> assumption

theorem linearSubstitution_homogeneous
    (p : MvPolynomial (Fin 3) ℂ) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) :
    (linearSubstitution A p).IsHomogeneous ℓ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.linearSubstitution_homogeneous <;> assumption

theorem linearSubstitution_harmonic
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ) :
    linearSubstitution A p ∈ harmonicPolynomials ℓ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.linearSubstitution_harmonic <;> assumption

end

section

variable (g : Ambient ≃ₗᵢ[ℝ] Ambient)

noncomputable def orthogonalSubstitutionMatrix :
    Matrix (Fin 3) (Fin 3) ℂ := fun i j => (g.symm (EuclideanSpace.single i 1)) j

theorem orthogonalSubstitutionMatrix_orthogonal (i k : Fin 3) :
    ∑ j, orthogonalSubstitutionMatrix g i j * orthogonalSubstitutionMatrix g k j =
      if i = k then 1 else 0 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.orthogonalSubstitutionMatrix_orthogonal <;> assumption

theorem orthogonalSubstitutionMatrix_eval (v : Ambient) (i : Fin 3) :
    ∑ j, orthogonalSubstitutionMatrix g i j * (v j : ℂ) = ((g v) i : ℂ) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.orthogonalSubstitutionMatrix_eval <;> assumption

theorem orthogonalSubstitution_eval
    (p : MvPolynomial (Fin 3) ℂ) (v : Ambient) :
    MvPolynomial.eval (fun j => (v j : ℂ)) (linearSubstitution (orthogonalSubstitutionMatrix g) p) =
      MvPolynomial.eval (fun i => ((g v) i : ℂ)) p := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.orthogonalSubstitution_eval <;> assumption

theorem orthogonalSubstitution_latitude
    (p : MvPolynomial (Fin 3) ℂ) (u θ : ℝ) :
    polynomialSphere (linearSubstitution (orthogonalSubstitutionMatrix g) p)
      (latitudePoint (.refl ℝ Ambient) u θ) = polynomialSphere p (latitudePoint g u θ) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.orthogonalSubstitution_latitude <;> assumption

end

theorem harmonic_latitude_average_of_standardFrame (ℓ : ℕ)
    (hstandard : ∀ q : MvPolynomial (Fin 3) ℂ, q ∈ harmonicPolynomials ℓ →
      ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere q (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) =
        ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
          polynomialSphere q ⟨north, mem_sphere_zero_iff_norm.mpr north_norm⟩)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ)
    (g : Ambient ≃ₗᵢ[ℝ] Ambient) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere p (latitudePoint g u θ) ∂angleMeasure) =
        ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
          polynomialSphere p ⟨g north,
            mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.harmonic_latitude_average_of_standardFrame <;> assumption

theorem harmonic_latitude_average (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∫ θ : ℝ, polynomialSphere p (latitudePoint g u θ) ∂angleMeasure) =
      ((Polynomial.shiftedLegendre ℓ).eval₂ (Int.castRingHom ℝ) u : ℝ) *
        polynomialSphere p ⟨g north,
          mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.harmonic_latitude_average <;> assumption

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke
