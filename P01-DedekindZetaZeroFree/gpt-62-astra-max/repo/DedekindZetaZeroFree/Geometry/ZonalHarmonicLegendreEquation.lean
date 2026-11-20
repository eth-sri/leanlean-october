module
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SphericalHarmonics.RotationLaplacian

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.LatitudeDisintegration
public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.SmoothPolynomialDensity

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
open MeasureTheory KPCplxIntertwinerEigenvalues MvPolynomial
open scoped BigOperators

noncomputable def rot (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :=
  X (i + 1) * pderiv (i + 2) p - X (i + 2) * pderiv (i + 1) p
section

variable (p : MvPolynomial (Fin 3) ℂ)

noncomputable def euler :=
  ∑ i : Fin 3, X i * pderiv i p
noncomputable def casOp :=
  -(∑ i : Fin 3, rot i (rot i p))
private theorem casimir :
    casOp p = euler (euler p) + euler p -
      (∑ i : Fin 3, X i ^ 2) * polynomialLaplacian p := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.casimir <;> assumption

end
private theorem casOp_eigen (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) :
    casOp p = ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) • p := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.casOp_eigen <;> assumption
private theorem rot_X (i j : Fin 3) (x : Ambient) :
    eval (fun k => (x k : ℂ)) (rot i (X j)) = ((rotationVector i x) j : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [rot, pderiv_X, Pi.single_apply, rotationVector, Fin.reduceAdd]
section

variable (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ)

private theorem rot_eval_flow
    (x : Ambient) (t : ℝ) :
    HasDerivAt (fun t => eval (fun j => ((rotationFlow i t x) j : ℂ)) p)
      (eval (fun j => ((rotationFlow i t x) j : ℂ)) (rot i p)) t := by apply @DedekindZetaZeroFree.ComplexFractionalInverse.HarmonicIdentity.RotationLaplacian.rot_eval_flow <;> assumption
private theorem rot_zero
    (h : ∀ x : Sphere, polynomialSphere p x = 0) :
    ∀ x : Sphere, polynomialSphere (rot i p) x = 0 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.rot_zero <;> assumption

end
private theorem casOp_zero (p : MvPolynomial (Fin 3) ℂ)
    (h : ∀ x : Sphere, polynomialSphere p x = 0) :
    ∀ x : Sphere, polynomialSphere (casOp p) x = 0 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.casOp_zero <;> assumption
noncomputable def heightLift : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  Polynomial.aeval ((1 - X 0) * C (1 / 2))
private theorem pderiv_heightLift (i : Fin 3) (Q : Polynomial ℂ) :
    pderiv i (heightLift Q) = (if i = 0 then C (-1 / 2) else 0) *
      heightLift Q.derivative := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.pderiv_heightLift <;> assumption
private theorem casOp_heightLift (Q : Polynomial ℂ) :
    casOp (heightLift Q) =
      -(X 1 ^ 2 + X 2 ^ 2) * C (1 / 4) * heightLift Q.derivative.derivative -
        X 0 * heightLift Q.derivative := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.casOp_heightLift <;> assumption
private theorem casOp_sub (p q : MvPolynomial (Fin 3) ℂ) :
    casOp (p - q) = casOp p - casOp q := by
  simp only [casOp, rot, map_sub, mul_sub, Fin.sum_univ_three]
  ring
private theorem eval_heightLift (Q : Polynomial ℂ) (x : Fin 3 → ℂ) :
    eval x (heightLift Q) = Q.eval ((1 - x 0) / 2) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.eval_heightLift <;> assumption
private theorem sphere_radius (x : Sphere) :
    ((x : Ambient) 0 : ℂ) ^ 2 + ((x : Ambient) 1 : ℂ) ^ 2 +
      ((x : Ambient) 2 : ℂ) ^ 2 = 1 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.sphere_radius <;> assumption

theorem zonal_harmonic_legendre_ode (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (Q : Polynomial ℂ)
    (hQ : ∀ x : Sphere, polynomialSphere p x =
      Q.eval ((1 - ((x : Ambient) 0 : ℂ)) / 2)) :
    Polynomial.X * (1 - Polynomial.X) * Q.derivative.derivative +
      (1 - 2 * Polynomial.X) * Q.derivative +
      Polynomial.C ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * Q = 0 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.zonal_harmonic_legendre_ode <;> assumption

section

variable (A : Matrix (Fin 3) (Fin 3) ℂ)

noncomputable def spinSubst :
    MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j)

private theorem pderiv_spinSubst
    (p : MvPolynomial (Fin 3) ℂ) (j : Fin 3) :
    MvPolynomial.pderiv j (spinSubst A p) =
      ∑ i, MvPolynomial.C (A i j) * spinSubst A (MvPolynomial.pderiv i p) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.pderiv_linearSubstitution <;> assumption

private theorem polynomialLaplacian_spinSubst
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    polynomialLaplacian (spinSubst A p) = spinSubst A (polynomialLaplacian p) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.polynomialLaplacian_linearSubstitution <;> assumption

private theorem spinSubst_homogeneous
    (p : MvPolynomial (Fin 3) ℂ) (ℓ : ℕ) (hp : p.IsHomogeneous ℓ) :
    (spinSubst A p).IsHomogeneous ℓ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.linearSubstitution_homogeneous <;> assumption

private theorem spinSubst_harmonic
    (hA : ∀ i k, ∑ j, A i j * A k j = if i = k then 1 else 0)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ) :
    spinSubst A p ∈ harmonicPolynomials ℓ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.linearSubstitution_harmonic <;> assumption

end

noncomputable def spinMatrix (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1,0,0], ![0,(Real.cos t : ℂ),-(Real.sin t : ℂ)],
    ![0,(Real.sin t : ℂ),(Real.cos t : ℂ)]]
private theorem spinMatrix_orthogonal (t : ℝ) (i k : Fin 3) :
    ∑ j, spinMatrix t i j * spinMatrix t k j = if i = k then 1 else 0 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.spinMatrix_orthogonal <;> assumption
private theorem spinSubst_eval (t : ℝ) (p : MvPolynomial (Fin 3) ℂ) (x : Ambient) :
    eval (fun j => (x j : ℂ)) (spinSubst (spinMatrix t) p) =
      eval (fun j => ((rotationFlow 0 t x) j : ℂ)) p := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.spinSubst_eval <;> assumption
instance sphere_compact : CompactSpace Sphere :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient) 1)
noncomputable def polyCM : MvPolynomial (Fin 3) ℂ →ₗ[ℂ] C(Sphere, ℂ) where
  toFun p := ⟨polynomialSphere p, (MvPolynomial.continuous_eval p).comp (by fun_prop)⟩
  map_add' p q := by ext x; change polynomialSphere (p + q) x = polynomialSphere p x + polynomialSphere q x; simp [polynomialSphere]
  map_smul' c p := by ext x; change polynomialSphere (c • p) x = c • polynomialSphere p x; simp [polynomialSphere]
section

variable (p : MvPolynomial (Fin 3) ℂ)

noncomputable def spinCM (t : ℝ) : C(Sphere, ℂ) :=
  ⟨fun x => polynomialSphere p (sphereOrthogonal (rotationFlow 0 t) x),
    (polyCM p).continuous.comp (sphereOrthogonal (rotationFlow 0 t)).continuous⟩
private theorem spinCM_continuous : Continuous (spinCM p) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply (MvPolynomial.continuous_eval p).comp
  apply continuous_pi
  intro j
  fin_cases j <;> simp [rotationFlowMap] <;> fun_prop
private theorem spinCM_integrable :
    Integrable (spinCM p) angleMeasure :=
  (spinCM_continuous p).integrableOn_Icc.smul_measure (by
    simp [ENNReal.inv_ne_top]; positivity)

end
private theorem average_harmonic (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) :
    ∃ q ∈ harmonicPolynomials ℓ, ∀ x : Sphere,
      polynomialSphere q x = ∫ t, polynomialSphere p
        (sphereOrthogonal (rotationFlow 0 t) x) ∂angleMeasure := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.average_harmonic <;> assumption

private alias latitude_surjective_aux := DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.LatitudeDisintegration.latitude_surjective

private lemma angle_shift_aux (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi))
    (θ : ℝ) :
    (∫ t, f (θ + t) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.shift <;> assumption

private theorem latitude_flow (u θ t : ℝ) :
    sphereOrthogonal (rotationFlow 0 t) (latitudePoint (.refl ℝ Ambient) u θ) =
      latitudePoint (.refl ℝ Ambient) u (θ + t) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.PolynomialFunkHecke.latitude_flow <;> assumption
private alias latitude_periodic_aux := DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.LatitudeDisintegration.latitude_periodic

theorem latitude_average_legendre_ode (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials ℓ) (Q : Polynomial ℂ)
    (hQ : ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (∫ θ : ℝ, polynomialSphere p
        (latitudePoint (.refl ℝ Ambient) u θ) ∂angleMeasure) = Q.eval (u : ℂ)) :
    Polynomial.X * (1 - Polynomial.X) * Q.derivative.derivative +
      (1 - 2 * Polynomial.X) * Q.derivative +
      Polynomial.C ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) * Q = 0 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.CircleAverage.latitude_average_legendre_ode <;> assumption

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke.CircleAverage
