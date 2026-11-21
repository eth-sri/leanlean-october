module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicKTypes
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PGLComplex.BruhatHopfCoordinates
public import DedekindZetaZeroFree.MeasureTheory.Sphere.HeightDistribution
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SphereProjectionRotationInvariance

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open ComplexFractionalInverse.RawSphereProjection
open ComplexLocal.StereographicTransport
open scoped RealInnerProductSpace

noncomputable def rawPolynomialSphere (p : MvPolynomial (Fin 3) ℂ)
    (y : rawSphere) : ℂ :=
  MvPolynomial.eval (fun i => ((y : rawAmbient) i : ℂ)) p

noncomputable def rawLatitudeKernel (w : ℝ → ℝ) (x : rawSphere)
    (p : MvPolynomial (Fin 3) ℂ) (y : rawSphere) : ℂ :=
  (w ((1 - inner ℝ (x : rawAmbient) (y : rawAmbient)) / 2) : ℂ) *
    rawPolynomialSphere p y

private theorem coords_norm (k : ComplexSU2) :
    ‖(WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re) : rawAmbient)‖ = 1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup k.property)
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 1 1).re) hu
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Complex.mul_re, Complex.star_def, Complex.normSq_apply] at h
  have hs : ‖(WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re) : rawAmbient)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [compactSphereCoordinate, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im,
      Complex.star_def, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_nonneg (((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re ^ 2 +
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im ^ 2 +
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ^ 2 +
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im ^ 2 - 1)]
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re) : rawAmbient)]

theorem compact_section_spherical_transport (k : ComplexSU2) :
    ∃ (x : rawSphere) (q : ℂ → rawSphere),
      (∀ i : Fin 3, ((x : rawAmbient) i : ℂ) = compactSphereCoordinate k i) ∧
      MeasurePreserving q ComplexLocal.StereographicTransport.planeProbability
        rawSphereArea ∧
      (∀ (p : MvPolynomial (Fin 3) ℂ) (f : PrincipalSeries positiveParameter),
        (∀ h : ComplexSU2,
          f (complexSU2Embedding h) = MvPolynomial.eval (compactSphereCoordinate h) p) →
        ∀ z : ℂ, f (weyl * upperUnipotent z * complexSU2Embedding k) =
          (3 * Real.pi : ℂ) *
            (ComplexLocal.StereographicTransport.denominator z ^ (-2 : ℝ) / Real.pi : ℝ) *
            rawLatitudeKernel (fun u : ℝ => (1 / 3) * u ^ (1 / 3 - 1 : ℝ)) x p (q z)) := by
  let H : ComplexSU2 → rawSphere := fun h =>
    ⟨WithLp.toLp 2 (fun i => (compactSphereCoordinate h i).re),
      mem_sphere_zero_iff_norm.mpr (coords_norm h)⟩
  have hH : HasRawHopfCoordinates H := fun _ => rfl
  have hc (h : ComplexSU2) (i : Fin 3) :
      ((H h : rawAmbient) i : ℂ) = compactSphereCoordinate h i := by
    fin_cases i <;> simp [H, compactSphereCoordinate, ← Complex.ofReal_pow]
  refine ⟨H k, fun z => H (kappa z * k), hc k, ?_, ?_⟩
  · exact (positive_section_stereographic H hH 0 (fun _ => 0) (fun _ => rfl) k).1
  · intro p f hf
    have hp : ∀ h, KPCplxHarmonicIntertwinerSpectrum.compactRestriction positiveParameter f h =
        rawPolynomialSphere p (H h) := by
      intro h
      change f (complexSU2Embedding h) = _
      rw [hf]
      unfold rawPolynomialSphere
      rw [show (fun i => ((H h : rawAmbient) i : ℂ)) = compactSphereCoordinate h from funext (hc h)]
    intro z
    simpa only [rawLatitudeKernel, mul_assoc] using
      (positive_section_stereographic H hH f (rawPolynomialSphere p) hp k).2 z

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral
open MeasureTheory ComplexFractionalInverse.RawSphereProjection

theorem raw_polynomial_latitude_integrable (p : MvPolynomial (Fin 3) ℂ)
    (w : ℝ → ℝ) (hw : Integrable w (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (x : rawSphere) :
    Integrable (rawLatitudeKernel w x p) rawSphereArea := by
  let φ : rawSphere → ℝ := fun y => (1 - inner ℝ (x : rawAmbient) (y : rawAmbient)) / 2
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hkm : Integrable w (Measure.map φ rawSphereArea) := by
    rw [show Measure.map φ rawSphereArea = volume.restrict (Set.Icc (0 : ℝ) 1) from
      (ComplexFractionalInverse.KernelMass.normalized_area_projection_rotation 3 0 x).trans
        normalized_coordinate_projection]
    exact hw
  have hi : Integrable (fun y => (w (φ y) : ℂ)) rawSphereArea :=
    ((integrable_map_measure hkm.aestronglyMeasurable hφ.aemeasurable).mp hkm).ofReal
  have hp : Continuous (rawPolynomialSphere p) := by
    unfold rawPolynomialSphere
    induction p using MvPolynomial.induction_on with
    | C c => simpa using (continuous_const : Continuous (fun _ : rawSphere => c))
    | add p q hp hq =>
      convert hp.add hq using 1 <;> ext y <;> simp
    | mul_X p i hp =>
      convert hp.mul (Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)) using 1
      ext y
      simp
  have h := (show IntegrableOn (fun y => (w (φ y) : ℂ)) Set.univ rawSphereArea by
    simpa using hi).mul_continuousOn hp.continuousOn isCompact_univ
  change Integrable (fun y => (w (φ y) : ℂ) * rawPolynomialSphere p y) rawSphereArea
  simpa only [IntegrableOn, Measure.restrict_univ] using h

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral

end
