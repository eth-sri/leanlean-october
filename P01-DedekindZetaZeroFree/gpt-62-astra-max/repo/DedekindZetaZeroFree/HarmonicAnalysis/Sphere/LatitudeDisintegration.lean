module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.FractionalIntegrals.NormalizedKernel

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke
open MeasureTheory
open scoped RealInnerProductSpace BoundedContinuousFunction

noncomputable def north : Ambient := EuclideanSpace.single 0 1

@[simp] theorem north_norm : ‖north‖ = 1 := by
  simp [north, PiLp.norm_single]

theorem exists_north_rotation (x : Sphere) :
    ∃ g : Ambient ≃ₗᵢ[ℝ] Ambient, g north = (x : Ambient) := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.exists_north_rotation x

section

variable (g : Ambient ≃ₗᵢ[ℝ] Ambient) (u θ : ℝ)

noncomputable def latitudeAmbient : Ambient :=
  g (WithLp.toLp 2 ![1 - 2*u,
    Real.sqrt (4*u*(1-u)) * Real.cos θ,
    Real.sqrt (4*u*(1-u)) * Real.sin θ])

theorem latitudeAmbient_norm
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : ‖latitudeAmbient g u θ‖ = 1 := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.latitudeAmbient_norm <;> assumption

noncomputable def latitudePoint : Sphere :=
  if hu : u ∈ Set.Icc (0 : ℝ) 1 then
    ⟨latitudeAmbient g u θ, mem_sphere_zero_iff_norm.mpr (latitudeAmbient_norm g u θ hu)⟩
  else ⟨g north, mem_sphere_zero_iff_norm.mpr (by rw [g.norm_map, north_norm])⟩

theorem latitudePoint_val
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (latitudePoint g u θ : Ambient) = latitudeAmbient g u θ := by
  simp [latitudePoint, hu]

end

theorem latitudePoint_projection (x : Sphere) (g : Ambient ≃ₗᵢ[ℝ] Ambient)
    (hg : g north = (x : Ambient)) (u θ : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (1 - inner ℝ (x : Ambient) (latitudePoint g u θ : Ambient)) / 2 = u := by
  rw [latitudePoint_val g u θ hu, ← hg, latitudeAmbient, g.inner_map_map]
  simp [north, EuclideanSpace.inner_single_left]

noncomputable def angleMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Icc 0 (2 * Real.pi))

instance angleMeasure_isFiniteMeasure : IsFiniteMeasure angleMeasure := (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))).smul_finite
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr
      (mul_pos (by norm_num) Real.pi_pos))))

section

variable (θ : ℝ)

noncomputable def spinMap : Ambient →ₗ[ℝ] Ambient :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi ![LinearMap.proj 0,
      Real.cos θ • LinearMap.proj 1 - Real.sin θ • LinearMap.proj 2,
      Real.sin θ • LinearMap.proj 1 + Real.cos θ • LinearMap.proj 2])
    |>.comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap

private lemma spinMap_apply (v : Ambient) :
    spinMap θ v = WithLp.toLp 2 ![v 0, Real.cos θ * v 1 - Real.sin θ * v 2,
      Real.sin θ * v 1 + Real.cos θ * v 2] := by
  ext i
  fin_cases i <;> simp [spinMap, WithLp.linearEquiv]

lemma spinMap_norm (v : Ambient) : ‖spinMap θ v‖ = ‖v‖ := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.spinMap_norm θ v

noncomputable def spin : Ambient ≃ₗᵢ[ℝ] Ambient :=
  LinearIsometryEquiv.ofSurjective
    ({spinMap θ with norm_map' := spinMap_norm θ} : Ambient →ₗᵢ[ℝ] Ambient)
    ((LinearMap.injective_iff_surjective).mp
      ({spinMap θ with norm_map' := spinMap_norm θ} : Ambient →ₗᵢ[ℝ] Ambient).injective)

private lemma spin_apply (v : Ambient) :
    spin θ v = WithLp.toLp 2 ![v 0, Real.cos θ * v 1 - Real.sin θ * v 2,
      Real.sin θ * v 1 + Real.cos θ * v 2] := spinMap_apply θ v

end

private lemma latitudePoint_measurable (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    Measurable (fun z : ℝ × ℝ => latitudePoint g z.1 z.2) := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.latitudePoint_measurable g

private lemma latitude_spin (u θ t : ℝ) :
    RawSphereProjection.rotation (spin t) (latitudePoint (.refl ℝ Ambient) u θ) =
      latitudePoint (.refl ℝ Ambient) u (θ + t) := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.latitude_spin <;> assumption

private lemma latitude_periodic (u : ℝ) :
    Function.Periodic (latitudePoint (.refl ℝ Ambient) u) (2 * Real.pi) := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.latitude_periodic u

alias LatitudeDisintegration.latitude_periodic := latitude_periodic

private lemma angle_shift (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi))
    (θ : ℝ) :
    (∫ t, f (θ + t) ∂angleMeasure) = ∫ t, f t ∂angleMeasure := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.angle_shift <;> assumption

private lemma latitude_surjective (y : Sphere) :
    ∃ θ : ℝ, latitudePoint (.refl ℝ Ambient)
      ((1 - (y : Ambient) 0) / 2) θ = y := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.latitude_surjective y

alias LatitudeDisintegration.latitude_surjective := latitude_surjective

private lemma spin_preserving (t : ℝ) :
    MeasurePreserving (RawSphereProjection.rotation (spin t)) sphereArea sphereArea := (RawSphereProjection.rotation_preserving (spin t)).smul_measure _

private lemma spin_rotation_measurable :
    Measurable (fun z : Sphere × ℝ => RawSphereProjection.rotation (spin z.2) z.1) := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.spin_rotation_measurable

private lemma bounded_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (f : Sphere →ᵇ ℝ) (p : X → Sphere) (hp : Measurable p) :
    Integrable (fun x => f (p x)) μ := by apply @DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.bounded_integrable <;> assumption

private lemma angle_mass : angleMeasure Set.univ = 1 := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.angle_mass

private lemma latitude_integral (f : Sphere →ᵇ ℝ) :
    (∫ z : ℝ × ℝ, f (latitudePoint (.refl ℝ Ambient) z.1 z.2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod angleMeasure)) =
      ∫ y : Sphere, f y ∂sphereArea := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.latitude_integral f

private lemma latitude_disintegration_identity :
    MeasurePreserving (fun z : ℝ × ℝ => latitudePoint (.refl ℝ Ambient) z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod angleMeasure) sphereArea := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.PolynomialFunkHecke.latitude_disintegration_identity

theorem latitude_disintegration (g : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (fun z : ℝ × ℝ => latitudePoint g z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod angleMeasure) sphereArea := by exact KPCplxHarmonicIntertwinerSpectrum.HarmonicIntegral.RawFiniteFunkHecke.latitude_disintegration g

end DedekindZetaZeroFree.ComplexFractionalInverse.FunkHecke
