module

public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.FractionalIntegrals.NormalizedKernel

@[expose] public section

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.SphereProjection

open MeasureTheory Set
open scoped ENNReal

private lemma coordinate_bounds (y : Sphere) :
    -1 ≤ (y : Ambient) 0 ∧ (y : Ambient) 0 ≤ 1 := by
  have h : ‖(y : Ambient) 0‖ ≤ 1 := by
    calc
      _ ≤ ‖(y : Ambient)‖ := PiLp.norm_apply_le _ _
      _ = 1 := mem_sphere_zero_iff_norm.mp y.property
  simpa [Real.norm_eq_abs, abs_le] using h

theorem projection_of_raw_caps
    (hmass : (volume : Measure Ambient).toSphere univ = ENNReal.ofReal (4 * Real.pi))
    (hcap : ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
      (volume : Measure Ambient).toSphere {y : Sphere | (y : Ambient) 0 ≤ t} =
        ENNReal.ofReal (2 * Real.pi * (t + 1))) :
    Measure.map (fun y : Sphere => (1 - (y : Ambient) 0) / 2) sphereArea =
      (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) := by apply @DedekindZetaZeroFree.ComplexFractionalInverse.RawSphereProjection.projection_of_raw_caps <;> assumption

end DedekindZetaZeroFree.ComplexFractionalInverse.SphereProjection

end

section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.SphereProjection
open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem open_north_cap_of_closed
    (μ : Measure Sphere)
    (hcap : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {y : Sphere | t ≤ (y : Ambient) 0} = ENNReal.ofReal (2 * Real.pi * (1 - t)))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    μ {y : Sphere | t < (y : Ambient) 0} = ENNReal.ofReal (2 * Real.pi * (1 - t)) := by apply @DedekindZetaZeroFree.ComplexFractionalInverse.RawSphereProjection.open_north_cap_of_closed <;> assumption

theorem raw_lower_caps_of_positive_north
    (μ : Measure Sphere) [IsFiniteMeasure μ]
    (hmass : μ univ = ENNReal.ofReal (4 * Real.pi))
    (hsym : ∀ t : ℝ, μ {y : Sphere | (y : Ambient) 0 ≤ t} =
      μ {y : Sphere | -t ≤ (y : Ambient) 0})
    (hcap : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {y : Sphere | t ≤ (y : Ambient) 0} = ENNReal.ofReal (2 * Real.pi * (1 - t))) :
    ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
      μ {y : Sphere | (y : Ambient) 0 ≤ t} = ENNReal.ofReal (2 * Real.pi * (t + 1)) := by apply @DedekindZetaZeroFree.ComplexFractionalInverse.RawSphereProjection.raw_lower_caps_of_positive_north <;> assumption

end DedekindZetaZeroFree.ComplexFractionalInverse.SphereProjection

end
