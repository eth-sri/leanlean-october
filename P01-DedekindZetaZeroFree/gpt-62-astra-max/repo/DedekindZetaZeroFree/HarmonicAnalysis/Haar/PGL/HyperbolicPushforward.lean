module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGL.CompactStabilizerLift
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGL.HyperbolicVolume
public import DedekindZetaZeroFree.Geometry.PGL.IwasawaTrivialization

@[expose] public section

namespace DedekindZetaZeroFree.KPCompactStabilizerHaarSources

noncomputable section
open scoped NNReal ENNReal
open MeasureTheory

theorem arch_haar_pushforward_hyperbolic (d : ℕ) (μ : Measure (G d))
    [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map (fun g : G d => g • o d) μ =
        (c : ℝ≥0∞) • KPArch.hyperbolicVolume d := by
  obtain ⟨e, heOrbit, heFiber⟩ := product_iwasawa_homeomorph d
  obtain ⟨hfinite, hpositive, hinvariant⟩ := hyperbolic_volume_properties d
  let ν :=
    Measure.map e.symm ((KPArch.hyperbolicVolume d).prod (stabilizerHaar d))
  have := compact_fiber_lift_isHaar d e heFiber
    (KPArch.hyperbolicVolume d) hfinite hpositive hinvariant
    (stabilizerHaar d) inferInstance inferInstance
  refine ⟨Measure.haarScalarFactor μ ν,
    Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν, ?_⟩
  have horbit : Measure.map (fun g : G d => g • o d) ν =
      KPArch.hyperbolicVolume d := by
    have hcomp : (fun p : X d × K d => e.symm p • o d) = Prod.fst := by
      funext p
      rw [← heOrbit (e.symm p), e.apply_symm_apply]
    rw [Measure.map_map ((show Continuous (fun g : G d => g • o d) from
      continuous_id.smul continuous_const).measurable) e.symm.measurable]
    simp only [Function.comp_def, hcomp, Measure.map_fst_prod,
      measure_univ, one_smul]
  calc
    _ =
        Measure.map (fun g : G d => g • o d) (Measure.haarScalarFactor μ ν • ν) :=
      congrArg (Measure.map (fun g : G d => g • o d)) (Measure.isMulLeftInvariant_eq_smul μ ν)
    _ = (Measure.haarScalarFactor μ ν : ℝ≥0∞) • KPArch.hyperbolicVolume d := by
      rw [Measure.map_smul _ ((show Continuous (fun g : G d => g • o d) from
        continuous_id.smul continuous_const).measurable.aemeasurable), horbit]
      rfl

end

end DedekindZetaZeroFree.KPCompactStabilizerHaarSources
