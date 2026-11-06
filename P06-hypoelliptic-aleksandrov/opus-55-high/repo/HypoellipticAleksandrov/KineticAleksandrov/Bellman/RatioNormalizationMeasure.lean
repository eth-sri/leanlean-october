module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureDegree
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-! # Radon and homogeneous measure transport under position normalization -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable {β : ℝ} {μ : Measure BellmanPuncturedPlane}

/-- A homeomorphism preserves the literal Radon conditions used for Bellman pairs. -/
theorem IsBellmanRadon.map_homeomorph 
    (hμ : IsBellmanRadon μ) (T : BellmanPuncturedPlane ≃ₜ BellmanPuncturedPlane) :
    IsBellmanRadon (Measure.map T μ) := by
  let  := hμ.1
  let  := hμ.2
  refine ⟨?_, Measure.InnerRegular.map T⟩
  constructor
  intro K hK
  rw [Measure.map_apply T.measurable hK.measurableSet]
  have he : T ⁻¹' K = T.symm '' K := by
    ext q
    constructor
    · intro hq
      exact ⟨T q, hq, T.symm_apply_apply q⟩
    · rintro ⟨z, hz, rfl⟩
      simp_all
  rw [he]
  exact (hK.image T.symm.continuous).measure_lt_top

/-- Finite scalar multiplication preserves the literal Radon conditions. -/
theorem IsBellmanRadon.smul 
    (hμ : IsBellmanRadon μ) (c : ENNReal) (hc : c ≠ ⊤) : IsBellmanRadon (c • μ) := by
  let  := hμ.1
  let  := hμ.2
  exact ⟨IsFiniteMeasureOnCompacts.smul μ hc, inferInstance⟩

/-- Position rescaling preserves every density degree without changing its exponent. -/
theorem HasBellmanDensityDegree.map_position  (hμ : HasBellmanDensityDegree β μ)
    (s : ℝ) (hs : 0 < s) :
    HasBellmanDensityDegree β (Measure.map (bellmanPositionHomeomorph s hs) μ) := by
  intro r hr E hE
  let T := bellmanPositionHomeomorph s hs
  let D := bellmanDilationHomeomorph r hr
  have hcomm (q : BellmanPuncturedPlane) : T (D q) = D (T q) :=
    bellmanPositionHomeomorph_dilation s hs r hr q
  have hset : T ⁻¹' (D '' E) = D '' (T ⁻¹' E) := by
    ext q
    constructor
    · rintro ⟨z, hz, he⟩
      refine ⟨T.symm z, by simp_all, ?_⟩
      apply T.injective
      rw [hcomm, T.apply_symm_apply]
      exact he
    grind
  change μ.map T (D '' E) = ENNReal.ofReal (r ^ (4 - β)) * μ.map T E
  rw [Measure.map_apply T.measurable (D.measurableEmbedding.measurableSet_image.mpr hE),
    hset, Measure.map_apply T.measurable hE]
  exact hμ r hr _ (T.measurable hE)

/-- Scalar multiplication preserves every density degree. -/
theorem HasBellmanDensityDegree.smul 
    (hμ : HasBellmanDensityDegree β μ) (c : ENNReal) :
    HasBellmanDensityDegree β (c • μ) := by
  intro r hr E hE
  simp only [Measure.smul_apply, hμ r hr E hE]
  ring

end HypoellipticAleksandrov.KineticAleksandrov
