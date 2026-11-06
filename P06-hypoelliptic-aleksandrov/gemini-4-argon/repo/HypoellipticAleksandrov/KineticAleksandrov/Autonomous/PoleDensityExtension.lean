module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityGeometry

/-! # Extend the actual normalized Green density by zero with its exact norm -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution Green
open scoped ENNReal NNReal

/- Extend a native Green density to the actual physical clock space by zero at nonpositive
  times. -/
def poleDensityExtend (G : GreenCarrier 1 → ℝ≥0∞) : Point → ℝ≥0∞ :=
  Function.extend (elapsedPhysicalPoint 0) G (fun _ => 0)

/- Zero extension through the actual elapsed embedding is Borel. -/
theorem poleDensityExtend_measurable {G } (hG : Measurable G) :
    Measurable (poleDensityExtend G) :=
  poleDensityElapsed_measurableEmbedding.measurable_extend hG measurable_const

/- The extension equals the native density at every genuine elapsed point. -/
theorem poleDensityExtend_apply (G : GreenCarrier 1 → ℝ≥0∞) (q : GreenCarrier 1) :
    poleDensityExtend G (elapsedPhysicalPoint 0 q) = G q :=
  poleDensityElapsed_measurableEmbedding.injective.extend_apply _ _ _

/- The physical zero extension has support only at strictly positive physical clock times. -/
theorem poleDensityExtend_support (G : GreenCarrier 1 → ℝ≥0∞) :
    Function.support (poleDensityExtend G) ⊆ {p : Point | 0 < p.time} := by
  intro p hp
  by_contra ht
  apply hp
  exact Function.extend_apply' _ _ _ (fun h => ht (poleDensityElapsed_range ▸ h))

/- Exact zero extension preserves the full ambient physical Lebesgue norm. -/
theorem poleDensityExtend_eLpNorm {G } (hG : Measurable G)
    (q : ℝ≥0∞) :
    eLpNorm (poleDensityExtend G) q (volume : Measure Point) =
      eLpNorm G q (greenLebesgue 1) := by
  have hr := eLpNorm_restrict_eq_of_support_subset (μ := (volume : Measure Point)) (p := q)
    (poleDensityExtend_measurable hG).aestronglyMeasurable (poleDensityExtend_support G)
  have hm := poleDensityElapsed_measurableEmbedding.eLpNorm_map_measure
    (μ := greenLebesgue 1) (g := poleDensityExtend G) (p := q)
  have heq :=
    funext (poleDensityExtend_apply G)
  exact hr.symm.trans ((congrArg (fun μ : Measure Point =>
    eLpNorm (poleDensityExtend G) q μ) poleDensityElapsed_map_volume).symm.trans
      (hm.trans (congrArg (fun f : GreenCarrier 1 → ℝ≥0∞ =>
        eLpNorm f q (greenLebesgue 1)) heq)))

/- Mapping a native density through the actual elapsed embedding yields its physical extension. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
