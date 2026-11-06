module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityGeometry

/-! # Extend the actual normalized Green density by zero with its exact norm -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open Green
open scoped ENNReal NNReal

/-- Extend a native Green density to the actual physical clock space by zero at nonpositive
  times. -/
def poleDensityExtend (G : GreenCarrier 1 → ℝ≥0∞) : Point → ℝ≥0∞ :=
  Function.extend (elapsedPhysicalPoint 0) G (fun _ => 0)

/-- Zero extension through the actual elapsed embedding is Borel. -/
theorem poleDensityExtend_measurable {G : GreenCarrier 1 → ℝ≥0∞} (hG : Measurable G) :
    Measurable (poleDensityExtend G) :=
  poleDensityElapsed_measurableEmbedding.measurable_extend hG measurable_const

variable (G : GreenCarrier 1 → ℝ≥0∞)

/-- The extension equals the native density at every genuine elapsed point. -/
theorem poleDensityExtend_apply  (q : GreenCarrier 1) :
    poleDensityExtend G (elapsedPhysicalPoint 0 q) = G q :=
  poleDensityElapsed_measurableEmbedding.injective.extend_apply _ _ _

/-- The physical zero extension has support only at strictly positive physical clock times. -/
theorem poleDensityExtend_support  :
    Function.support (poleDensityExtend G) ⊆ {p : Point | 0 < p.time} := by
  intro p hp
  by_contra ht
  apply hp
  exact Function.extend_apply' _ _ _ (fun h => ht (poleDensityElapsed_range ▸ h))

variable {G : GreenCarrier 1 → ℝ≥0∞}

/-- Exact zero extension preserves the full ambient physical Lebesgue norm. -/
theorem poleDensityExtend_eLpNorm  (hG : Measurable G)
    (q : ℝ≥0∞) :
    eLpNorm (poleDensityExtend G) q  =
      eLpNorm G q (greenLebesgue 1) := (Eq.trans
  (Eq.symm
    (eLpNorm_restrict_eq_of_support_subset (Measurable.aestronglyMeasurable (poleDensityExtend_measurable hG))
      (poleDensityExtend_support G)))
  (Eq.trans (Eq.symm (congrArg (fun μ => eLpNorm (poleDensityExtend G) q μ) poleDensityElapsed_map_volume))
    (Eq.trans (MeasurableEmbedding.eLpNorm_map_measure poleDensityElapsed_measurableEmbedding)
      (congrArg (fun f => eLpNorm f q (greenLebesgue 1)) (funext (poleDensityExtend_apply G))))))

/-- Mapping a native density through the actual elapsed embedding yields its physical extension. -/
theorem poleDensityExtend_map_withDensity  (hG : Measurable G) :
    ((greenLebesgue 1).withDensity G).map (elapsedPhysicalPoint 0) =
      (volume : Measure Point).withDensity (poleDensityExtend G) := by



  exact (show ((greenLebesgue 1).withDensity G).map (elapsedPhysicalPoint 0) =
      ((greenLebesgue 1).map (elapsedPhysicalPoint 0)).withDensity (poleDensityExtend G) by
      apply Measure.ext
      intro S hS
      rw [poleDensityElapsed_measurableEmbedding.map_apply,
        withDensity_apply _ (poleDensityElapsed_measurableEmbedding.measurable hS),
        withDensity_apply _ hS,
        setLIntegral_map hS (poleDensityExtend_measurable hG)
          poleDensityElapsed_measurableEmbedding.measurable]
      apply lintegral_congr
      intro q
      exact (poleDensityExtend_apply G q).symm).trans ((congrArg (fun μ : Measure Point => μ.withDensity (poleDensityExtend G))
    poleDensityElapsed_map_volume).trans (by
        apply Measure.ext
        intro S hS
        rw [withDensity_apply _ hS, withDensity_apply _ hS,
          Measure.restrict_restrict hS]
        rw [← lintegral_indicator hS, ← lintegral_indicator
          (hS.inter (isOpen_lt continuous_const continuous_time).measurableSet)]

        exact congrArg _ (by
            funext p
            by_cases hp : p ∈ S
            · by_cases ht : 0 < p.time
              · simp_all
              · have hz : poleDensityExtend G p = 0 := by
                  by_contra hn
                  exact ht (poleDensityExtend_support G hn)
                simp [hp, ht, hz]
            · simp [hp])))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
