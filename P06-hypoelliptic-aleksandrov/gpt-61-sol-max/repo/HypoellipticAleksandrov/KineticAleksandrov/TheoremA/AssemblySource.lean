module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionAPI
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Measurable zero extension of a cylinder source -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ} {Q : Set (KineticPoint d)} (hQ : MeasurableSet Q) (f : HypoellipticAleksandrov.KineticScalarField d)

include hQ
/-- Subtype measurability yields a globally measurable zero extension. -/
theorem measurable_source_indicator
    (hf : Measurable (fun P : Q => f P)) : Measurable (Q.indicator f) := (measurable_of_restrict_of_restrict_compl hQ
  (Eq.mpr (id (congrArg (fun _a => Measurable _a) (funext fun P => indicator_of_mem P.property f))) hf)
  (Eq.mpr (id (congrArg (fun _a => Measurable _a) (funext fun P => indicator_of_notMem P.property f))) measurable_const))

/-- Zero extension agrees with the original source almost everywhere on its cylinder. -/
theorem source_indicator_ae_eq  :
    Q.indicator f =ᵐ[volume.restrict Q] f := by
  filter_upwards [ae_restrict_mem hQ] with P hP
  exact Set.indicator_of_mem hP f

/-- The positive source norm is unchanged by the measurable zero extension. -/
theorem eLpNorm_positive_source_indicator  (p : ℝ≥0∞) :
    eLpNorm (fun P => max (Q.indicator f P) 0) p (volume.restrict Q) =
      eLpNorm (fun P => max (f P) 0) p (volume.restrict Q) := by
  apply eLpNorm_congr_ae
  filter_upwards [source_indicator_ae_eq hQ f] with P hP
  rw [hP]

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
