module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionAPI
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Measurable zero extension of a cylinder source -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Set
open scoped ENNReal

section
variable {d : ℕ} {Q : Set (KineticPoint d)} (hQ : MeasurableSet Q) (f : KineticPoint d → ℝ)
include hQ

/-- Subtype measurability yields a globally measurable zero extension. -/
theorem measurable_source_indicator
    (hf : Measurable (fun P : Q => f P)) : Measurable (Q.indicator f) := by
  classical
  apply measurable_of_restrict_of_restrict_compl hQ
  · have heq : Q.domRestrict (Q.indicator f) = fun P : Q => f P := by
      funext P
      exact Set.indicator_of_mem P.property f
    rw [heq]
    exact hf
  · have heq : Qᶜ.domRestrict (Q.indicator f) = fun _ => (0 : ℝ) := by
      funext P
      exact Set.indicator_of_notMem P.property f
    rw [heq]
    exact measurable_const

/-- Zero extension agrees with the original source almost everywhere on its cylinder. -/
theorem source_indicator_ae_eq :
    Q.indicator f =ᵐ[volume.restrict Q] f := by
  filter_upwards [ae_restrict_mem hQ] with P hP
  exact Set.indicator_of_mem hP f

end

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA
