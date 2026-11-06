module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitive
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Mixed-measure triangular Fubini for one-dimensional measure primitives -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Triangular Fubini for a real measure and real Lebesgue measure, retaining atoms of μ. -/
theorem bellman_measure_triangle_swap (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (r R : ℝ) (g ψ : ℝ → ℝ) (hg : Continuous g) (hψ : Continuous ψ) :
    (∫ x in Icc r R, ∫ z in Ioc r x, g z * ψ x ∂μ) =
      ∫ z in Ioc r R, (∫ x in Icc z R, g z * ψ x) ∂μ := by
  let ν := μ.restrict (Ioc r R)
  let νvol := volume.restrict (Icc r R)
  let T : Set (ℝ × ℝ) := {w | w.1 ≤ w.2}
  have hT : MeasurableSet T := (isClosed_le continuous_fst continuous_snd).measurableSet
  have hgi : Integrable g ν := hg.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hψi : Integrable ψ νvol := hψ.continuousOn.integrableOn_Icc
  have hp : Integrable (fun w : ℝ × ℝ => g w.1 * ψ w.2) _ := hgi.mul_prod hψi
  have ht := hp.indicator hT
  have hleft : (∫ x, ∫ z, T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x)
      ∂ν ∂νvol) = ∫ x in Icc r R, ∫ z in Ioc r x, g z * ψ x ∂μ := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change (∫ z, T.indicator _ _ ∂ν) =
      ∫ z in Ioc r x, g z * ψ x ∂μ
    have he : (fun z => T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x)) =
        (Iic x).indicator (fun z => g z * ψ x) := by
      rfl
    rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hs : Iic x ∩ Ioc r R = Ioc r x := by
      grind
    rw [hs]
  have hright : (∫ z, ∫ x, T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x)
      ∂νvol ∂ν) = ∫ z in Ioc r R, (∫ x in Icc z R, g z * ψ x) ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    change (∫ x, T.indicator _ _ ∂νvol) =
      ∫ x in Icc z R, g z * ψ x
    have he : (fun x => T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x)) =
        (Ici z).indicator (fun x => g z * ψ x) := by
      rfl
    rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hs : Ici z ∩ Icc r R = Icc z R := by
      grind
    rw [hs]
  calc
    _ = ∫ x, ∫ z, T.indicator _ _ ∂ν ∂νvol :=
      hleft.symm
    _ = ∫ z, ∫ x, T.indicator _ _ ∂νvol ∂ν :=
      integral_integral_swap ht.swap
    _ = _ := hright

end HypoellipticAleksandrov.KineticAleksandrov
