module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturnAction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturn

/-! # Uniform velocity decay throughout an elapsed-time bin

This is the velocity-return input to time-bin counting, rather than a bound
on the visit-counting measure itself.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/- Elapsed time after the start of bin `j` has at least its dimensionless bin index. -/
theorem timeBinCount_integral_le {r a b D : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hlen : b - a ≤ r ^ 2) (hD : 0 ≤ D)
    (hi : IntegrableOn f (Ioc a b)) (hb : ∀ t ∈ Ioc a b, f t ≤ D) :
    (∫ t in Ioc a b, f t) ≤ r ^ 2 * D := by
  have hm := setIntegral_mono_on hi
    (integrableOn_const (C := D) (by simp : volume (Ioc a b) ≠ ⊤)) measurableSet_Ioc hb
  have hv : volume.real (Ioc a b) = b - a := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [setIntegral_const, hv, smul_eq_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right hlen hD)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
