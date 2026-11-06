module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierSplit

/-! # Uniform two-exponential bound for the actual full exit Fourier measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

/- Combining loss and killed bounds only enlarges their structural prefactor. -/
theorem exitFourier_add_positive_bounds {A B X Y : ℝ} (hA : 0 ≤ A) (hY : 0 ≤ Y) :
    A * X + B * (X + Y) ≤ (A + B) * (X + Y) := by
  nlinarith only [mul_nonneg hA hY]

/- Decreasing a nonnegative rate increases the corresponding exponential bound. -/
theorem exitFourier_exp_rate {a c x } (hca : c ≤ a) (hx : 0 ≤ x) :
    Real.exp (-a * x) ≤ Real.exp (-c * x) :=
  Real.exp_le_exp.mpr (by
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hca hx))

/- The actual exit Fourier measure has both short-time exponentials, uniformly over all data. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
