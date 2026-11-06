module
public import OAI.NumberTheory.DirichletL.Moments.Counting

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson CenteredMomentLattice CenteredMomentCounting

lemma normPowerProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    Function.support (normPowerProfile W a b ha hs hW t : ℝ → ℂ) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by rw [normPowerProfile_apply, hz, mul_zero])

lemma normPowerProfile_norm (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    ‖normPowerProfile W a b ha hs hW t x‖ = ‖W x‖ := by
  rw [normPowerProfile, CompletedHeight.uniformTwistedSchwartz_apply,
    CompletedHeight.normTwistedSource, norm_mul, FourierBridge.logPhase_norm, one_mul]

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp
