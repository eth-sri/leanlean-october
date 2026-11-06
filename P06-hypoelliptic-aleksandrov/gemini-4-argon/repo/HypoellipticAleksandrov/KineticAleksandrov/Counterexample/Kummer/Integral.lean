module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Series
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.IntegralKernel
import Mathlib.Tactic.Linarith

/-!
# Positive integral definitions of Kummer U

`UI` has positive shape and argument. `UN` is the source transformation for the
negative shape interval. The real auxiliary formulae are only characterized at positive
arguments; their values outside that domain are never used as special-function values.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/- The Laplace kernel with positive first parameter. -/
def laplaceKernel (a : Pos) (b z t : ℝ) : ℝ := laplaceKernelReal a.1 b z t

/- Kummer U defined by the convergent positive integral. -/
def UIr (a : Pos) (b z : ℝ) : ℝ :=
  (Real.Gamma a.1)⁻¹ * ∫ t in Ioi (0 : ℝ), laplaceKernel a b z t

/- Transformed U for the negative shape interval in Appendix C. -/
def UNr (a : NegThird) (z : ℝ) : ℝ :=
  z ^ (1 / 3 : ℝ) * UIr ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩ (4 / 3) z

/- Restriction of the auxiliary integral formula to its genuine domain. -/
theorem UIr_pos (a : Pos) (b z : ℝ) (hz : 0 < z) : 0 < UIr a b z :=
  mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos a.2))
    (integral_laplaceKernelReal_pos a.1 b z a.2 hz)

/- Strict positivity of the transformed negative-shape U on the positive real axis. -/
theorem UNr_pos (a : NegThird) (z : ℝ) (hz : 0 < z) : 0 < UNr a z :=
  mul_pos (Real.rpow_pos_of_pos hz _) (UIr_pos _ _ z hz)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
