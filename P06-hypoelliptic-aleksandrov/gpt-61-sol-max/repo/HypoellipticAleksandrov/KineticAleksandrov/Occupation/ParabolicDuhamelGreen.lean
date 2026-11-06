module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierOccupation
import Lean.Elab.Tactic.SolveByElim



/-!
# The Duhamel potential as a Green integral

For a starting point `(s, v)` in `U₀` and any `z`, the parabolic Duhamel potential `W(s,v)` is the
integral of `g(s + τ, w₁)` against the Green measure `Γ` of the supplied evolution kernel from the
Dirac mass at `(v, z)` with horizon `T - s`: the Green identity of Lemma 2.3, carried to the
parabolic marginal, in absolute time.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ProbabilityTheory

/-- Integration over the elapsed-time carrier is Lebesgue integration over `(0, L)`. -/
theorem integral_elapsed_eq (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ τ : ElapsedTime (ENNReal.ofReal L), f τ.1 ∂elapsedVolume (ENNReal.ofReal L) =
      ∫ x in Ioo 0 L, f x := (Green.integral_elapsed_finite L hL f)

/-- A translation of the elapsed-time interval. -/
theorem integral_Ioo_shift (f : ℝ → ℝ) (s L : ℝ) (hL : 0 ≤ L) :
    ∫ x in Ioo 0 L, f (s + x) = ∫ r in Ioc s (s + L), f r := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_comp_add_left f s, intervalIntegral.integral_of_le (by linarith)]
  simp

variable {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
