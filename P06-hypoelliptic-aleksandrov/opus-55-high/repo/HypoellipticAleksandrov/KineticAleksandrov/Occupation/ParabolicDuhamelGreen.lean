module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Duhamel potential as a Green integral

For a starting point `(s, v)` in `U₀` and any `z`, the parabolic Duhamel potential `W(s,v)` is the
integral of `g(s + τ, w₁)` against the Green measure `Γ` of the supplied evolution kernel from the
Dirac mass at `(v, z)` with horizon `T - s`: the Green identity of Lemma 2.3, carried to the
parabolic marginal, in absolute time.
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal ProbabilityTheory

/-- Integration over the elapsed-time carrier is Lebesgue integration over `(0, L)`. -/
theorem integral_elapsed_eq (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ τ : ElapsedTime (ENNReal.ofReal L), f τ.1 ∂elapsedVolume (ENNReal.ofReal L) =
      ∫ x in Ioo 0 L, f x := by
  have h1 := integral_map (μ := elapsedVolume _)
    (φ := (Subtype.val : ElapsedTime (ENNReal.ofReal L) → ℝ))
    measurable_subtype_coe.aemeasurable (f := f) hf.aestronglyMeasurable
  have h2 : (elapsedVolume _).map
      (Subtype.val : ElapsedTime (ENNReal.ofReal L) → ℝ) = volume.restrict (Ioo 0 L) := by
    have he : {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal L} = Ioo 0 L := by
      aesop
    exact (map_comap_subtype_coe (measurableSet_elapsedTime _) volume).trans
      (by rw [he])
  simp_all

/-- A translation of the elapsed-time interval. -/
theorem integral_Ioo_shift (f : ℝ → ℝ) (s L : ℝ) (hL : 0 ≤ L) :
    ∫ x in Ioo 0 L, f (s + x) = ∫ r in Ioc s (s + L), f r := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_comp_add_left, intervalIntegral.integral_of_le (by linarith)]
  simp

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
