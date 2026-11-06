module

public import Mathlib

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section


open MeasureTheory

namespace DedekindZetaZeroFree.Quantitative
namespace NormalizedFubiniMajorant

noncomputable def c  := (2 * (Real.pi : ℂ))⁻¹

lemma norm_c : ‖c‖ = (2 * Real.pi)⁻¹ := by
  simp [c, Real.pi_pos.le, abs_of_pos Real.pi_pos]

def integrable_of_majorant2 (Fn : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable Fn volume)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ‖Fn p‖ ≤ A * g p)  :=
  Integrable.mono' (hg.const_mul A) hF hb

def integrable_of_majorant2_continuous (Fn : ℝ × ℝ → ℂ) (hF : Continuous Fn)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
    (hb : ∀ p, ‖Fn p‖ ≤ A * g p)  :=
  integrable_of_majorant2 Fn hF.aestronglyMeasurable g hg A (Filter.Eventually.of_forall hb)

section
variable (Fn : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable Fn volume)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g volume) (A : ℝ)
include Fn hF g hg A
def outer_integrable2  
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ‖Fn p‖ ≤ A * g p)  :=
  (integrable_of_majorant2 Fn hF g hg A hb).integral_prod_left.const_mul c

theorem norm_double_le   (hA : 0 ≤ A)
    (hb : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ‖Fn p‖ ≤ A * g p) :
    ‖c * ∫ t : ℝ, c * ∫ s : ℝ, Fn (t, s)‖
      ≤ ((2 * Real.pi)⁻¹) ^ 2 * A * ∫ p : ℝ × ℝ, g p := by
  have hI := integrable_of_majorant2 Fn hF g hg A hb
  have h1 : ∫ t : ℝ, c * ∫ s : ℝ, Fn (t, s) = c * ∫ p, Fn p := by
    rw [integral_const_mul, ← integral_prod (fun p : ℝ × ℝ => Fn p) hI]
    rfl
  rw [h1, ← mul_assoc, norm_mul, norm_mul, norm_c]
  have h2 : ‖∫ p, Fn p‖ ≤ A * ∫ p, g p := by
    calc ‖∫ p, Fn p‖ ≤ ∫ p, ‖Fn p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p, A * g p := integral_mono_ae hI.norm (hg.const_mul A) hb
      _ = A * ∫ p, g p := integral_const_mul _ _
  have := norm_nonneg c
  calc (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ‖∫ p, Fn p‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * (A * ∫ p, g p) := by
        gcongr
    _ = _ := by ring
end


end NormalizedFubiniMajorant
end DedekindZetaZeroFree.Quantitative
