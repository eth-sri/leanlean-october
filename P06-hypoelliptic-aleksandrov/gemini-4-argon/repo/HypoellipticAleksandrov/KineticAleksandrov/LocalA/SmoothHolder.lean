module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothHolderNormalized
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothLocalStatement
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic

/-! # Smooth local regularity conditional only on the spatial derivative bound

The spatial-bound theorem is the sole
hypothesis. All kinetic normalization and Hölder
combination steps are proved here. The joint statement is not claimed unconditionally.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Holder SectionTwo
open scoped ContDiff MatrixOrder Matrix.Norms.Elementwise

/- Smooth time--velocity coefficients with pointwise bounds meet the Section 2 premises. -/
theorem sectionTwo_of_smooth_bounds {d lam Lam}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) {A : CoefficientField d}
    (hA : IsSmoothCoefficient A) (hs : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A) :
    IsSectionTwoCoefficient lam Lam A := by
  refine ⟨hlam, hLam, ?_, hs, hlo, hhi⟩
  intro i j
  exact ((contDiff_apply_apply ℝ ℝ i j).comp hA).comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))

/- The exact joint smooth conditions follows from the sole authorized LA-08 input. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
