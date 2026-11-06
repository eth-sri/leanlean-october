module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Null-set replacement of time--velocity coefficients -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.Elementwise

/- Replace only matrices violating the source ellipticity bounds. -/
def borelEllipticRepresentative {d } (lam Lam : ℝ) (A : CoefficientField d) :
    CoefficientField d := by
  classical
  exact fun t v => if lam • (1 : PDE.Mat d) ≤ A t v ∧ A t v ≤ Lam • (1 : PDE.Mat d)
  then A t v else lam • (1 : PDE.Mat d)

/- The replacement is Borel, symmetric, elliptic everywhere, and a.e. unchanged. -/
@[instance_reducible] def borelMatrixContinuousENorm {d } :
    ContinuousENorm (PDE.Mat d) :=
  inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℝ))

attribute [local instance] borelMatrixContinuousENorm

/- Global ellipticity provides the local integrability required for convolution. -/
theorem borel_coefficient_locallyIntegrable {d lam Lam}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : CoefficientField d)
    (hBorel : IsBorelCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A) :
    LocallyIntegrable (coefficientAt A) volume := by
  let : ContinuousENorm (PDE.Mat d) :=
    inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℝ))
  let : TopologicalSpace.PseudoMetrizableSpace (PDE.Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  change Measurable (coefficientAt A) at hBorel
  have hLam0 := (hlam.le.trans hLam)
  apply (locallyIntegrable_const Lam).mono hBorel.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_of_nonneg hLam0,Matrix.norm_le_iff hLam0]
  intro i j
  exact HypoellipticAleksandrov.abs_apply_le_of_loewner hlam (hlo z.1 z.2) (hhi z.1 z.2) i j

end HypoellipticAleksandrov.KineticAleksandrov
