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

section
variable {d : ℕ} (lam Lam : ℝ)

include lam Lam in
/-- Replace only matrices violating the source ellipticity bounds. -/
def borelEllipticRepresentative (A : CoefficientField d) :
    CoefficientField d := by
  classical
  exact fun t v => if lam • (1 : PDE.Mat d) ≤ A t v ∧ A t v ≤ Lam • (1 : PDE.Mat d)
  then A t v else lam • (1 : PDE.Mat d)

/-- The replacement is Borel, symmetric, elliptic everywhere, and a.e. unchanged. -/
theorem borelEllipticRepresentative_spec
    (_hlam : 0 < lam) (hLam : lam ≤ Lam) (A : CoefficientField d)
    (hBorel : IsBorelCoefficient A) (hsymm : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A) :
    IsBorelCoefficient (borelEllipticRepresentative lam Lam A) ∧
    IsSymmetricCoefficient (borelEllipticRepresentative lam Lam A) ∧
    HasLowerEllipticity lam (borelEllipticRepresentative lam Lam A) ∧
    HasUpperEllipticity Lam (borelEllipticRepresentative lam Lam A) ∧
    coefficientAt (borelEllipticRepresentative lam Lam A) =ᵐ[volume] coefficientAt A := by
  classical
  let : SecondCountableTopology (PDE.Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  change Measurable (coefficientAt A) at hBorel
  have hscalar : lam • (1 : PDE.Mat d) ≤ Lam • 1 := by
    gcongr
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact hBorel.ite
      ((measurableSet_le measurable_const hBorel).inter
        (measurableSet_le hBorel measurable_const)) measurable_const
  · intro t v
    unfold borelEllipticRepresentative
    split_ifs
    · exact hsymm t v
    · exact Matrix.isSymm_one.smul lam
  · intro t v
    grind [borelEllipticRepresentative]
  · intro t v
    grind [borelEllipticRepresentative]
  · filter_upwards [hlo,hhi] with z hl hh
    exact ite_eq_left ⟨hl,hh⟩

/-- The matrix bridge uses precisely the inherited finite-product supremum norm. -/
@[instance_reducible] def borelMatrixContinuousENorm :
    ContinuousENorm (PDE.Mat d) :=
  inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℝ))

end

attribute [local instance] borelMatrixContinuousENorm

/-- Global ellipticity provides the local integrability required for convolution. -/
theorem borel_coefficient_locallyIntegrable {d : ℕ} {lam Lam : ℝ}
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
  apply_rules [HypoellipticAleksandrov.abs_apply_le_of_loewner]

end HypoellipticAleksandrov.KineticAleksandrov
