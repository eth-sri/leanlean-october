module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.BoundaryOperatorWords
public import Mathlib.Tactic.FunProp

@[expose] public section

noncomputable section
open scoped Classical Topology Matrix.Norms.Operator
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPGlobalResidualConstruction
open NativeComplexHCOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
 instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℝ _
 theorem exponential_continuous (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (fun t : ℝ => KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X)) := by
  apply Units.continuous_iff.mpr
  constructor
  · fun_prop
  · change Continuous (fun t : ℝ => ((NormedSpace.isUnit_exp ((t : ℂ) • X)).unit⁻¹).val)
    simp only [← Ring.inverse_of_isUnit, Ring.inverse_exp]
    fun_prop
 theorem exponential_zero : KPSmoothActualFlowData.matrixExponential
    (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  apply Units.ext
  exact NormedSpace.exp_zero

end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
