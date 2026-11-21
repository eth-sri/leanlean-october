module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows

@[expose] public section

noncomputable section
open MeasureTheory NumberField
open scoped Matrix BigOperators Classical InnerProductSpace
namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction

export KPCplxLoweringCoordinateBoost.Geometry (noncompactMatrix compactMatrix LocalBasis cartanMatrix)

export KPCplxHarmonicExtraction.CasimirTransfer.Transfer (local_derivative_mem)

private theorem local_path_differentiable (s : ℝ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (g : KPCplxCharacterHaar.ComplexGL2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • M))) 0 :=
  (KPCplxHarmonicExtraction.CasimirTransfer.Transfer.hasDerivAt_rightExp s f g M).differentiableAt

 def rightDerivative (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.PrincipalSeries s :=
  ⟨fun g => deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0,
    local_derivative_mem s X f⟩

theorem rightDerivative_add (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f h : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    rightDerivative s X (f + h) = rightDerivative s X f + rightDerivative s X h := by
  apply Subtype.ext
  funext g
  have hfh : (fun t : ℝ => (f + h) (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) =
      (fun t : ℝ => f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) +
        (fun t : ℝ => h (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) := by
    funext t
    rfl
  show deriv (fun t : ℝ =>
      (f + h) (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 +
    deriv (fun t : ℝ =>
      h (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0
  rw [hfh]
  exact deriv_add (local_path_differentiable s f g X) (local_path_differentiable s h g X)

theorem rightDerivative_smul (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    rightDerivative s X (a • f) = a • rightDerivative s X f := by
  apply Subtype.ext
  funext g
  have hsf : (fun t : ℝ => (a • f) (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) =
      (fun t : ℝ => a • f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) := by
    funext t
    rfl
  show deriv (fun t : ℝ =>
      (a • f) (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 =
    a • deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0
  rw [hsf]
  exact deriv_const_smul a (local_path_differentiable s f g X)

def rightDerivativeLinear (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Module.End ℂ (KPCplxPrincipalSeriesCharts.PrincipalSeries s) where
  toFun := rightDerivative s X
  map_add' := rightDerivative_add s X
  map_smul' := rightDerivative_smul s X

theorem rightDerivativeLinear_apply (s : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (g) :
    rightDerivativeLinear s X f g = deriv (fun t : ℝ =>
      f (g * KPSmoothActualFlowData.matrixExponential ((t : ℂ) • X))) 0 := rfl

def localDerivative (s : ℝ) (b : LocalBasis) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :=
  rightDerivative s (cartanMatrix b) f

end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction

end
