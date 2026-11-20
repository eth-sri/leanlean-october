module

public import DedekindZetaZeroFree.Eisenstein.Sections.FlatRightWordJets

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff Matrix.Norms.Operator
open Filter
namespace DedekindZetaZeroFree.KPActualReflectionData.NativeFlowJet
open KPGlobalResidualConstruction KPContinuation.ChamberFlatSource
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (b : KPSmoothActualFlowData.B F)

def flowMatrix (t : ℝ) (w : NumberField.InfinitePlace F) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPSmoothActualFlowData.matrixExponential
    (KPSmoothActualFlowData.sl2Matrix (fun j => if (w,j) = b then t else 0))

def flowChart (t : ℝ) : ArchCoordinates F :=
  fun w => ChartMatrix.chartCoordinates (flowMatrix F b t w).val

 theorem flowMatrix_zero (w : NumberField.InfinitePlace F) :
    flowMatrix F b 0 w = 1 := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.RightChartJetsAndFlowWords.flowMatrix_zero <;> assumption

@[simp] theorem flowChart_zero : flowChart F b 0 = archBase F := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.theta_zero <;> assumption

private theorem flowEntry_smooth
    (w : NumberField.InfinitePlace F) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => (flowMatrix F b t w).val i j) := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.RightChartJetsAndFlowWords.flowEntry_smooth <;> assumption

theorem flowChart_smooth :
    ContDiffAt ℝ (⊤ : ℕ∞) (flowChart F b) 0 := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.theta_smooth <;> assumption

def flowDirection : ArchCoordinates F := deriv (flowChart F b) 0

theorem flowChart_hasDeriv :
    HasDerivAt (flowChart F b) (flowDirection F b) 0 :=
  ((flowChart_smooth F b).differentiableAt (by simp)).hasDerivAt

theorem flowChart_reconstruct :
    ∀ᶠ t in nhds (0 : ℝ), archChart F ζ hζ (flowChart F b t) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t) := by apply @DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets.theta_chart <;> assumption

end DedekindZetaZeroFree.KPActualReflectionData.NativeFlowJet

end
