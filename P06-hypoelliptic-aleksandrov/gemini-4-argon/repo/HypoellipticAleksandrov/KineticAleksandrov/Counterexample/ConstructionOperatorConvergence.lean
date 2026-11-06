module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionOperator
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMollifiedJets

/-! # Pointwise recovery of the actual mollified operator at each fixed time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter
open scoped Topology
open scoped Convolution

/- The selected full extended source, with the literal backward-operator sign convention. -/
def constructionExtendedSource {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ) (A : XV d → PDE.Mat d)
    (P : KineticPoint d) : ℝ :=
  constructionExtendedTimeJet h r mu R P.time (P.position, P.velocity) +
    PDE.vecDot P.velocity (fun i => constructionExtendedNativeGradient h r mu R m P.time
      (P.position, P.velocity) (Fin.castAdd d i)) -
    matrixContraction (A (P.position, P.velocity)) (fun i k =>
      constructionExtendedNativeHessian h r mu R m P.time (P.position, P.velocity) i k)

/- At each time the actual smoothed operator converges almost everywhere to the full
source formed from the same selected representatives. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
