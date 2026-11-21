module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open MeasureTheory Topology
open scoped Classical
open KPContLocalNorm KPContLocalEnergy



 def derivativeTest {n : ℕ} {Ω : TopologicalSpace.Opens (Space n)}
    (φ : TestFunction Ω ℂ ⊤) (j : Fin n) : TestFunction Ω ℂ ⊤ :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) φ








end DedekindZetaZeroFree

end
