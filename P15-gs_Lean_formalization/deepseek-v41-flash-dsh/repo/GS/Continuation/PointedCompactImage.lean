module
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CompactFibres
public import GS.Continuation.ExponentialChart
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.OriginalCompact
public import GS.Extensions.OriginalFibres
public import GS.Extensions.OriginalUniform
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.M4Certificate
public import GS.M4Necessary
public import GS.M4Obstruction
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Specifications
public import GS.ThreeFactor


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Pointed homeomorphism of the ORIGINAL compact images

 Compactness, continuity and same fibres are taken
from theorem bodies, not assumptions. Only the two compact images are identified;
coverage of a neighbourhood of the whole GS family and the cone obstruction are
not claimed here.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

/-- Convenient names for the two genuine compact image spaces. -/
abbrev OriginalFImage {q : ℕ} (Q₀ : Mat q) (η : ℝ) :=
  Set.range (fun p : ↥(originalK q η) => originalF Q₀ p.val)

/-- A basepoint in the F-image with its actual membership witness. -/
def originalFImageBase {q : ℕ} (Q₀ : Mat q) (η : ℝ) (hη : 0 ≤ η) :
    OriginalFImage Q₀ η :=
  ⟨basePoint Q₀,
    ⟨⟨originalBaseParameters q, originalBaseParameters_mem q hη⟩,
      originalF_basePoint Q₀⟩⟩

end GS.Continuation
