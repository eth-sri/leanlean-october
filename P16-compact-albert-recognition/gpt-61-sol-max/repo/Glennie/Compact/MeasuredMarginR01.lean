module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop
public import Glennie.Compact.InputDisplacementR01
public import Glennie.NativeGenerationStabilizersR01
public import Glennie.Compact.ReadoutRobustnessR01

/- Measured margins using native producers.
ε denotes entrywise raw readout error, ξ a certified scalar error allowance,
and δ endpoint displacement. No target-null or multiplication-defect claim. -/
@[expose] public section
namespace Glennie.Compact.MeasuredMarginR01
open Glennie
open Glennie.NativeGenerationEndpointR01
open Glennie.NativeGenerationStabilizersR01
open Glennie.Compact.NativeNormKernel
section
 theorem scalar_margin_lower (observed actual ξ : ℝ)
    (herr : |observed-actual| ≤ ξ) : |observed|-ξ ≤ |actual| := by
  have ht : |observed| ≤ |observed-actual|+|actual| := by grind
  linarith

 /-- Raw six-readout errors ε induce a scalar allowance ξ when 6ε≤ξ.
No frame premise is needed for this algebraic error statement. -/
 theorem six_readout_scalar_error
    (T : Glennie.Compact.Affine20.Triple)
    (noisy : Glennie.Compact.ReadoutRobustnessR01.Readouts) (ε ξ : ℝ)
    (herr : Glennie.Compact.ReadoutRobustnessR01.ErrorsAtMost noisy
      (Glennie.Compact.ReadoutRobustnessR01.exactReadouts T) ε)
    (hallowance : 6*ε ≤ ξ) :
    |Glennie.Compact.ReadoutRobustnessR01.noisyPhi noisy -
      phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))| ≤ ξ := (Glennie.Compact.ReadoutRobustnessR01.phi_error T noisy ε herr).trans hallowance


end
end Glennie.Compact.MeasuredMarginR01
