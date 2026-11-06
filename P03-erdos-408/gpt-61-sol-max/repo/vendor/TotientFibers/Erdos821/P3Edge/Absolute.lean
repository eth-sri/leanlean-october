module
public import Mathlib.Tactic

public import Erdos821.P3Edge.CoeffBound
public import Erdos821.P3Edge.NormOsc
public import Erdos821.P3Edge.LargeX

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

section
variable (r : MemoryParameters F) (z : P.MemoryState (J + F.ell))

lemma memoryWeight_pos     :
    0 < P.memoryWeight r.v z := pow_pos (lt_trans zero_lt_one r.v_gt) (P.memorySize z)

lemma memoryWeight_nonneg     :
    0 ≤ P.memoryWeight r.v z :=
  (memoryWeight_pos r z).le

end

section
variable (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n) (s t : P.MemoryState (J + F.ell))

lemma absoluteMemoryEdgeKernel_nonneg      
        :
    0 ≤ absoluteMemoryEdgeKernel A n rho theta i .all s t := by
  unfold absoluteMemoryEdgeKernel
  apply mul_nonneg (edgeSymmetryFactor_nonneg P _)
  positivity

lemma norm_cast_absolute      
        :
    ‖((absoluteMemoryEdgeKernel A n rho theta i .all s t : ℝ) : ℂ)‖ =
      absoluteMemoryEdgeKernel A n rho theta i .all s t := by
  simp_all [absoluteMemoryEdgeKernel_nonneg]

end

-- Coefficient norms: oscillation (pattern coeff * imaginaryPower, phase) has
-- modulus ≤ patternMass; rawEdgeWeight carries all masses/dampings.

end Erdos821.P3Edge
