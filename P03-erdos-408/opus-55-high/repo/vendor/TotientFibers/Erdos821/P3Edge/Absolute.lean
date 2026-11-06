module

public import Erdos821.P3Edge.CoeffBound
public import Erdos821.P3Edge.NormOsc
public import Erdos821.P3Edge.LargeX

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

lemma memoryWeight_pos (r : MemoryParameters F) (z : P.MemoryState (J + F.ell)) :
    0 < P.memoryWeight r.v z := by
  unfold PrimeGroups.memoryWeight
  exact pow_pos (lt_trans zero_lt_one r.v_gt) _

lemma memoryWeight_nonneg (r : MemoryParameters F) (z : P.MemoryState (J + F.ell)) :
    0 ≤ P.memoryWeight r.v z :=
  (memoryWeight_pos r z).le

lemma absoluteMemoryEdgeKernel_nonneg (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (s t : P.MemoryState (J + F.ell)) :
    0 ≤ absoluteMemoryEdgeKernel A n rho theta i .all s t := by
  unfold absoluteMemoryEdgeKernel
  apply mul_nonneg (edgeSymmetryFactor_nonneg P _)
  positivity

lemma norm_cast_absolute (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (s t : P.MemoryState (J + F.ell)) :
    ‖((absoluteMemoryEdgeKernel A n rho theta i .all s t : ℝ) : ℂ)‖ =
      absoluteMemoryEdgeKernel A n rho theta i .all s t := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (absoluteMemoryEdgeKernel_nonneg A n rho theta i s t)]

-- Coefficient norms: oscillation (pattern coeff * imaginaryPower, phase) has
-- modulus ≤ patternMass; rawEdgeWeight carries all masses/dampings.

end Erdos821.P3Edge
