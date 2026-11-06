module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.S2.MemoryMassBounds

public import Erdos821.P3Clean.Structure
public import Erdos821.P3Clean.Contractions

/-! The damping factors of a literal clean edge. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups} {F : FixedData}

def pendingDamping {M } (rho : ℝ) (s : P.MemoryState M)  :=
  rho ^ (∑ g : P.BigGroup, (_root_.Erdos821.S2Core.zeroMemoryIndices (s.2.2 g)).card)

section
variable {M : ℕ} (r : MemoryParameters F) (s : P.MemoryState M)

theorem pendingDamping_nonneg       :
    0 ≤ pendingDamping r.rho s := pow_nonneg r.rho_pos.le _

theorem pendingDamping_le_one       :
    pendingDamping r.rho s ≤ 1 := pow_le_one₀ r.rho_pos.le r.rho_lt.le

end

section
variable {J m : ℕ} (A : Model F P J m) (n : ℕ)

theorem rawEdgeWeight_rho        rho 
    (ν : Pattern P J F.ell m) (u : P.Aux J)
    (s t : P.MemoryState (J + F.ell)) (c : _root_.Erdos821.S2Core.TransferChoice s) :
    _root_.Erdos821.S2Core.rawEdgeWeight A n rho ν u s t c =
      pendingDamping rho s * _root_.Erdos821.S2Core.rawEdgeWeight A n 1 ν u s t c * pendingDamping rho t := by
  simp only [_root_.Erdos821.S2Core.rawEdgeWeight, one_pow, mul_one, pendingDamping, pow_add]
  ring

theorem edgeChoiceCoefficient_rho      
     rho theta   i  (s t : P.MemoryState (J + F.ell)) (c : _root_.Erdos821.S2Core.EdgeChoice A s) :
    _root_.Erdos821.S2Core.edgeChoiceCoefficient A n rho theta i s t c =
      (pendingDamping rho s : ℂ) * _root_.Erdos821.S2Core.edgeChoiceCoefficient A n 1 theta i s t c *
        (pendingDamping rho t : ℂ) := by
  simp only [_root_.Erdos821.S2Core.edgeChoiceCoefficient]
  rw [rawEdgeWeight_rho A n rho (A.pattern c.2.2.1) c.2.2.2.1
    (_root_.Erdos821.S2Core.permuteActive c.1 s) (_root_.Erdos821.S2Core.permuteActive c.2.1 t) c.2.2.2.2]
  simp only [Complex.ofReal_mul]
  change ((pendingDamping rho s : ℂ) * _ * (pendingDamping rho t : ℂ)) * _ * _ = _
  ring

theorem memoryEdgeKernel_rho      
     rho theta   i  (mode : _root_.Erdos821.S2Core.TransferMode)
    (phi : (s t : P.MemoryState (J + F.ell)) → _root_.Erdos821.S2Core.EdgeChoice A s → ℂ)
    (s t : P.MemoryState (J + F.ell)) :
    _root_.Erdos821.S2Core.memoryEdgeKernel A n rho theta i mode phi s t =
      (pendingDamping rho s : ℂ) * _root_.Erdos821.S2Core.memoryEdgeKernel A n 1 theta i mode phi s t *
        (pendingDamping rho t : ℂ) := by
  classical
  have hc (c : _root_.Erdos821.S2Core.EdgeChoice A s) :
      (if _root_.Erdos821.S2Core.edgeChoiceValid A mode i s t c then
        _root_.Erdos821.S2Core.edgeChoiceCoefficient A n rho theta i s t c * phi s t c else 0) =
      (pendingDamping rho s : ℂ) *
        (if _root_.Erdos821.S2Core.edgeChoiceValid A mode i s t c then
          _root_.Erdos821.S2Core.edgeChoiceCoefficient A n 1 theta i s t c * phi s t c else 0) *
        (pendingDamping rho t : ℂ) := by
    by_cases h : _root_.Erdos821.S2Core.edgeChoiceValid A mode i s t c
    · rw [ite_eq_left h, ite_eq_left h, edgeChoiceCoefficient_rho]
      ring
    · simp only [ite_eq_right h, mul_zero, zero_mul]
  simp only [_root_.Erdos821.S2Core.memoryEdgeKernel]
  simp_rw [hc]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end

theorem memoryMass_nonneg  J n 
    (hV : ∀ g, 0 < P.V g)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
     s  : 0 ≤ P.memoryMass F J n s := by solve_by_elim [_root_.Erdos821.S2Core.memoryMass_nonneg]

end Erdos821.P3Clean
