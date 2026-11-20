module

public import PottsDiscontinuity.TorusLoops.LoopIncidence
public import PottsDiscontinuity.TorusLoops.BipartiteCirculations

/-!
# Winding is conserved at both primal and dual clusters

The sum of the boundary chains incident to one primal cluster is zero.
Dual translation reverses both displacement coordinates, giving the same
conservation law at dual clusters.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

noncomputable section

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

abbrev loopDisplacement (vertical : Bool) (q : Loop hN hM (rcSmoothing A)) : ℚ :=
  (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) (axisIncrement vertical) q : ℤ)

def loopDisplacementX (q : Loop hN hM (rcSmoothing A)) : ℚ :=
  (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) horizontalIncrement q : ℤ)

def loopDisplacementY (q : Loop hN hM (rcSmoothing A)) : ℚ :=
  (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) verticalIncrement q : ℤ)


end

open scoped Classical in
theorem sum_loopBoundaryCycle_fiber (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) :
    (∑ q with loopPrimalCluster hN hM A q = c, (loopBoundaryCycle hN hM A q).val) = 0 := by
  ext e
  simp only [Finset.sum_apply, Pi.zero_apply]
  change (∑ q with loopPrimalCluster hN hM A q = c,
    ((if directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
        (ribbonEndEquiv hN hM (e.val, true)) = q then (1 : ℚ) else 0) -
      (if directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
        (ribbonEndEquiv hN hM (e.val, false)) = q then (1 : ℚ) else 0))) = 0
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, loopPrimalCluster_end, sub_self]

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M) (vertical : Bool)

open scoped Classical in
theorem loopDisplacement_primal_sum
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) :
    (∑ q with loopPrimalCluster hN hM A q = c, loopDisplacement hN hM A vertical q) = 0 := by
  simp only [loopDisplacement, ← loopBoundaryCycle_displacement hN hM A]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.mul_sum]
  have he := congrFun (sum_loopBoundaryCycle_fiber hN hM A c) e
  simp only [Finset.sum_apply, Pi.zero_apply] at he
  simp [he]

private theorem loopDisplacement_translatedDual (q : Loop hN hM (rcSmoothing A)) :
    loopDisplacement hN hM (translatedDual A) vertical (translatedDualLoopEquiv hN hM A q) =
      -loopDisplacement hN hM A vertical q := by
  unfold loopDisplacement
  rw [loopSum_translatedDual]
  have hf : (fun d : Dart N M => axisIncrement vertical (dartColumnShift (edgeReverse d))) =
      fun d => -axisIncrement vertical d := by
    funext d
    rcases d with ⟨v, p⟩
    cases vertical <;> cases p <;> rfl
  rw [hf]
  simp only [loopSum, Finset.sum_neg_distrib, Int.cast_neg]

open scoped Classical in
private theorem loopDisplacement_dual_sum
    (c : (diamondOpenGraph hN hM true (translatedDual A)).ConnectedComponent) :
    (∑ q with loopDualCluster hN hM A q = c, loopDisplacement hN hM A vertical q) = 0 := by
  have h := loopDisplacement_primal_sum hN hM (translatedDual A) vertical c
  rw [Finset.sum_filter, ← (translatedDualLoopEquiv hN hM A).sum_comp] at h
  apply neg_eq_zero.mp
  rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine (Finset.sum_congr rfl fun q _ => ?_).trans h
  by_cases hq : loopDualCluster hN hM A q = c <;>
    simp [loopDisplacement_translatedDual, ← show
      loopDualCluster hN hM A q = loopPrimalCluster hN hM (translatedDual A)
        (translatedDualLoopEquiv hN hM A q) from rfl, hq]

theorem loopDisplacement_mem_incidenceCycleSpace :
    loopDisplacement hN hM A vertical ∈ LinearMap.ker (loopIncidenceBoundary hN hM A) := by
  classical
  ext v
  change Bipartite.boundary (loopPrimalCluster hN hM A) (loopDualCluster hN hM A)
    (loopDisplacement hN hM A vertical) v = 0
  cases v with
  | inl c => rw [Bipartite.boundary_inl, loopDisplacement_primal_sum]
  | inr c => simp [Bipartite.boundary_inr, loopDisplacement_dual_sum]

end

end
end PottsDiscontinuity.TorusLoops
