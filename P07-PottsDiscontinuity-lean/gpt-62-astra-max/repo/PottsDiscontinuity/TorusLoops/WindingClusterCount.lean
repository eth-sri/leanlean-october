module

public import PottsDiscontinuity.TorusLoops.WindingCirculations
public import PottsDiscontinuity.TorusLoops.WindingLoopCount

/-!
# At most two winding boundary loops per primal cluster

The two conserved displacement coordinates form circulations in the same
at-most-one-dimensional incidence circulation space. A scalar combination can
be chosen with exactly their joint support. The finite support-degree theorem
then gives the factor two in the loop-to-cluster count.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

private theorem exists_combination_joint_support {E : Type*} [Fintype E]
    (x y : E → ℚ) : ∃ a : ℚ, ∀ e, x e + a * y e = 0 ↔ x e = 0 ∧ y e = 0 := by
  classical
  obtain ⟨a, ha⟩ := (Finset.univ.image fun e => -x e / y e).exists_notMem
  refine ⟨a, fun e => ?_⟩
  grind

theorem mem_windingLoopSet_iff_displacement (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    q ∈ windingLoopSet hN hM i j A ↔
      loopDisplacementX q ≠ 0 ∨ loopDisplacementY q ≠ 0 := by
  classical
  have hx : loopDisplacementX q = 0 ↔
      loopSum (horizontalCross i) q = 0 := by
    rw [loopDisplacementX, loop_horizontal_displacement _ i q]
    simp only [Int.cast_mul, Int.cast_natCast, mul_eq_zero, Nat.cast_eq_zero,
      Int.cast_eq_zero, (Fin.pos i).ne', false_or]
  have hy : loopDisplacementY q = 0 ↔
      loopVertical j q = 0 := by
    rw [loopDisplacementY, loop_vertical_displacement _ j q]
    simp only [Int.cast_mul, Int.cast_natCast, mul_eq_zero, Nat.cast_eq_zero,
      Int.cast_eq_zero, (Fin.pos j).ne', false_or]
  simp only [windingLoopSet, Finset.mem_filter, Finset.mem_univ, true_and]
  grind

open scoped Classical in
/-- No actual primal cluster has more than two incident essential boundary loops. -/
theorem windingLoops_per_primalCluster_le_two (hN : Even N) (hM : Even M)
    (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent) :
    ((windingLoopSet hN hM i j A).filter fun q => loopPrimalCluster (hN := hN) (hM := hM) (A := A) q = c).card ≤ 2 := by
  classical
  obtain ⟨a, ha⟩ := exists_combination_joint_support
    (loopDisplacementX (hN := hN) (hM := hM) (A := A)) (loopDisplacementY (hN := hN) (hM := hM) (A := A))
  let f := fun q =>
    loopDisplacementX (hN := hN) (hM := hM) (A := A) q + a * loopDisplacementY (hN := hN) (hM := hM) (A := A) q
  have hf :=
    (LinearMap.ker _).add_mem (loopDisplacementX_mem_incidenceCycleSpace hN hM A)
      ((LinearMap.ker _).smul_mem a (loopDisplacementY_mem_incidenceCycleSpace hN hM A))
  have hk := finrank_loopIncidenceCycleSpace_le_one hN hM (Fin.pos i) (Fin.pos j) A
  have hb := Bipartite.primal_support_degree_le_two f hf hk c
  have he : (Finset.univ.filter fun q => f q ≠ 0 ∧ loopPrimalCluster q = c) =
      (windingLoopSet hN hM i j A).filter (fun q => loopPrimalCluster q = c) := by
    ext q
    have hs : f q ≠ 0 ↔ loopDisplacementX q ≠ 0 ∨
        loopDisplacementY q ≠ 0 := by
      grind
    simp [Finset.mem_filter, Finset.mem_univ, true_and, hs, mem_windingLoopSet_iff_displacement]
  grind

end PottsDiscontinuity.TorusLoops
