module

public import QPBT.Combining.Defs

/-!
# Uniform coordinate-index mixtures of the line-point laws

This module proves that the axis-parallel and diagonal line-point laws are the
uniform mixtures of their coordinate-index restrictions.  The identity rests on
the exact seed decomposition of `chiIndex`: the retained scalar seed is uniform,
so each of its `m` coordinate-index fibers carries mass `1 / m`, and every
line conditioning map keeps that seed.

## References

The mixture assertion is the opening sentence of blueprint
`lem:restricted-line-mixture-bounds`, formalizing the unlabelled observation at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`.
The restricted laws are blueprint `def:ith-restricted-line`, paper lines
1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-! ## The uniform coordinate-index law of the retained seed -/

variable (L : LdParams)

/-- The coordinate index of the retained seed of a uniformly sampled low-degree
vector is uniform.  Formalization-only auxiliary for blueprint
`def:ith-restricted-line`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem uniformDistribution_map_chiIndex_ldSeed :
    (uniformDistribution (LdSpace L)).map
        (fun z : LdSpace L => chiIndex L z.seed) =
      uniformDistribution (Fin L.m) := by
  classical
  haveI : Nonempty (ScalarQ L) := ⟨0⟩
  haveI :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [← Distribution.map_map,
    uniformDistribution_map_ldSeed, uniformDistribution_map_chiIndex]

/-! ## The mass of a coordinate-index event -/

/-- Every coordinate-index event of a line conditioning map that keeps the
shared scalar coordinate carries mass `1 / m`.  This is the equal-weight
statement behind blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem clDistribution_seedEvent_mass (i : Fin L.m)
    (CL : LdSpace L → LdSpace L)
    (hseed : ∀ z : LdSpace L, (CL z).seed = z.seed) :
    ∑ sample ∈
        (clDistribution CL (ldPointCL L)).support.filter
          (restrictedLineSeedEvent L i),
      (clDistribution CL (ldPointCL L)).weight sample = 1 / (L.m : ℝ) := by
  classical
  haveI :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [Distribution.sum_filter_weight_eq_avgOver]
  unfold clDistribution
  rw [Distribution.avgOver_map]
  have hpoint : ∀ z : LdSpace L,
      (if restrictedLineSeedEvent L i (CL z, ldPointCL L z) then (1 : ℝ)
        else 0) = if chiIndex L z.seed = i then 1 else 0 := by
    intro z
    by_cases h : chiIndex L z.seed = i
    · simp_all
      change _ = i
      rw [hseed]
      exact h
    · simp_all
      change ¬ _ = i
      rw [hseed]
      exact h
  simp [avgOver_congr _ _ _ hpoint, ← Distribution.avgOver_map (uniformDistribution (LdSpace L))
      (fun z : LdSpace L => chiIndex L z.seed)
      (fun j : Fin L.m => if j = i then (1 : ℝ) else 0), uniformDistribution_map_chiIndex_ldSeed]
  unfold avgOver
  simp [uniformDistribution_weight_apply]

/-! ## The two source mixture identities -/

end

end MIPStarRE.QPBT
