module

public import Mathlib
public import PottsDiscontinuity.Frozen.Defs.IsRCInfiniteVolumeLimit
public import PottsDiscontinuity.Frozen.Defs.RCCriticalParameter
public import PottsDiscontinuity.Frozen.Defs.RCInfiniteOpenGraph
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.RCMProof.Item3
public import PottsDiscontinuity.TorusCrossing.Final

/-!
# Theorem statement `rc_theorem_1_2` (arXiv:1611.09877v2)

This declaration is reproduced verbatim in `Challenge.lean`; Comparator checks that the two
agree.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity

/-- **Theorem 1.2**, items 1–3 including (1.2) (arXiv:1611.09877v2, p. 4). -/
theorem rc_theorem_1_2 (q : ℝ) (hq : 4 < q) :
    ∃ φ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i
        (φ i)) ∧
      φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
              (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S))) := by
  classical
  let Q : Set.Ici (1 : ℝ) := ⟨q, Set.mem_Ici.2 (by linarith)⟩
  choose φ hφ using FK.exists_isRCInfiniteVolumeLimit_interior (FK.criticalParameters Q)
  have hrate := RCMProof.rcItem3ForEveryFreeLimit_proved TorusCrossing.h319_proved q hq _ (hφ 0)
  obtain ⟨hL, hc⟩ := arcosh_pos_of_gt4 q hq
  obtain ⟨S, hS, hr⟩ := hrate _ hL hc
  have hd := Duality.critical_discontinuity_of_pos_diagonal_rate Q _ _ (hφ 0) (hφ 1) _
    (RCMProof.altTanhLimit_pos hL hS) hr
  refine ⟨φ, hφ, hd.2.2.2, ?_, hrate⟩
  change (φ 1).real Duality.existsInfiniteCluster = 1
  simp [Measure.real_def, hd.2.2.1]

end PottsDiscontinuity
