module

public import PottsDiscontinuity.RCMProof.Item3
public import PottsDiscontinuity.Duality.Discontinuity

@[expose] public section

open MeasureTheory Filter Topology Real

namespace PottsDiscontinuity

/-- Specialize the positive exact rate at the physical rapidity to separate
free and wired clusters. Both the Potts and RC assertions use this step. -/
theorem critical_cluster_probabilities (q : ℝ) (hq : 4 < q)
    (φ : Fin 2 → Measure FK.LatticeConfiguration)
    (hφ : ∀ i, IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, by show 1 ≤ q; linarith⟩) ⟨q, by show 0 < q; linarith⟩ i (φ i)) :
    φ 0 (RCInfinite.infiniteAt 0) = 0 ∧ 0 < φ 1 (RCInfinite.infiniteAt 0) ∧
      φ 1 Duality.existsInfiniteCluster = 1 ∧ φ 1 ≠ φ 0 := by
  obtain ⟨hl, hc⟩ := arcosh_pos_of_gt4 hq
  obtain ⟨S, _, hr, hp⟩ := RCMProof.rc_critical_rate q hq (hφ 0) _ hl hc
  exact Duality.critical_discontinuity_of_pos_diagonal_rate _ _ (hφ 0) (hφ 1) _ hp hr

/-- **Theorem 1.2**, items 1–3 including (1.2). -/
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
  let θ := FK.criticalParameters ⟨q, by grind⟩
  choose φ hφ using FK.exists_isRCInfiniteVolumeLimit_interior θ
  have hitem3free := RCMProof.rc_critical_rate q hq (hφ 0)
  obtain ⟨_, _, hone, hne⟩ := critical_cluster_probabilities q hq φ hφ
  refine ⟨φ, hφ, hne, ?_, ?_⟩
  · change (φ 1 Duality.existsInfiniteCluster).toReal = 1; simp [hone]
  intro lam hlam hcoshlam
  obtain ⟨s, hs, hr, _⟩ := hitem3free lam hlam hcoshlam
  exact ⟨s, hs, hr⟩

end PottsDiscontinuity
