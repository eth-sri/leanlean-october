module
public import GS.Results.Nonmanifold
public import GS.Topology.QuaternionCone
public import GS.Unitary.RealEmbedding
public import GS.UnitaryNonmanifold.ScalarBridge
@[expose] public section

noncomputable section
open GS.Spectral GS.Isometric GS.Results
namespace GS.UnitaryTopology
/-- Use the very same reflection over the complexes. For odd block count its
anchored slice has positive width divisible by four. -/
theorem exists_unitary_nonEuclidean_point (q : ℕ) (hq : 3≤q) (hodd : Odd q) :
    ∃ M : CMat (q*2), M ∈ GS.UnitaryNonmanifold.localFamily q ∧
      ¬ EuclideanAtSubset (GS.UnitaryNonmanifold.localFamily q) M := by
  let o : Fin q := ⟨0,by omega⟩
  obtain ⟨Q,hne⟩ := reflection ℂ hq
  let e : (ℝ × ℂ) ≃L[ℝ] V 3 := .ofFinrankEq (by simp [V])
  refine ⟨_,family_singularity Q o hne e fun n => GS.RankLocus.three_row_bad n _ ?_ ?_⟩
  · rw [complex_width Q o hne]; exact pow_pos (by omega) _
  · obtain ⟨k,hk⟩ := hodd; rw [complex_width Q o hne]; exact ⟨k^2,by rw [show q-1 = 2*k by omega]; ring⟩
end GS.UnitaryTopology
