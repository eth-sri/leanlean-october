import Mathlib.Tactic

import RequestProject.UnivCoverIncl

/-! Vertex-chain naturality of actual cellular maps. -/
namespace FiniteChains.Comb
variable {X Y : Complex2.{u}}

noncomputable def chain0 (f : Hom X Y)  :=
  Finsupp.lmapDomain ℤ ℤ f.onV

/-- Actual cellular maps commute with the edge-to-vertex boundary. -/
theorem bdry1_chain1 (f : Hom X Y) (z : X.E →₀ ℤ) :
    bdry1 Y (chain1 f z) = chain0 f (bdry1 X z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single e n =>
      change bdry1 Y (Finsupp.mapDomain f.onE (Finsupp.single e n)) = _
      rw [Finsupp.mapDomain_single, bdry1_single, bdry1_single, map_smul, map_sub]
      simp [chain0, f.src_onE, f.tgt_onE]

end FiniteChains.Comb
