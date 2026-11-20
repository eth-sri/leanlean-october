module

public import RequestProject.UnivCoverIncl

@[expose] public section

/-! Vertex-chain naturality of actual cellular maps. -/
namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}

variable (f : Hom X Y)

noncomputable def chain0 :=
  Finsupp.lmapDomain ℤ ℤ f.onV

/-- Actual cellular maps commute with the edge-to-vertex boundary. -/
theorem bdry1_chain1 (z : X.E →₀ ℤ) :
    bdry1 Y (chain1 f z) = chain0 f (bdry1 X z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp_all
  | single e n =>
      change bdry1 Y (Finsupp.mapDomain f.onE (Finsupp.single e n)) = _
      simp [Finsupp.mapDomain_single, bdry1_single, map_smul, map_sub, chain0, f.src_onE, f.tgt_onE]

end FiniteChains.Comb
