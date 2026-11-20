module

public import RequestProject.UnivCoverIncl
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Vertex-chain naturality of actual cellular maps. -/
namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}

noncomputable def chain0 (f : Hom X Y) : (X.V →₀ ℤ) →ₗ[ℤ] (Y.V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ f.onV

/-- Actual cellular maps commute with the edge-to-vertex boundary. -/
theorem bdry1_chain1 (f : Hom X Y) (z : X.E →₀ ℤ) :
    bdry1 Y (chain1 f z) = chain0 f (bdry1 X z) := by
  finsupp_basis z
  intro e
  change bdry1 Y (Finsupp.mapDomain f.onE (Finsupp.single e 1)) = _
  simp_all [Finsupp.mapDomain_single, bdry1_single, map_sub, chain0, f.src_onE, f.tgt_onE]

/-- A cellular map sends one-cycles to one-cycles. -/
theorem chain1_cycle (f : Hom X Y) {z : X.E →₀ ℤ} (h : bdry1 X z = 0) :
    bdry1 Y (chain1 f z) = 0 := by rw [bdry1_chain1, h, map_zero]

end FiniteChains.Comb
