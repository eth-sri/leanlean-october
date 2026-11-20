module

public import QPBT.Combining.Lines.SubLineSupport

/-! A line-point law is a uniform mixture of its coordinate-index fibers. -/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- Decode the line-point law from the independent uniform blocks. -/
theorem lineKindPointDist_eq_map_blocks (L : LdParams) (kind : LineKind) :
    lineKindPointDist L kind =
      (uniformDistribution ((LdPoint L) × (ScalarQ L × (LdPoint L)))).map
        (fun w => (lineDescOfBlock L kind w, w.1)) := by
  rw [← uniformDistribution_map_equiv (ldSpaceBlockEquiv L), Distribution.map_map]
  cases kind <;> simp [lineKindPointDist, sampledLine, lineDescOfBlock,
    aLineDescOfBlock, dLineDescOfBlock] <;> rfl

private theorem prod_bind_right {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (ρ : Distribution α) (μ : Distribution β) (ν : β → Distribution γ) :
    Distribution.prod ρ (Distribution.bind μ ν) =
      Distribution.bind μ (fun b => Distribution.prod ρ (ν b)) := by
  classical
  refine Distribution.ext_of_support_of_avgOver ?_ fun f => ?_
  · change ρ.support ×ˢ (μ.support.biUnion fun b => (ν b).support) =
      μ.support.biUnion (fun b => ρ.support ×ˢ (ν b).support)
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_product]
    grind
  · simp only [avgOver_bind, Distribution.avgOver_prod]
    exact avgOver_comm _ _ _

/-- The coordinate-index fibers of a uniform scalar seed are equiprobable. -/
theorem bind_ldSeedFiberDist (L : LdParams) [Nonempty (Fin L.m)] :
    Distribution.bind (uniformDistribution (Fin L.m)) (ldSeedFiberDist L) =
      uniformDistribution (ScalarQ L) := by
  letI : Nonempty (SeedResidue L) := Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold ldSeedFiberDist
  rw [bind_uniformDistribution_map]
  exact uniformDistribution_map_equiv (seedFiberEquiv L).symm

/-- For either kind, the line-point law is the uniform mixture over its seed fibers. -/
theorem lineKindPointDist_eq_bind_restricted (L : LdParams) (kind : LineKind)
    [Nonempty (Fin L.m)] :
    lineKindPointDist L kind =
      Distribution.bind (uniformDistribution (Fin L.m)) (restrictedLineDist L kind) := by
  rw [lineKindPointDist_eq_map_blocks, uniformDistribution_prod,
    uniformDistribution_prod (α := ScalarQ L), ← bind_ldSeedFiberDist L,
    Distribution.prod_bind_left, prod_bind_right, Distribution.bind_map]
  rfl

end
end MIPStarRE.QPBT
