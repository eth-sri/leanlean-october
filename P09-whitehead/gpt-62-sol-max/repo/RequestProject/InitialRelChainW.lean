module

public import RequestProject.InitialComplex
public import RequestProject.FoxNaturality
public import RequestProject.PresentationDictionary
public import RequestProject.NecessityAlgebraicMod
public import RequestProject.CycleLifting
public import RequestProject.Pi2Dictionary
public import RequestProject.CoverComplex
public import RequestProject.ChainFormula
public import RequestProject.FinitelyDeterminedInf
public import RequestProject.Pigeonhole
public import RequestProject.CoverChainComplex
public import RequestProject.FoxCommutator
public import RequestProject.TorsionFreeGroupRing
public import RequestProject.ChainFormulaMod
public import RequestProject.PresCockcroftDictionary
public import RequestProject.CombPi2
public import RequestProject.SubgroupCompactness
public import RequestProject.CombHurewicz1Pres
public import RequestProject.CombCellularIso
public import RequestProject.MapChainDescent

@[expose] public section

/-! The cellular two-boundary of a presentation is its exponent-sum matrix. -/

namespace FiniteChains
namespace Comb

universe u

variable {I J : Type u} [DecidableEq I]
variable (r : J → FreeGroup I)

/-! ### Acyclicity of the presentation complex, read off the exponent-sum matrix -/

theorem bdry2_presComplex_eq_expMatrix :
    bdry2 (presComplex r) = expMatrix r := by
  refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring ?_
  show bdry2 (presComplex r) (Finsupp.single j 1)
    = expMatrix r (Finsupp.single j 1)
  rw [bdry2_pres_single, expMatrix, Finsupp.linearCombination_single, one_smul]
  rfl

end Comb
end FiniteChains
