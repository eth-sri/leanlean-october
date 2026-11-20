module
public import ADR11.Nonbinary.Theorem9

@[expose] public section
namespace ADR11.Challenge
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (_ : σ.IsBinary)
    (_ : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := proposition11_theorem9 hX σ σ' h

theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (_ : σ.IsBinary)
    (_ : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := proposition11_theorem9_four hX σ σ'

end ADR11.Challenge
