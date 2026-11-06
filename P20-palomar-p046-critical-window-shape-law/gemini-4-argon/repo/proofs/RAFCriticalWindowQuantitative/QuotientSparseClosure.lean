module

public import proofs.RAFCriticalWindowQuantitative.SparseClosure
public import proofs.RAFReactionQuotient.History

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Concrete RAF.Polymer OverlapCorrectedRAF.Source

theorem quotient_sparse_closure_length (N : ℕ) (S : Finset (RepositoryChannel N))
    (x : Molecule N) (hx : x ∈ quotientClosure N 2 S) :
    molLength x ≤ 2^(S.card+1) :=
  crs_iteration_length (repositoryCRS N 2) rfl
    (fun r => ⟨r.val.1, r.val.2, concatMolecule r.val.1 r.val.2 r.property.1, rfl, rfl, by simp [concatMolecule]⟩)
    S x hx

end RAFCriticalWindowQuantitative
