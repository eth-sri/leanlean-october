module

public import proofs.RAFCriticalWindowQuantitative.SparseClosure
public import proofs.RAFReactionQuotient.History

public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Concrete RAF.Polymer OverlapCorrectedRAF.Source

/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
theorem quotient_closure_length {N : ℕ} (S : Finset $ RepositoryChannel N)
    (x : Molecule N) (hx : x ∈ quotientClosure N 2 S) : molLength x ≤ 2^(S.card+1) := by
  obtain ⟨k, hk⟩ := (mem_quotientClosure _ _).1 hx
  exact closure_length _ (by simp [repositoryCRS, binaryFood]) (fun r B => by
    simp [repositoryCRS, concatMolecule]; omega) S k x hk

end RAFCriticalWindowQuantitative
