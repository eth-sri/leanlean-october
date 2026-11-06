
import proofs.RAFCriticalWindowQuantitative.SparseClosure
import proofs.RAFReactionQuotient.History
import proofs.RAFReactionQuotient.Surjectivity



namespace RAFCriticalWindowQuantitative
open RAFReactionQuotient RAF.Concrete RAF.Polymer OverlapCorrectedRAF.Source

variable (N : ℕ) (S : Finset (RepositoryChannel N))

/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
abbrev quotient_sparse_closure_length 
    (x : Molecule N) (hx : x ∈ quotientClosure N 2 S)  := by
  classical
  let f := Function.surjInv (splitToQuotient_surjective N)
  have he : (S.image f).image splitToQuotient = S := by simp [Finset.image_image,f]
  apply finite_iteration_length N (S.image f) S.card x
  rw [← split_closure_eq_quotient, he]
  exact (closureAt_exists_iff _ _ (closure_stable_at_channel_count _ _) x).mp (by simpa using hx)

end RAFCriticalWindowQuantitative
