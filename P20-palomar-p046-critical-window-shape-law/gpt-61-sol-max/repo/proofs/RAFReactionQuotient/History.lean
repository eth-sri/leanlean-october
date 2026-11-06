
import proofs.RAFReactionQuotient.QuotientMap
import proofs.RAFEmergenceApprox.GenericHistory
import proofs.HordijkSteelThreshold.GatewayCavity




namespace RAFReactionQuotient
open Classical unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold

variable (n L : ℕ)

noncomputable def quotientClosure  (S : Finset (RepositoryChannel n))  := Finset.univ.filter
      (fun x => ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k)

@[simp] theorem mem_quotientClosure {n L : ℕ} (S : _)
    (x : Molecule n) : x ∈ quotientClosure n L S ↔
      ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k := by
  simp [quotientClosure]

theorem quotientClosure_mono  : Monotone (quotientClosure n L) := by
  intro S T hST x hx
  obtain ⟨k,hk⟩ := (mem_quotientClosure S x).mp hx
  exact (mem_quotientClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

noncomputable def quotientCatalyticLaw (n : ℕ) (p : I) :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)

end RAFReactionQuotient
