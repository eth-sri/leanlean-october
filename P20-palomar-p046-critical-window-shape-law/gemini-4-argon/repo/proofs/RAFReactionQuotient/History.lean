module

public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.RAFEmergenceApprox.GenericHistory
public import proofs.HordijkSteelThreshold.GatewayCavity

@[expose] public section

namespace RAFReactionQuotient
open Classical unitInterval RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold

noncomputable def quotientClosure (n L : ℕ) (S : Finset (RepositoryChannel n)) :
    Finset (Molecule n) := Finset.univ.filter
      (fun x => ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k)

@[simp] theorem mem_quotientClosure {n L : ℕ} (S : Finset (RepositoryChannel n))
    (x : Molecule n) : x ∈ quotientClosure n L S ↔
      ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k := by
  simp [quotientClosure]

theorem quotientClosure_mono (n L : ℕ) : Monotone (quotientClosure n L) :=
  fun _ _ hST _ hx =>
    let ⟨k, hk⟩ := (mem_quotientClosure _ _).mp hx
    (mem_quotientClosure _ _).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

noncomputable def quotientCatalyticLaw (n : ℕ) (p : I) :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)

end RAFReactionQuotient
