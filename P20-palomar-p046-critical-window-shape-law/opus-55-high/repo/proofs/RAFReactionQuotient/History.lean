module

public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.RAFEmergenceApprox.GenericHistory
public import proofs.HordijkSteelThreshold.GatewayCavity

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold

section
variable (n L : ℕ)

noncomputable def quotientClosure  (S : Finset $ RepositoryChannel n) :
    Finset (Molecule n) := Finset.univ.filter
      (∃ k, · ∈ revClosureAt (repositoryCRS n L) S k)

@[simp] theorem mem_quotientClosure {n L : ℕ} (S : Finset $ RepositoryChannel n)
    (x : Molecule n) : x ∈ quotientClosure n L S ↔
      ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k := by
  simp [quotientClosure]

theorem quotientClosure_mono  : Monotone (quotientClosure n L) := by
  intro S T hST x hx
  obtain ⟨k,hk⟩ := (mem_quotientClosure S x).mp hx
  exact (mem_quotientClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

end

noncomputable def quotientCatalyticLaw (n : ℕ) (p : I) :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)

end RAFReactionQuotient
