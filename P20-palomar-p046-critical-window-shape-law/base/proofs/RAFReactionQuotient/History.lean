module

public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.RAFEmergenceApprox.GenericHistory
public import proofs.HordijkSteelThreshold.GatewayCavity

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold

noncomputable def quotientClosure (n L : ℕ) (S : Finset (RepositoryChannel n)) :
    Finset (Molecule n) := Finset.univ.filter
      (fun x => ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k)

@[simp] theorem mem_quotientClosure {n L : ℕ} (S : Finset (RepositoryChannel n))
    (x : Molecule n) : x ∈ quotientClosure n L S ↔
      ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k := by
  simp [quotientClosure]

theorem quotientClosure_mono (n L : ℕ) : Monotone (quotientClosure n L) := by
  intro S T hST x hx
  obtain ⟨k,hk⟩ := (mem_quotientClosure S x).mp hx
  exact (mem_quotientClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

noncomputable def quotientCatalyticLaw (n : ℕ) (p : I) :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)

/-- Entire adaptive histories, using the actual quotient food closure, have
the same law after replacement by deterministic cardinality prefixes. -/
theorem quotient_history_map (n L : ℕ) (p : I) (T : ℕ) :
    (quotientCatalyticLaw n p).map (fun ω => activeTrace
      (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) T) =
    (quotientCatalyticLaw n p).map (fun ω => activeTrace
      (fun C => RAFEmergenceApprox.Generic.catalystActive ω
        (finiteInitialSegment (Molecule n) C.card)) (quotientClosure n L) T) :=
  RAFEmergenceApprox.Generic.activeTrace_map_eq_scalar _ _ (quotientClosure_mono n L) T

end RAFReactionQuotient
