module

public import proofs.RAF.Core.CRS
public import Mathlib
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryCRS
public import proofs.HordijkSteelThreshold.PolymerCounts

@[expose] public section

namespace OverlapCorrectedRAF.Source

open RAF RAF.Polymer RAF.Concrete

def repositorySeedChannels (n t : Nat) : Finset (RepositoryChannel n) :=
  Finset.univ.filter fun r => RevSeedReaction (repositoryCRS n t) r

theorem repositorySeedChannels_card_le_34 (n : Nat) :
    (repositorySeedChannels n 2).card ≤ 34 := by
  rw [← card_repository_gateway_binary_t2, repositorySeedChannels, ← Fintype.card_subtype]
  have h (r : {r : RepositoryChannel n // RevSeedReaction (repositoryCRS n 2) r}) :
      molLength r.1.1.1 ≤ 2 ∧ molLength r.1.1.2 ≤ 2 := by
    have := r.2
    simp [RevSeedReaction, repositoryCRS, binaryFood, Finset.insert_subset_iff, concatMolecule] at this
    omega
  refine Fintype.card_le_of_injective (fun r => ⟨(⟨⟨r.1.1.1.1.val, by grind [molLength]⟩, r.1.1.1.2⟩,
    ⟨⟨r.1.1.2.1.val, by grind [molLength]⟩, r.1.1.2.2⟩), ?_⟩) ?_
  · simpa [displayedConcat, moleculePrecedes, molLength] using r.1.2.2
  · rintro ⟨⟨⟨⟨⟨a, _⟩, _⟩, ⟨⟨b, _⟩, _⟩⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨c, _⟩, _⟩, ⟨⟨d, _⟩, _⟩⟩, _⟩, _⟩ h
    simp_all

end OverlapCorrectedRAF.Source
