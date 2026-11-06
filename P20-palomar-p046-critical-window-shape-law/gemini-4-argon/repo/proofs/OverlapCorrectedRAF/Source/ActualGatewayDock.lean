module

public import proofs.OverlapCorrectedRAF.Source.RepositorySemanticCounting
public import proofs.OverlapCorrectedRAF.Asymptotic.GatewayProbability

@[expose] public section

namespace OverlapCorrectedRAF.Source

open RAF RAF.Polymer RAF.Concrete

def repositorySeedChannels (n t : Nat) : Finset (RepositoryChannel n) :=
  Finset.univ.filter fun r => RevSeedReaction (repositoryCRS n t) r

theorem repositorySeedChannel_factors_lt {n : Nat} {r : RepositoryChannel n}
    (hseed : RevSeedReaction (repositoryCRS n 2) r) :
    r.1.1.1.1 < 2 ∧ r.1.2.1.1 < 2 := by
  have hf : molLength r.1.1 ≤ 2 ∧ molLength r.1.2 ≤ 2 := by
    rcases hseed with hlhs | hrhs
    · have h : r.1.1 ∈ binaryFood n 2 ∧ r.1.2 ∈ binaryFood n 2 :=
        ⟨hlhs (by simp [repositoryCRS]), hlhs (by simp [repositoryCRS])⟩
      simpa only [binaryFood, Finset.mem_filter, Finset.mem_univ, true_and] using h
    · have hp : concatMolecule r.1.1 r.1.2 r.2.1 ∈ binaryFood n 2 := hrhs (by simp [repositoryCRS])
      simp only [binaryFood, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [concatMolecule, molLength_moleculeOfCode] at hp
      omega
  dsimp [molLength] at hf; omega

theorem repositorySeedChannels_card_le_34 (n : Nat) :
    (repositorySeedChannels n 2).card ≤ 34 := by
  rw [← card_repository_gateway_binary_t2, repositorySeedChannels, ← Fintype.card_subtype]
  let f (r : {r : RepositoryChannel n // RevSeedReaction (repositoryCRS n 2) r}) : RepositoryGateway 2 :=
    ⟨(⟨⟨r.1.1.1.1.1, (repositorySeedChannel_factors_lt r.2).1⟩, r.1.1.1.2⟩,
      ⟨⟨r.1.1.2.1.1, (repositorySeedChannel_factors_lt r.2).2⟩, r.1.1.2.2⟩), r.1.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨⟨⟨⟨ui, _⟩, uw⟩, ⟨⟨vi, _⟩, vw⟩⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨ui', _⟩, uw'⟩, ⟨⟨vi', _⟩, vw'⟩⟩, _⟩, _⟩ h
    cases h; rfl
  exact Fintype.card_le_of_injective f hf

end OverlapCorrectedRAF.Source
