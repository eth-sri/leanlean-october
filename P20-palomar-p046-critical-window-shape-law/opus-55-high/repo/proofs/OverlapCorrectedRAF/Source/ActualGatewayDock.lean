module

public import proofs.OverlapCorrectedRAF.Source.RepositorySemanticCounting
public import proofs.OverlapCorrectedRAF.Asymptotic.GatewayProbability

@[expose] public section

namespace OverlapCorrectedRAF.Source

open RAF RAF.Polymer RAF.Concrete

def repositorySeedChannels (n t : Nat) : Finset (RepositoryChannel n) :=
  Finset.univ.filter fun r => RevSeedReaction (repositoryCRS n t) r

def lowerMolecule {n t : Nat} (x : Molecule n) (h : molLength x ≤ t) :
    Molecule t :=
  moleculeOfCode (by simp [molLength]) h x.2

@[simp] theorem molLength_lowerMolecule {n t : Nat} (x : Molecule n)
    (h : molLength x ≤ t) :
    molLength (lowerMolecule x h) = molLength x := by
  unfold lowerMolecule moleculeOfCode molLength
  dsimp

@[simp] theorem lowerMolecule_code {n t : Nat} (x : Molecule n)
    (h : molLength x ≤ t) :
    (lowerMolecule x h).2.val = x.2.val := by
  unfold lowerMolecule moleculeOfCode
  rfl

theorem lowerMolecule_injective_on {n t : Nat} {x y : Molecule n}
    {hx : molLength x ≤ t} {hy : molLength y ≤ t}
    (hxy : lowerMolecule x hx = lowerMolecule y hy) : x = y := by
  have hlen : molLength x = molLength y := by
    simpa only [molLength_lowerMolecule] using congrArg molLength hxy
  rcases x with ⟨xi, xv⟩
  rcases y with ⟨yi, yv⟩
  have hi : xi = yi := by
    apply Fin.ext
    have hval : xi.val + 1 = yi.val + 1 := by
      simpa only [molLength] using hlen
    omega
  subst yi
  have hcode := congrArg (fun z : Molecule t => z.2.val) hxy
  have hv : xv = yv := by
    apply Fin.ext
    simpa using hcode
  exact congrArg (Sigma.mk xi) hv

theorem repositorySeedChannel_factors_food {n : Nat}
    {r : RepositoryChannel n}
    (hseed : RevSeedReaction (repositoryCRS n 2) r) :
    r.1.1 ∈ binaryFood n 2 ∧ r.1.2 ∈ binaryFood n 2 := by
  rcases hseed with hlhs | hrhs
  · exact ⟨hlhs (by simp [repositoryCRS]),
      hlhs (by simp [repositoryCRS])⟩
  · have hp : concatMolecule r.1.1 r.1.2 r.2.1 ∈ binaryFood n 2 := by
      apply hrhs
      simp [repositoryCRS]
    simp only [binaryFood, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hsum : molLength r.1.1 + molLength r.1.2 ≤ 2 := by
      simpa only [concatMolecule, molLength_moleculeOfCode] using hp
    omega

def repositorySeedChannelToGateway {n : Nat}
    (r : {r : RepositoryChannel n //
      RevSeedReaction (repositoryCRS n 2) r}) : RepositoryGateway 2 := by
  have hfood := repositorySeedChannel_factors_food r.2
  have hu : molLength r.1.1.1 ≤ 2 := by
    simpa [binaryFood] using hfood.1
  have hv : molLength r.1.1.2 ≤ 2 := by
    simpa [binaryFood] using hfood.2
  let u := lowerMolecule r.1.1.1 hu
  let v := lowerMolecule r.1.1.2 hv
  refine ⟨(u, v), ?_⟩
  rcases r.1.2.2 with hdisplay | hprecedes
  · left
    intro heq
    apply hdisplay
    simpa [displayedConcat, u, v] using heq
  · right
    rcases hprecedes with hlen | ⟨hlen, hcode⟩
    · left
      simpa [moleculePrecedes, u, v] using hlen
    · right
      exact ⟨by simpa [u, v] using hlen,
        by simpa [u, v] using hcode⟩

theorem repositorySeedChannelToGateway_injective {n : Nat} :
    Function.Injective (@repositorySeedChannelToGateway n) := by
  intro r s hrs
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hrfood := repositorySeedChannel_factors_food r.2
    have hsfood := repositorySeedChannel_factors_food s.2
    have hru : molLength r.1.1.1 ≤ 2 := by
      simpa [binaryFood] using hrfood.1
    have hsu : molLength s.1.1.1 ≤ 2 := by
      simpa [binaryFood] using hsfood.1
    exact lowerMolecule_injective_on (hx := hru) (hy := hsu) (by
      simpa [repositorySeedChannelToGateway] using
        congrArg (fun z : RepositoryGateway 2 => z.1.1) hrs)
  · have hrfood := repositorySeedChannel_factors_food r.2
    have hsfood := repositorySeedChannel_factors_food s.2
    have hrv : molLength r.1.1.2 ≤ 2 := by
      simpa [binaryFood] using hrfood.2
    have hsv : molLength s.1.1.2 ≤ 2 := by
      simpa [binaryFood] using hsfood.2
    exact lowerMolecule_injective_on (hx := hrv) (hy := hsv) (by
      simpa [repositorySeedChannelToGateway] using
        congrArg (fun z : RepositoryGateway 2 => z.1.2) hrs)

theorem repositorySeedChannels_card_le_34 (n : Nat) :
    (repositorySeedChannels n 2).card ≤ 34 := by
  rw [← card_repository_gateway_binary_t2]
  rw [repositorySeedChannels, ← Fintype.card_subtype]
  exact Fintype.card_le_of_injective repositorySeedChannelToGateway
    repositorySeedChannelToGateway_injective

end OverlapCorrectedRAF.Source
