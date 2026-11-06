import proofs.RAFReactionQuotient.QuotientMap

import proofs.RAF.Core.CRS
import Mathlib
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.BigOperators.Ring.Finset
import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryCRS
import proofs.HordijkSteelThreshold.PolymerCounts



namespace OverlapCorrectedRAF.Source

variable {n : ℕ}
open RAF.Polymer RAF.Concrete

def repositorySeedChannels (n t : Nat)  :=
  Finset.univ.filter (RevSeedReaction (repositoryCRS n t))

variable {t : Nat} (x : Molecule n) (h : molLength x ≤ t)

def lowerMolecule   :=
  moleculeOfCode (by simp [molLength]) h x.2







theorem lowerMolecule_injective_on {n t : Nat} {x y : Molecule n}
    {hx : _} {hy : molLength y ≤ t}
    (hxy : lowerMolecule x hx = lowerMolecule y hy) : x = y := by
  exact RAFReactionQuotient.molecule_ext
    (congrArg (@molLength t) hxy)
    (congrArg (fun z : Molecule t => z.2.val) hxy)



theorem repositorySeedChannel_factors_food 
    {r : RepositoryChannel n}
    (hseed : RevSeedReaction (repositoryCRS n 2) r) :
    r.1.1 ∈ binaryFood n 2 ∧ r.1.2 ∈ binaryFood n 2 := by
  rcases hseed with hlhs | hrhs
  · grind [repositoryCRS]
  · have hp : concatMolecule r.1.1 r.1.2 r.2.1 ∈ binaryFood n 2 := by
      apply hrhs
      simp [repositoryCRS]
    simp [binaryFood] at hp ⊢
    have hsum  := by
      simpa [concatMolecule] using hp
    omega

def repositorySeedChannelToGateway 
    (r : {r : RepositoryChannel n //
      RevSeedReaction (repositoryCRS n 2) r}) : RepositoryGateway 2 := by
  have hfood := repositorySeedChannel_factors_food r.2
  have hu : molLength r.1.1.1 ≤ 2 := by grind [binaryFood]
  have hv : molLength r.1.1.2 ≤ 2 := by grind [binaryFood]
  let u := lowerMolecule r.1.1.1 hu
  let v := lowerMolecule r.1.1.2 hv
  refine ⟨(u, v), ?_⟩
  clear x h
  measurability





end OverlapCorrectedRAF.Source
