module

public import proofs.RAFReactionQuotient.SplitAdapter
public import proofs.RAFReactionQuotient.CapCompatibility

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem splitToOrdered_injective (n : ℕ) : Function.Injective (@splitToOrdered n) := by
  rintro ⟨ri, rw, rk⟩ ⟨si, sw, sk⟩ he
  have hp : (⟨ri, rw⟩ : Molecule n) = ⟨si, sw⟩ :=
    (split_concat _).symm.trans ((congrArg (fun q : OrderedChannel n => concatMolecule q.1.1 q.1.2 q.2) he).trans (split_concat _))
  have hl := congrArg (fun q : OrderedChannel n => molLength q.1.1) he
  cases hp
  cases Fin.ext (Nat.succ.inj (by simpa [splitToOrdered, reactionLeftLength] using hl))
  rfl

theorem split_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter (fun r : Reaction n => splitToQuotient r = j)).card ≤ 2 := by
  let S := Finset.univ.filter (fun r : Reaction n => splitToQuotient r = j)
  rw [← Finset.card_image_of_injective S (splitToOrdered_injective n)]
  refine (Finset.card_le_card fun q hq => ?_).trans (canonical_fibre_le_two j)
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩

end RAFReactionQuotient
