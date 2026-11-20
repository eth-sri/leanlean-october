module

public import RequestProject.GenusNonemptyWords

@[expose] public section

/-! Actual marking paths for the connected, nonempty-word base model.

-/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α)
  (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- Adding cancelling letters to empty retained relators leaves the actual
surface marking and its reading unchanged. -/
theorem genusNonempty_hread (s : PUnit) (x : ℕ × Bool) :
    Htpy (orderCx (PresPos (genusNonemptyW ρ a b q)))
      (ptBase (genusNonemptyW ρ a b q)) (ptBase (genusNonemptyW ρ a b q))
      ([] ++ mapPath (orderCxMap (genusNonemptyAtt ρ a b q)
        (genusNonemptyAtt ρ a b q).monotone) (gSig q x) ++ revPath [])
      (wordLoop (genusNonemptyW ρ a b q) (genusLw a b q s x)) := genus_read_surface_word a b q (w := genusNonemptyW ρ a b q) (j := Sum.inr PUnit.unit) rfl s x

end FiniteChains.Davis.Genus
