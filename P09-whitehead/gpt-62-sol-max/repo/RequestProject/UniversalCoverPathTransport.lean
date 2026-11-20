module

public import RequestProject.CombPi2
public import RequestProject.CombPi1Conj

@[expose] public section

/-!
# Universal-cover transport along an actual path

A path `a : x ⟶ y` gives a cellular map from the universal cover based at `y`
to the universal cover based at `x`, by prefixing `a` to every represented
path.  Its projection is the identity on every underlying cell.  The map
intertwines deck transformations by the actual conjugation `pi1Conj ha`.
No equality of base points or connectedness hypothesis is used.

-/

namespace FiniteChains.Comb

universe u

variable {K : Complex2.{u}} {x y : K.V} {a : List (K.E × Bool)}
  (ha : IsPath K.src K.tgt a x y)

/-- Prefix transport intertwines the deck actions by conjugation along the same path. -/
theorem shiftHom_deckV (γ : Pi1 K y) (c : UV K y) :
    (shiftHom ha).onV (deckV γ c) =
      deckV (pi1Conj ha γ) ((shiftHom ha).onV c) := by
  induction γ using Quotient.ind with
  | _ g =>
      induction c using UV.ind with
      | h p =>
          apply UV.sound
          change Htpy K x (endpt K x (a ++ (g.1 ++ p.1)))
            (a ++ (g.1 ++ p.1)) ((a ++ g.1 ++ revPath a) ++ (a ++ p.1))
          rw [endpt_append, endpt_eq_of_isPath ha,
            endpt_append, endpt_eq_of_isPath g.2]
          have h := (htpy_revPath_append ha).congr_append (ha.append g.2) p.2
          simpa only [List.append_assoc, List.nil_append] using h.symm

end FiniteChains.Comb
