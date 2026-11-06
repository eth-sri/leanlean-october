
import proofs.RAF.Concrete.PolymerCRS




namespace OverlapCorrectedRAF.Source

open RAF.Polymer RAF.Concrete

variable {n : Nat}

/-- The exact order used when `create_XFR` builds its molecule list: shorter
words precede longer words, and equal-length words use binary-code order. -/
abbrev moleculePrecedes  (u v : Molecule n)  :=
  molLength u < molLength v ∨
    (molLength u = molLength v ∧ u.2.val ≤ v.2.val)

/-- Numeric code of the displayed concatenation `u ++ v`. -/
def displayedConcat  (u v : Molecule n)  :=
  u.2.val * 2 ^ molLength v + v.2.val

/-- Canonical representative of the repository's displayed-reaction quotient.
Both orientations are retained when `u ++ v` and `v ++ u` differ.  When they
coincide, the repository emits only the orientation whose first factor occurs
first in its molecule list. -/
abbrev RepositoryChannel (n : Nat) :=
  {uv : Molecule n × Molecule n //
    molLength uv.1 + molLength uv.2 ≤ n ∧
      (displayedConcat uv.1 uv.2 ≠ displayedConcat uv.2 uv.1 ∨
        moleculePrecedes uv.1 uv.2)}

/-- A fixed-food source gateway, represented in the intrinsic food type.  For
`t = 2` and `n ≥ 4`, every such pair embeds as a repository channel. -/
abbrev RepositoryGateway (t : Nat) :=
  {uv : Molecule t × Molecule t //
    displayedConcat uv.1 uv.2 ≠ displayedConcat uv.2 uv.1 ∨
      moleculePrecedes uv.1 uv.2}



end OverlapCorrectedRAF.Source
