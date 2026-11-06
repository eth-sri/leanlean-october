import RequestProject.ChamberZPoset
import RequestProject.CoverLevelComparison


/-!
# The construction `Z` is equivariant

The copies of the base are attached in every marked chamber by the *same* marked map `att`,
which depends on the mirror type of a cell only.  Therefore the deck action of the Coxeter group
on the poset of spherical cosets (`FiniteChains.Davis.sphAct`) lifts to the complex `Z` of
modified chambers, for every group element `k` that preserves the set `M` of marked chambers —
in the application, for every element of `Γ`.

* `FiniteChains.Davis.zAct` — the action of such a `k` on `Z`, and `FiniteChains.Davis.zActIso`
  its packaging as an order automorphism;
* `FiniteChains.Davis.inZChamber_zAct` — it carries the chamber of `w` to the chamber of `k w`;
* `FiniteChains.Davis.zAct_zNew` — it carries the copy of the base attached at `w` to the copy
  attached at `k w`, by the identity of `X`: the marked attaching map is the same in every
  chamber.

Only the action on `Z` is built here; the quotient of `Z` by this action and the resulting
covering description are not constructed.
-/
