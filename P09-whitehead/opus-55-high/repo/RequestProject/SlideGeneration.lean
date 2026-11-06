import RequestProject.CoverChainComplex
import RequestProject.PresentationDictionary
import RequestProject.ExponentCorrection
import RequestProject.Cockcroft


/-!
# Rule 2 of Section 3.4 does not change `π₂`

Rule 2 of the operation `T` replaces an extra relator `r*` by

  `r⁰ = r* ∏_j r_j^{c_j}`,

a product of `r*` with core relators (`RequestProject/ExponentCorrection.lean` produces the
exponents `c`).  The paper justifies the generation property for this rule by

> Rule 2 is a finite sequence of slides of each extra relator disk over retained core disks.
> The inverse slides undo it.  It is a homotopy equivalence relative to `D`.

This file proves the corresponding statement in the combinatorial model.  The slide does not
change the normal closure of the relators (`FiniteChains.relSub_slideRel`), so both
presentations have the same fundamental group, and their second homotopy groups are the
modules of two-cycles of the same complex of `RequestProject/CoverChainComplex.lean`, taken
over `N = ⟪relators⟫`.  In that vocabulary the slide multiplies the Fox matrix by an
invertible unitriangular matrix:

* `FiniteChains.foxVec_mem_range_bdry2` — the Fox vector of an element of the normal closure
  of a family of words is a `ℤ[Q]`-combination of the Fox vectors of that family;
* `FiniteChains.exists_slideCoeff` — hence the coefficient vector `λ` of the slide exists,
  with `λ` vanishing at the slid index;
* `FiniteChains.bdry2_slideRel` — the boundary of the slid presentation expressed through the
  old one;
* `FiniteChains.slideCycle_image` and `FiniteChains.slideCycle_image_isCycle` — **rule 2 has
  the generation property**: the two-cycles of the slid presentation are exactly the images
  of the two-cycles of the old one under the `ℤ[Q]`-linear isomorphism `y ↦ y - y_{j₀} λ`;
* `FiniteChains.slide_cockcroft` — consequently rule 2 preserves the Cockcroft property.
-/
