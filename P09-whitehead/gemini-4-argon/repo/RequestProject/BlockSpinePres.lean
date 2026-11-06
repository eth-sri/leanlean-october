module

public import RequestProject.SubstOneWay
public import RequestProject.PresPosetReading
public import RequestProject.ChamberQuotientCover
public import RequestProject.CombLoopWord
public import RequestProject.TreePresentation
public import RequestProject.CombPi1Conj

@[expose] public section

/-!
# The block of the article: its spine, its marked presentation, its loops and its fillings

`RequestProject/SubstOneWayQuotient.lean` reduces the injectivity of the structural homomorphism
`FiniteChains.BlockFamily.substHomF` of the actual substitution to a marked homomorphism of each
substituted block into the fundamental group of the quotient `Q = Z/Γ` of the model of modified
chambers.  This file constructs that homomorphism **for the block itself**, and constructs the
block presentation it is defined on **from the geometry of the block**, not as data.

The block is the truncated cube complex

    `M = C(L) ∖ (the all-positive vertex)`,

which inside the quotient is the poset `FiniteChains.Davis.QOld A` of retained cubes; the
boundary of the chamber — the cut surface — is the subposet of the cubes `(σ, 0)` of a nonempty
simplex `σ`, that is, the image of `FiniteChains.Davis.posQCube`.  Everything is read off the
two-dimensional order complex of that poset:

* `FiniteChains.Davis.spineGens` — the **internal generators** `Z` of the block: the edges of
  the block outside a spanning tree of its one-skeleton (the generators of the presentation
  carried by the two-dimensional spine of the block);
* `FiniteChains.Davis.spineBeta` — the **relators** `β_m` of the marked presentation
  `B_q = ⟨s_h, t_h, Z ∣ β_m⟩`: one relator for every two-cell of the block, and one *marking
  relator* for every distinguished generator `s_h`, which says that `s_h` is the word spelled by
  the corresponding loop of the cut surface inside the block;
* `FiniteChains.Davis.blockToQ` — the **geometric loops**: the homomorphism which carries the
  class of a loop of the block to its class in `Q`, conjugated to the base point of the copy of
  the base along the fixed path through the cylinder;
* `FiniteChains.Davis.blockToQ_surfLoop` — the **cylinder computation**: the class in `Q` of a
  loop of the cut surface, read through the block, equals the class of its image under the
  attaching map, read through the base copy.  This is the naturality homotopy of the mapping
  cylinder, and it is what makes the marking relators die;
* `FiniteChains.Davis.injective_substHomF_of_spine` — **the application**: for the marked
  presentation just constructed, the structural homomorphism of the actual simultaneous
  substitution is injective.  The relators of the block are filled by the two-cells of the block
  (`FiniteChains.Comb.SpanningTree.freeToPi1_treeRel`) and the marking relators by the cylinder;
  the only remaining input is the attaching map itself, through the hypothesis that it reads the
  prescribed old word `u_h` along the chosen loop of the cut surface.
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V}

/-- The retained cubes of `C(L)` form a poset: the face order of the cubes. -/
instance : PartialOrder (QOld A) := Subtype.partialOrder _

/-! ### The cut surface inside the block -/

/-- The cube `(σ, 0)` of a nonempty simplex `σ`: a cell of the cut surface, that is, of the part
of the block which is glued to the copy of the base. -/
def posQCube (σ : NeSpx A) : QOld A :=
  ⟨⟨σ.1, 0, σ.2.2, fun _ _ => rfl⟩, fun h => (Finset.nonempty_iff_ne_empty.mp σ.2.1) h.1⟩

theorem posQCube_monotone : Monotone (posQCube (A := A)) := fun _ _ h => ⟨h, fun _ _ => rfl⟩

/-- The cut surface as a cellular map into the block. -/
def surfCx (A : CommRel V) : Hom (orderCx (NeSpx A)) (orderCx (QOld A)) :=
  orderCxMap posQCube posQCube_monotone


variable {X : Type u} [Preorder X] {att : NeSpx A →o X}

/-- The block inside the quotient `Q`: a retained cube is a cell of `Q`. -/
def qOldIncl (c : QOld A) : Qpos A X att := qOld c.1 c.2

theorem qOldIncl_monotone : Monotone (qOldIncl (X := X) (att := att)) := fun _ _ h => h

/-- The block as a cellular map into the quotient. -/
def blockCx (A : CommRel V) (X : Type u) [Preorder X] (att : NeSpx A →o X) :
    Hom (orderCx (QOld A)) (orderCx (Qpos A X att)) :=
  orderCxMap qOldIncl qOldIncl_monotone

/-- **The defining relation of the cylinder**: the image of a cell of the cut surface under the
attaching map lies below that cell. -/
theorem qNew_att_le_qOldIncl (σ : NeSpx A) :
    (qNew (A := A) (att := att) (att σ)) ≤ qOldIncl (posQCube σ) :=
  ⟨rfl, σ.2.1, le_refl _⟩
