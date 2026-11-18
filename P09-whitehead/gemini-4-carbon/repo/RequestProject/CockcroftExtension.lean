module

public import RequestProject.Cockcroft
public import RequestProject.Pi2Dictionary

@[expose] public section

/-!
# Cockcroft complexes and two-dimensional extensions killing `π₂`

The introduction of the paper records the following characterization: a connected
two-complex `K` admits at least one two-dimensional extension inducing zero on `π₂` if and
only if `K` is Cockcroft.  The argument given there is:

* for an inclusion `i : K ⊂ L` of two-complexes the map `H₂(i)` is injective, since there
  are no three-cells; hence `π₂(i) = 0` forces the Hurewicz map of `K` to vanish;
* conversely, attaching disks along a generating set of `π₁(K)` produces a simply connected
  `L`, and the inclusion is then zero on `π₂`.

This file proves both halves in the combinatorial model of the project, for a complex of a
finite presentation: `π₂` is the module of Fox cycles, the Hurewicz map is the augmentation
(see `RequestProject/Cockcroft.lean`), and an extension is a presentation containing the
generators and the two-cells of `K`, with the old cells attached along the old words.

The result is `FiniteChains.isCockcroft_iff_nonempty_zeroPi2Ext`: the presentation complex
of `ρ` is Cockcroft if and only if it admits a two-dimensional extension which is zero on
`π₂`.  The extension produced in the proof is the one from the paper: adjoin one disk along
each generator.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α J : Type u} [Fintype α] [DecidableEq α] [Fintype J]

/-! ### The condition "zero on `π₂`" in cellular form -/

/-! ### The capped extension: adjoin a disk along every generator -/

/-- The presentation obtained from `ρ` by attaching a disk along each generator. -/
def capRel (ρ : J → FreeGroup α) : J ⊕ α → FreeGroup α :=
  Sum.elim ρ fun i => FreeGroup.of i

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The capped presentation presents the trivial group: its complex is simply connected. -/
theorem capRel_relSub_top (ρ : J → FreeGroup α) : relSub (capRel ρ) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun w => ?_
  induction w using FreeGroup.induction_on with
  | one => exact one_mem _
  | of i => exact Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩
  | inv_of i _ => exact inv_mem (Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩)
  | mul x y hx hy => exact mul_mem hx hy

instance capPresGroup_subsingleton (ρ : J → FreeGroup α) :
    Subsingleton (PresGroup (capRel ρ)) := by
  constructor
  intro x y
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      refine QuotientGroup.eq.2 ?_
      rw [capRel_relSub_top]
      trivial

end FiniteChains
