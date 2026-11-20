module

public import Glennie.Compact.Sections.Reversal
public import Glennie.Compact.FlatOrbit
@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20

def fibre54 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (IsFrameTriple T) ∧ fullLedger T = decode20 b}
def fibre20 (b : Fin 20 → ℝ) : Set Triple :=
  {T | (IsFrameTriple T) ∧ encode20 (fullLedger T) = b}

end
end Glennie.SubmissionR03

namespace Glennie.Compact.NearbyOrbits

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The twenty chart coordinates and the fifty-four ledger entries are the same fibre

This section is the whole content of the coordinate shortcut, and it is unconditional. The
sharper tool is `Affine20.decode_encode_frames` (`Affine20/Chart.lean`), which PINS the
value `ledger54 T = decode20 b` rather than merely comparing two triples;
`Affine20.encode20_injOn` (`:344`) is the injectivity form and follows. Both rest on
`Affine20.ledger54_inDomain` (`:80`), which holds for ARBITRARY genuine frame triples with no
nearness, no genericity and nothing about sections.

What this buys and what it does not: it collapses the 54-versus-20 distinction completely,
so "full-54" is a redundant adjective wherever both fibres are in play. It says NOTHING about
how many orbits sit in a fibre, nothing about non-emptiness of a nearby fibre, and nothing
about Phi -- which is not a function of the ledger at all. It is load-bearing at exactly one
step below: it is what puts an arbitrary fibre member, known only by its twenty chart
coordinates, inside a neighbourhood of a 54-entry ledger VALUE. -/

/-- Twenty chart coordinates pin all fifty-four ledger entries. -/
theorem ledger54_eq_decode20 {T : Triple} (hT : IsFrameTriple T)
    {b : Fin 20 → ℝ} (hb : encode20 (ledger54 T) = b) :
    ledger54 T = decode20 b := by
  subst hb
  exact (decode_encode_frames T hT).symm

export Glennie.SubmissionR03 (fibre54 fibre20)

/-- Unconditional, for every chart point, with no hypothesis whatever. -/
theorem fibre20_subset_fibre54 (b : Fin 20 → ℝ) : fibre20 b ⊆ fibre54 b := by
  rintro T ⟨hT, hb⟩
  exact ⟨hT, ledger54_eq_decode20 hT hb⟩

theorem fibre20_eq_fibre54 (b : Fin 20 → ℝ) : fibre20 b = fibre54 b := by
  refine Set.Subset.antisymm (fibre20_subset_fibre54 b) ?_
  rintro T ⟨hT, hL⟩
  exact ⟨hT, hL.symm ▸ ChartTransfer.encode20_decode20 b⟩

/-! ## 2. Phi in the sections' spelling

`FlatOrbit` writes Phi out as `phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))`; the
sections use `Sections.phiOf` (`Sections/Reversal.lean`). `phiOf_apply` is `rfl`, so
these are repackagings and not new mathematics. They are needed because the two halves of
the argument speak the two spellings. -/

/-- Phi in `phiOf` spelling is a diagonal-action invariant. -/
theorem phiOf_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    phiOf (mapAtoms g T) = phiOf T := by exact phi_mapAtoms g T

/-- Hence constant on orbits. -/
theorem phiOf_eq_of_mem_autOrbit {S T : Triple} (h : T ∈ autOrbit S) :
    phiOf T = phiOf S := by exact phi_eq_of_mem_autOrbit h

end
end Glennie.Compact.NearbyOrbits
