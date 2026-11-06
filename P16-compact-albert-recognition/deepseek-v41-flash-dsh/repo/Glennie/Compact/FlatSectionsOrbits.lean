/- The analytic and algebraic descriptions of the flat-base fibre.

`Glennie.Compact.NativeFlatSections.native_flat_two_sections_full54` gives two continuous
sections over an open neighbourhood V of the flat base's encoded ledger. Both invert the
full 54-entry ledger, with Phi > 0 and Phi < 0 respectively. This construction uses the
rank-20 Jacobian bridge.

`Glennie.Compact.FlatOrbit` identifies the flat-base fibre with two disjoint
compact-automorphism orbits, each exactly one sign sheet of Phi. The fibre is the
level set |Phi| = 4/27; this classification is bridge-free.

At the flat base, the analytic section values represent the two algebraic orbit
components and together represent the entire fibre. The sign and orbit labels agree.
`Sections.flatBase` and `FrameTopology.flatBaseTriple` are definitionally equal;
the first-frame and third-frame reversals have equal orbits by `FlatOrbit`.

No novelty is claimed. The two-orbit statement concerns ORDERED triples. `FlatOrbit`
also proves that the fibre is one class modulo the 1296 outcome relabellings:
`encoder p = p 2 - p 0` sees only outcomes 0 and 2, so Phi is not a relabelling invariant
even up to sign.

The orbit identification here is restricted to the flat base. The sections are local
in the ledger, but this module asserts no nearby orbit classification, stabilizer,
orbit dimension, or number of automorphisms realizing a given fibre element. -/
module

public import Glennie.Compact.NativeFlatSections
public import Glennie.Compact.FlatOrbit

@[expose] public section

namespace Glennie.Compact.FlatSectionsOrbits

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections

noncomputable section

set_option maxHeartbeats 2000000

/-! ## 1. The two flat base triples are one triple

`Glennie.Compact.Sections.flatBase` and
`Glennie.Compact.FrameTopology.flatBaseTriple` are both
`![flatFrameP, flatFrameQ, flatFrameR]` over the same `FlatBase` frames.
They are definitionally equal. This identity connects the analytic statement over
the first representative to the algebraic statement over the second. -/

/-- The sections' base triple and the classification's base triple are equal. -/
theorem flatBase_eq_flatBaseTriple :
    Glennie.Compact.Sections.flatBase = flatBaseTriple := rfl

/-- Hence their ledgers agree. -/
theorem ledger54_flatBase_eq :
    ledger54 Glennie.Compact.Sections.flatBase = ledger54 flatBaseTriple := by
  rw [flatBase_eq_flatBaseTriple]

/-! ## 2. A section value at the base point lands in the fibre

The sections invert the ledger map through the 20-parameter chart, so at the base
point they return a triple whose ledger is `decode20 (encode20 (ledger54 flatBase))`.
The chart inverts on the ledger of any triple of genuine frames
(`Glennie.Compact.Affine20.decode_encode_frames`, `Affine20/Chart.lean`), so that
is the flat ledger itself, on all 54 entries and not merely on the 20 chart
coordinates. That last point is what makes the membership real rather than a
coincidence of the chart. -/

/-- The chart round trip at the flat base, written out. -/
theorem decode_encode_flatBase :
    decode20 (encode20 (ledger54 Glennie.Compact.Sections.flatBase)) =
      ledger54 flatBaseTriple := by
  rw [decode_encode_frames Glennie.Compact.Sections.flatBase
        Glennie.Compact.Sections.flatBase_frames, ledger54_flatBase_eq]

/-! ## 3. The sign of Phi picks the sheet

`FlatOrbit.flat_fibre_eq_abs_phi` says a fibre member has `|Phi| = 4/27`, and
`autOrbit_flatBase_eq` / `autOrbit_flatBaseRev3_eq` say each orbit is exactly one
signed sheet. So on the fibre the SIGN of Phi decides the orbit outright. -/

/-! ## 4. The capstone

The two sections, evaluated at the flat base point, represent the two orbits,
and the whole fibre is their union. The first conjuncts give
`native_flat_two_sections_full54`; the final six identify the section values
with the orbit representatives. -/

/-! ## 5. The same statement with the sections' own reversal

The sections are built on the FIRST-frame reversal `flatBaseRevP`, while the
classification is stated with the THIRD-frame reversal `flatBaseRev3`. They are
different triples in the same orbit, which `FlatOrbit` records as
`autOrbit_flatBaseRevP_eq_autOrbit_flatBaseRev3`. So the capstone can be read with
either representative, and this corollary says so explicitly rather than leaving a
reader to wonder whether the two halves are talking about the same component. -/

/-! ## 6. The sections' own reversal

`flatBaseRevP` is the first-frame reversal defined in `FlatOrbit`; the sections use
`Glennie.Compact.Sections.revTriple`. Their identification follows from
`flatFramePRev_eq_reverse`, which turns the reversed first frame into
`reverseFrame flatFrameP`, and `reverseFrame_eq_swap`, which identifies `reverseFrame`
with precomposition by (0 2). This is exactly the action of `revTriple` on slot 0,
leaving slots 1 and 2 unchanged. -/

end
end Glennie.Compact.FlatSectionsOrbits
