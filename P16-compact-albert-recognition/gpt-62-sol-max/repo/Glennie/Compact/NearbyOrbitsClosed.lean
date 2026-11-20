module
public import Glennie.Compact.PairNormNearby
public import Glennie.Compact.Sections
public import Glennie.Compact.NativeFlatRank20
public import Glennie.Compact.FrameTopology
@[expose] public section
namespace Glennie.Compact.NearbyOrbitsClosed
open Affine20 FlatBase FlatOrbit Sections NearbyOrbits PairNormNearby
noncomputable section


theorem exists_localData : Nonempty LocalData := by
  obtain ⟨e, he⟩ := Rank20.exists_equiv_of_det_ne_zero flatBase NativeFlatRank20.det_ne_zero_flatBase
  exact flat_two_sections e he

def localData : LocalData := Classical.choice exists_localData

namespace LocalData
variable (d : LocalData) {b : ChartPoint}

theorem ledgerPos (hb : b ∈ d.V) : ledger54 (d.pos b) = decode20 b :=
  ledger54_eq_decode20 (d.framePos b hb) (d.chartPos b hb)

theorem ledgerNeg (hb : b ∈ d.V) : ledger54 (d.neg b) = decode20 b :=
  ledger54_eq_decode20 (d.frameNeg b hb) (d.chartNeg b hb)

theorem phiPos (b) (hb : b ∈ d.V) : 0 < phiOf (d.pos b) :=
  lt_trans (by norm_num) (d.marginPos b hb)

theorem phiNeg (b) (hb : b ∈ d.V) : phiOf (d.neg b) < 0 :=
  lt_trans (d.marginNeg b hb) (by norm_num)

theorem margin_fibre (hb : b ∈ d.V) {T : Triple} (hT : T ∈ fibre54 b) :
    1 / 27 < |phiOf T| := by
  have hn := d.phiNeg b hb
  have hs := (nearby_core (d.neg b) T (d.frameNeg b hb) hT.1
    ((d.ledgerNeg hb).trans hT.2.symm) hn.ne).1
  rw [← (sq_eq_sq_iff_abs_eq_abs _ _).mp hs, abs_of_neg hn]
  linarith [d.marginNeg b hb]

theorem margin {T : Triple} (hT : IsFrameTriple T) (hb : encode20 (ledger54 T) ∈ d.V) :
    1 / 27 < |phiOf T| := d.margin_fibre hb ⟨hT, ledger54_eq_decode20 hT rfl⟩

theorem cover (b) (hb : b ∈ d.V) : fibre54 b = autOrbit (d.neg b) ∪ autOrbit (d.pos b) := by
  ext T
  constructor
  · intro hT
    have hn := abs_pos.mp (lt_trans (by norm_num) (d.margin_fibre hb hT))
    rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inl (orbit_of_same_sign T (d.neg b) hT.1 (d.frameNeg b hb)
        (hT.2.trans (d.ledgerNeg hb).symm) (Or.inl ⟨h, d.phiNeg b hb⟩))
    · exact Or.inr (orbit_of_same_sign T (d.pos b) hT.1 (d.framePos b hb)
        (hT.2.trans (d.ledgerPos hb).symm) (Or.inr ⟨h, d.phiPos b hb⟩))
  · rintro (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact ⟨frame_mapAtoms g _ (d.frameNeg b hb), (ledger54_map g _).trans (d.ledgerNeg hb)⟩
    · exact ⟨frame_mapAtoms g _ (d.framePos b hb), (ledger54_map g _).trans (d.ledgerPos hb)⟩

theorem disjoint (hb : b ∈ d.V) : Disjoint (autOrbit (d.neg b)) (autOrbit (d.pos b)) := by
  rw [Set.disjoint_left]
  intro T hN hP
  linarith [phiOf_eq_of_mem_autOrbit hN, phiOf_eq_of_mem_autOrbit hP, d.phiNeg b hb, d.phiPos b hb]

end LocalData
end
end Glennie.Compact.NearbyOrbitsClosed
