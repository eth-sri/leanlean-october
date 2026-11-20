module
public import Glennie.Compact.PairNormNearby
public import Glennie.Compact.NativeFlatRank20

/-! Compare every fibre member with the negative section first: equality of
squares gives the margin before we know which orbit it belongs to. -/
@[expose] public section
noncomputable section
namespace Glennie.Compact
open Affine20 PairNormNearby Sections FlatOrbit NearbyOrbits
namespace LocalOrbitQuotientR01
abbrev ChartPoint := Fin 20 → ℝ

/-- Only the exact section and whole-fibre facts needed for the quotient. -/
structure LocalData where
  V : Set ChartPoint
  openV : IsOpen V
  base : encode20 (fullLedger flatBase) ∈ V
  pos : ChartPoint → Triple
  neg : ChartPoint → Triple
  contPos : ContinuousOn pos V
  contNeg : ContinuousOn neg V
  framePos : ∀ b ∈ V, ∀ a : Fin 3, Frame (pos b a)
  frameNeg : ∀ b ∈ V, ∀ a : Fin 3, Frame (neg b a)
  chartPos : ∀ b ∈ V, encode20 (fullLedger (pos b)) = b
  chartNeg : ∀ b ∈ V, encode20 (fullLedger (neg b)) = b
  phiPos : ∀ b ∈ V, 0 < phiOf (pos b)
  bound : ∀ b ∈ V, phiOf (neg b) < -(1/27)

def localData : LocalData := Classical.choice <| by
  obtain ⟨e, he⟩ := NativeFlatRank20.flat_rank
  obtain ⟨V, ho, hb, p,n, cp,cn, fp,fn', lp,ln, hp,hn⟩ := flat_two_sections e he
  exact ⟨⟨V,ho,hb,p,n,cp,cn,fp,fn',lp,ln,hp,hn⟩⟩

namespace LocalData
variable (d : LocalData) (b : ChartPoint) (hb : b ∈ d.V)
include hb

theorem posL : fullLedger (d.pos b) = decode20 b := ledger54_eq_decode20 (d.framePos b hb) (d.chartPos b hb)
theorem negL : fullLedger (d.neg b) = decode20 b := ledger54_eq_decode20 (d.frameNeg b hb) (d.chartNeg b hb)
theorem phiNeg : phiOf (d.neg b) < 0 := lt_trans (d.bound b hb) (by norm_num)

theorem margin {T : Triple} (h : T ∈ fibre54 b) : 1/27 < |phiOf T| := by
  have hn := d.negL b hb
  have hs := (core (d.neg b) T (d.frameNeg b hb) h.1
    (hn.trans h.2.symm) (d.phiNeg b hb).ne).1
  rw [← (sq_eq_sq_iff_abs_eq_abs ..).mp hs, abs_of_neg (d.phiNeg b hb)]
  linarith [d.bound b hb]

theorem cover : fibre54 b = autOrbit (d.neg b) ∪ autOrbit (d.pos b) := by
  ext T; constructor
  · intro h
    have ne := abs_pos.mp (lt_trans (by norm_num) (d.margin b hb h))
    rcases lt_or_gt_of_ne ne with hn | hp
    · exact Or.inl (rigid h.1 (d.frameNeg b hb) (h.2.trans (d.negL b hb).symm) (.inl ⟨hn,d.phiNeg b hb⟩))
    · exact Or.inr (rigid h.1 (d.framePos b hb) (h.2.trans (d.posL b hb).symm) (.inr ⟨hp,d.phiPos b hb⟩))
  · rintro (⟨g,rfl⟩ | ⟨g,rfl⟩)
    · exact ⟨frame_mapAtoms _ _ (d.frameNeg b hb), (ledger54_map ..).trans (d.negL b hb)⟩
    · exact ⟨frame_mapAtoms _ _ (d.framePos b hb), (ledger54_map ..).trans (d.posL b hb)⟩

theorem disjoint : Disjoint (autOrbit (d.neg b)) (autOrbit (d.pos b)) := by
  rw [Set.disjoint_left]; intro T hn hp
  linarith [phiOf_eq_of_mem_autOrbit hn, phiOf_eq_of_mem_autOrbit hp, d.phiNeg b hb, d.phiPos b hb]
end LocalData
end LocalOrbitQuotientR01
end Glennie.Compact
