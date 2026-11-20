module

public import Glennie.Compact.LocalContrast

@[expose] public section
namespace Glennie.Compact.LocalReconstruction
noncomputable section

open Glennie
open Glennie.Compact.Affine20 Glennie.Compact.FlatOrbit
open Glennie.Compact.NearbyOrbits
open Glennie.Compact.NativeQFamilyLedger Glennie.Compact.LocalContrast
open Glennie.Compact.Sections

def SameScoreSign (T S : Triple) : Prop :=
  (score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S)

open LocalOrbitQuotientR01

theorem complete (d : LocalData) (T S : Triple) (ht : ∀ a, Frame (T a)) (hs : ∀ a, Frame (S a))
    (hb : encode20 (fullLedger T) ∈ d.V) : score T ≠ 0 ∧
    (T ∈ autOrbit S ↔ q26 T = q26 S ∧ SameScoreSign T S) := by
  have ne := abs_pos.mp (lt_trans (by norm_num) (d.margin _ hb ⟨ht,ledger54_eq_decode20 ht rfl⟩))
  refine ⟨by rw [score_eq_two_phi]; exact mul_ne_zero (by norm_num) ne, ?_⟩
  simp only [SameScoreSign, score_eq_two_phi, q26_eq_iff_ledger54_eq T S ht hs]
  constructor
  · rintro ⟨g,rfl⟩
    simp only [phiOf_mapAtoms] at ne ⊢
    exact ⟨ledger54_map .., by rcases ne.lt_or_gt with h | h <;> simp [h, mul_neg_iff, mul_pos_iff]⟩
  · rintro ⟨hL, h⟩; apply PairNormNearby.rigid ht hs hL
    rcases h with ⟨_,_⟩ | ⟨_,_⟩ <;> first | left; constructor <;> linarith | right; constructor <;> linarith

end
end Glennie.Compact.LocalReconstruction
