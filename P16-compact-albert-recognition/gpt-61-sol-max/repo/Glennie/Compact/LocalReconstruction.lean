module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

public import Glennie.Compact.LocalContrast
public import Glennie.Compact.LocalOrbitQuotientR01

@[expose] public section
namespace Glennie.Compact.LocalReconstruction
noncomputable section

open Glennie
open Glennie.Compact.Affine20 Glennie.Compact.FlatOrbit
open Glennie.Compact.NearbyOrbits Glennie.Compact.NearbyOrbitsClosed
open Glennie.Compact.NativeQFamilyLedger Glennie.Compact.LocalContrast
open Glennie.Compact.Sections Glennie.Compact.PairNormNearby

def SameScoreSign (T S : Triple) : Prop :=
  (score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S)

/-- The existing local fibre theorem gives a finite-observation orbit test on actual frames. -/
theorem nearby_q26_score_complete (d : LocalOrbitQuotientR01.LocalData) :
    ∀ T S : Triple, (∀ a, Frame (T a)) → (∀ a, Frame (S a)) →
      encode20 (ledger54 T) ∈ d.V →
      score T ≠ 0 ∧
      ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔
        q26 T = q26 S ∧ SameScoreSign T S) := by
  intro T S hT hS hTV
  have hn := LocalOrbitQuotientR01.phi_ne_zero d ⟨T, hT, hTV⟩
  have hscore : score T ≠ 0 := by
    rw [score_eq_two_phi]
    exact mul_ne_zero (by norm_num) hn
  refine ⟨hscore, ?_⟩
  constructor
  · rintro ⟨k, hk⟩
    have hL : ledger54 T = ledger54 S := by rw [← hk, ledger54_map]
    have he : score T = score S := by
      rw [score_eq_two_phi, score_eq_two_phi,
        phiOf_eq_of_mem_autOrbit (show T ∈ autOrbit S from ⟨k, hk⟩)]
    exact ⟨(q26_eq_iff_ledger54_eq T S hT hS).mpr hL, by grind [SameScoreSign]⟩
  · rintro ⟨hq, hs⟩
    apply same_sign_rigidity T S hT hS ((q26_eq_iff_ledger54_eq T S hT hS).mp hq)
    unfold SameScoreSign at hs
    simp only [score_eq_two_phi] at hs
    grind

end
end Glennie.Compact.LocalReconstruction
