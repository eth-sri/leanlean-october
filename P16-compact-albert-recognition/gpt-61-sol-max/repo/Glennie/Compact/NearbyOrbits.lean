module

public import Glennie.Compact.PairNormNearby
public import Glennie.Compact.FlatOrbit
public import Glennie.Compact.Sections

@[expose] public section

namespace Glennie.Compact.NearbyOrbits

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.PairNormNearby

noncomputable section
/-- Twenty chart coordinates pin all fifty-four ledger entries. -/
theorem ledger54_eq_decode20 {T : Triple} (hT : ∀ a : Fin 3, Glennie.Frame (T a))
    {b : Fin 20 → ℝ} (hb : encode20 (ledger54 T) = b) :
    ledger54 T = decode20 b := by
  subst hb
  exact (decode_encode_frames T hT).symm

/-- The FULL 54-entry fibre over a chart point: ordered frame triples whose complete ledger
is the decoded chart point. This is the set the target is about. -/
def fibre54 (b : Fin 20 → ℝ) : Set Triple :=
  {T : Triple | (∀ a : Fin 3, Glennie.Frame (T a)) ∧ ledger54 T = decode20 b}

/-- The 20-coordinate fibre over a chart point. -/
def fibre20 (b : Fin 20 → ℝ) : Set Triple :=
  {T : Triple | (∀ a : Fin 3, Glennie.Frame (T a)) ∧ encode20 (ledger54 T) = b}

theorem fibre20_eq_fibre54 (b : Fin 20 → ℝ) : fibre20 b = fibre54 b := by
  ext T
  constructor
  · exact fun ⟨hT, hb⟩ => ⟨hT, ledger54_eq_decode20 hT hb⟩
  · rintro ⟨hT, hb⟩
    exact ⟨hT, by rw [hb, ChartTransfer.encode20_decode20]⟩

theorem phiOf_eq_of_mem_autOrbit {S T : Triple} (h : T ∈ autOrbit S) :
    phiOf T = phiOf S := by
  obtain ⟨g, rfl⟩ := h
  exact phiOf_mapAtoms g S

theorem continuous_encode20 : Continuous (encode20 : Ledger54 → (Fin 20 → ℝ)) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [encode20, centred] <;> fun_prop

theorem abs_phi_eq (T S : Triple) (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))
    (hL : ledger54 T = ledger54 S) (hn : phiOf T ≠ 0) : |phiOf T| = |phiOf S| :=
  abs_eq_abs.mpr (sq_eq_sq_iff_eq_or_eq_neg.mp (nearby_core T S hT hS hL hn).1)


end
end Glennie.Compact.NearbyOrbits
