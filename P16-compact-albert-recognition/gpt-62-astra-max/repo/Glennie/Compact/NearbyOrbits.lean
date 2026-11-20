module
public import Glennie.Compact.Sections
public import Glennie.Compact.FlatOrbit
@[expose] public section
namespace Glennie.Compact.NearbyOrbits
noncomputable section
open Affine20 Sections ChartTransfer FlatOrbit
theorem ledger54_eq_decode20 {T : Triple} (hT : ∀ a : Fin 3, Glennie.Frame (T a))
    {b : Fin 20 → ℝ} (hb : encode20 (fullLedger T) = b) :
    fullLedger T = decode20 b := by
  grind [decode_encode_frames]

export _root_.Glennie.SubmissionR03 (fibre54 fibre20)

theorem fibre_eq (b : Fin 20 → ℝ) : fibre20 b = fibre54 b := by
  ext T
  refine and_congr_right fun h => ⟨ledger54_eq_decode20 h, fun he => ?_⟩
  rw [he, encode20_decode20]

theorem phiOf_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    phiOf (mapAtoms g T) = phiOf T := phi_mapAtoms ..

/-- Hence constant on orbits. -/
theorem phiOf_eq_of_mem_autOrbit {S T : Triple} (h : T ∈ autOrbit S) :
    phiOf T = phiOf S := phi_eq_of_mem_autOrbit h

end
end Glennie.Compact.NearbyOrbits
