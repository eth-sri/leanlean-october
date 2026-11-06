/- The algebraic readout of the signed invariant on ordered frame triples. -/
module

public import Glennie.Compact.NearbyOrbitsClosed
public import Glennie.Compact.OperationalPhi
public import Glennie.Compact.NativeQFamilyLedger

@[expose] public section
namespace Glennie.Compact.LocalContrast

open Glennie
open Glennie.Compact.Affine20
open Glennie.Compact.Sections
open Glennie.Compact.OperationalPhi

section


export Glennie.SubmissionR03 (score)

theorem score_eq_two_phi (T : Triple) : score T = 2 * phiOf T := phi_division_free (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

end
end Glennie.Compact.LocalContrast
