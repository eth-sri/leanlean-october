/- Exact unproved dependency propositions. Definitions here assert no theorem. -/
module
public import Glennie.Native

@[expose] public section
namespace Glennie

/-- An actual invertible real-linear map preserving the native product and trace.
No orbit, spectral, pair-reduction, or endpoint conclusion is a structure field. -/
structure CompactAutomorphism where
  equiv : Albert ≃ₗ[ℝ] Albert
  map_jordan : ∀ x y, equiv (jordan x y) = jordan (equiv x) (equiv y)
  map_trace : ∀ x, trace (equiv x) = trace x

def IsDiagonal (x : Albert) : Prop := x.o01 = 0 ∧ x.o02 = 0 ∧ x.o12 = 0

/-- The fixed ordinary complex line is span(1,i) inside the first quaternion. -/
def OctInComplex (x : Octonion) : Prop := x.1.imJ = 0 ∧ x.1.imK = 0 ∧ x.2 = 0

def InComplexSector (x : Albert) : Prop :=
  OctInComplex x.o01 ∧ OctInComplex x.o02 ∧ OctInComplex x.o12

/-- Includes every pair, with zero slots and repeated spectra; presently unproved. -/
def UniversalPairReduction : Prop := ∀ x y : Albert,
  ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) ∧ InComplexSector (g.equiv y)

end Glennie
