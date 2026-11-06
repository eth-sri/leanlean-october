module
public import OAI.NumberTheory.DirichletL.PrimeRows.Principal
public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedHolomorphic
public import OAI.NumberTheory.DirichletL.Detector.CalibrationSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve

lemma calibration_nonzero_supported (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (a : O)
    (ha : (calibrationForSet S hS).residueMonoid a≠0) : Supported (Ideal.span {a}) := by
  have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp ha
  have hc := (CubicEisenstein.isUnit_quotient_span_iff _ _).mp hu
  have havoid := (calibrationForSet_coprime_iff S hS a).mp hc
  rw [supported_span_iff]
  constructor
  · intro hd
    exact havoid (Ideal.span {λ₀}) (hbad (Finset.mem_insert_self _ _))
      (Ideal.mem_span_singleton.mpr hd)
  · intro hd
    exact havoid (Ideal.span {(2:O)}) (hbad (by simp [CanonicalQuadraticSieve.fixedBadPrimes]))
      (Ideal.mem_span_singleton.mpr hd)

theorem calibrated_row_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1)
    (hcal : (calibrationForSet S hmax).residueMonoid u.val≠0) :
    (rowCharacter S hS u).residue≠1 := fun hp=>hu
      (rowCharacter_principal_supported_eq_one S hS hbad u
        (calibration_nonzero_supported S hmax hbad u.val hcal) hp)
