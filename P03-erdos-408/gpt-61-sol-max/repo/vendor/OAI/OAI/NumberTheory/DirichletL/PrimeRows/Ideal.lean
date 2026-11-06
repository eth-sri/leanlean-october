module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.PrimeRows.Unramified
public import OAI.NumberTheory.DirichletL.Detector.SourceExclusions

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss


def idealUnramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ)  :=
  unramifiedClosed P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x w z

theorem localCorrection_unramified_ideal  η   u   P 
    (hs : Supported P.val) (hcop : IsCoprime P.val (Ideal.span {u.val}))
     x w z  (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal HeckeFamily.O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hu : IsCoprime u.val p := ((Ideal.isCoprime_span_singleton_iff p u.val).mp
    (by rw [hspan]; exact hcop)).symm
  have he := localCorrection_unramified η u p hp hg.1 hg.2 hprimary hsp hu x w z hx hw hz
  have hP : (⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ : PrimeIdeal)=P := Subtype.ext hspan
  rw [hP] at he
  unfold actualUnramifiedClosed at he
  rw [←idealCoeff_span η hp.ne_zero,←idealRowHom_prime u.val (Ideal.span {p}) hg.1,hspan] at he
  exact he

theorem localCorrection_ramified  η   u   P 
    (hP : P.val∣Ideal.span {u.val})  x w z  :
    localCorrection η u P x w z=
      idealRowHighLocalFactor η u.val P.val x w z*(1-CubicEisenstein.fullIdealWeight (6*z) P.val) := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  have hr : idealRowHom u.val P.val=0 := idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu
  simp_all [localCorrection]

end SevenEighths.ProbeHighRowFamily

end

end OAI
