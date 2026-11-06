module
public import OAI.NumberTheory.DirichletL.PrimeRows.Unramified
public import OAI.NumberTheory.DirichletL.Detector.SourceExclusions
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def idealUnramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x w z

section
variable (η : Character) (u : FreeRow) (P : PrimeIdeal)
include η u P
theorem localCorrection_unramified_ideal
    (hs : Supported P.val) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
  pm_3885
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  pm_3886
  pm_3888
  have hu : IsCoprime u.val p := ((Ideal.isCoprime_span_singleton_iff p u.val).mp
    (by grind)).symm
  have he := localCorrection_unramified η u p hp hg.1 hg.2 hprimary hsp hu x w z hx hw hz
  have hP : (⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ : PrimeIdeal)=P := Subtype.ext hspan
  rw [hP] at he
  unfold actualUnramifiedClosed at he
  rw [←idealCoeff_span η hp.ne_zero,←idealRowHom_prime u.val (Ideal.span {p}) hg.1,hspan] at he
  exact he

theorem localCorrection_ramified
    (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    localCorrection η u P x w z=
      idealRowHighLocalFactor η u.val P.val x w z*(1-CubicEisenstein.fullIdealWeight (6*z) P.val) := by
  pm_6278
  have hr : idealRowHom u.val P.val=0 := idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu
  pm_403 localCorrection hr map_zero mul_zero zero_mul sub_zero mul_one div_one
end

end SevenEighths.ProbeHighRowFamily

end

end OAI
