module
public import OAI.NumberTheory.DirichletL.PrimeRows.MarkedCompensation
public import OAI.NumberTheory.DirichletL.PrimeRows.Continuation
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def continuedMarkedLocal (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    (multiplicity p u.val)

section
variable (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val) (x w z : ℂ)
include η u P hs x w z
theorem idealRowMarkedLocalFactor_eq_source :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
    let hg := (supported_prime_data p hp hsp).1
    idealRowMarkedLocalFactor η u.val P x w z=
      rowMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
        (multiplicity p u.val) := by
  dsimp only
  pm_3885
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  pm_3886
  pm_3888
  unfold idealRowMarkedLocalFactor rowMarkedSeries rowInner
  pm_3827
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η u.val x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have ht := bareIdealHighSummand_row_at_prime η p hp hg.1 hg.2 hprimary hsp
    (unitPart u p hp) (unitPart_coprime u p hp) (multiplicity p u.val) e.val l k m (by omega) x w z
  rw [←(canonical_decomposition u p hp).1] at ht
  pm_7351 ht hzero
  · simp only [completedValuationMark,hzero,ne_eq,not_true_eq_false,ite_false,zero_mul,
      rowMarkedTerm,ite_true]
  · simp only [completedValuationMark,hzero,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourceRowTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p)
      (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x w z
      (multiplicity p u.val) e.val l k m hzero

theorem continuedMarkedLocal_eq_initial
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedMarkedLocal η u P hs x w z=idealRowMarkedLocalFactor η u.val P x w z := by
  pm_3885
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  pm_3886
  pm_3491
  pm_934
  pm_5227 he evenRatio_eq_coordR actualACube z
  simp only [Complex.ofReal_natCast] at he
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [he]
    exact hgeom.2.1
  rw [idealRowMarkedLocalFactor_eq_source η u P hs x w z]
  unfold continuedMarkedLocal
  symm
  simpa only [hspan] using rowMarkedSeries_eq_closed p hp hg.1 hg.2 (targetMonoid η p)
    (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    _ hρ hgeom.1 hR (multiplicity p u.val) (multiplicity_lt_six u p hp)
end

end SevenEighths.ProbeHighRowFamily

end

end OAI
