module
public import OAI.NumberTheory.DirichletL.PrimeRows.Ideal
public import OAI.NumberTheory.DirichletL.Detector.HighRowsRamified
public import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def ramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x w z (multiplicity p u.val)

theorem localCorrection_eq_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hPu : P.val∣Ideal.span {u.val})
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
  pm_3885
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  pm_3886
  pm_3888
  have hdiv : p∣u.val := Ideal.span_singleton_le_span_singleton.mp
    (by simp_all)
  have hj0 : multiplicity p u.val≠0 := ne_of_gt (multiplicity_pos_of_dvd hdiv
    (FiniteMultiplicity.of_prime_left hp u.property.1))
  pm_3491
  dsimp only at hgeom
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    have hpos : (0 : ℝ)<Ideal.absNorm (Ideal.span {p}) :=
      HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
    have he := evenRatio_eq_coordR _ hpos (actualACube η p) x z
    simp only [Complex.ofReal_natCast] at he
    rw [he]
    exact hgeom.2.1
  rw [localCorrection_ramified η u P hPu,←hspan,
    idealRowHighLocalFactor_canonical η u p hp hg.1 hg.2 hprimary hsp]
  have he := sourceRowSeries_ramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p) _ x w z hρ hgeom.1 hR
    hgeom.2.2.1 (multiplicity p u.val) hj0 (multiplicity_lt_six u p hp)
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  convert he using 1
  · simp only [sourceRowSeries,CubicEisenstein.fullIdealWeight,
      hP0,ite_false,Complex.ofReal_natCast,coordV]
    pm_5676
  · rfl

def ramifiedPrimes (S : Finset (Ideal O)) (u : FreeRow) : Finset PrimeIdeal :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).filter (fun P => P.val∉S)

end SevenEighths.ProbeHighRowFamily

end

end OAI
