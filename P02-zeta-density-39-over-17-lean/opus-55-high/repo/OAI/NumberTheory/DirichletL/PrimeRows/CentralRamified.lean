module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralRamifiedQuotient
public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_ramified_normalized (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (alpha eps : ℝ) (x w z : ℂ)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*eps)≤1/2)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50) :
    1/2≤‖ramifiedCorrection η u P hs x w z‖ ∧
    (P.val.absNorm:ℝ)^(-1:ℝ)*
      ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
        ramifiedCorrection η u P hs x w z‖≤
      800*(P.val.absNorm:ℝ)^(-(1/2:ℝ))+
        (if 2≤ multiplicity (primaryGenerator P.val) u.val then 12*(P.val.absNorm:ℝ)^(-w.re) else 0) := by
  pm_3885
  pm_3889 HeckeFamily.O
  pm_3886
  have ha : ‖actualACube η p‖≤1 := by
    pm_3467
    nlinarith [norm_nonneg (actualACube η p)]
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  pm_6718
  constructor
  · have hb := ramifiedClosed_central_lower p hp hg.1 hg.2 _ _ _ x w z alpha eps
      (hspan.symm ▸ hQ) (by simpa only [hnorm] using hsmall) (targetMonoid_norm_le_one η p) ha hρ
      halpha halpha1 heps heps1 hx hw hz (multiplicity p u.val) (multiplicity_lt_six u p hp)
    exact hb
  · rw [continuedCompensatedLocal_ramified η u P hs hP x w z]
    have hb := ramifiedSelected_central_quotient p hp hg.1 hg.2 _ _ _ x w z alpha eps
      (hspan.symm ▸ hQ) (by simpa only [hnorm] using hsmall) (targetMonoid_norm_le_one η p) ha hρ
      halpha halpha1 heps heps1 hx hw hz (multiplicity p u.val) (multiplicity_lt_six u p hp)
    dsimp only at hb
    simpa only [ramifiedCorrection,p,hnorm] using hb
end SevenEighths.ProbeHighRowFamily
end

end OAI
