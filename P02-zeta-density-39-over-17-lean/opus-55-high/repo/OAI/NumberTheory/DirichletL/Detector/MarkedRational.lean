module
public import OAI.NumberTheory.DirichletL.Detector.MarkedLocal
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def idealMarkedClosed (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  let R := coordR Q (actualAPhase η (primaryGenerator P.val)) x z
  markedFactor R (coordV Q z) (Q:ℂ)⁻¹ (coordK Q (HeckeFamily.idealCoeff η P.val) x w)
    (-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x+coordW Q 1 w*R) 1

theorem idealMarkedLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hz : 1/6<z.re) :
    idealMarkedLocalFactor η P x w z=idealMarkedClosed η P x w z := by
  pm_3885
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  pm_3886
  pm_3887
  pm_3850
  have he := principalMarkedSeries_eq p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) hV (by grind)
  have hsource := idealMarkedLocalFactor_eq_source η P hs x w z
  dsimp only at hsource
  rw [hsource]
  pm_5227 hk coordK_eq_geometric targetMonoid w
  simp only [Complex.ofReal_natCast] at hr hk
  rw [hr,←hk] at he
  simp only [actualACube_sq] at he
  convert he using 1
  grind
  · simp only [idealMarkedClosed,coordD,coordW,star_one,mul_one,one_mul]
    simp only [hspan,p,targetMonoid_primaryGenerator η P.val hs,Complex.ofReal_natCast,neg_mul]

end SevenEighths.ProbePhysical
end

end OAI
