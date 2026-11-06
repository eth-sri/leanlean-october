module
public import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralSelected
public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedBounds
public import OAI.NumberTheory.DirichletL.Detector.RayPoolGood
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma row_phase_norm_one_of_not_dvd (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) :
    ‖idealRowHom u.val P.val‖=1 := by
  pm_3885
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg := supported_prime_data p hp (hspan.symm ▸ hs)
  pm_3492 u.val hn hspan
  pm_7812
  pm_683 he
  rw [he]
  exact Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p u.val hg.1 hg.2 hu) (by decide)

end SevenEighths.ProbeHighRowFamily
end

end OAI
