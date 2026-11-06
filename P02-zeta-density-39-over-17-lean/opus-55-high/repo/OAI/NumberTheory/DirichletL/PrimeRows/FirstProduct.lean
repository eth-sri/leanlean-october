module
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstTail
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

theorem unramifiedFactor_first_defect (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ) (eps : ℝ) (heps : 0<eps)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedFactor η u P x w z-1‖≤firstPrimeDefectBound eps P := by pm_3490 unramifiedClosed_first_region_bound

section
variable (eps : ℝ) (S : Finset (Ideal O)) (hS : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ) (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re)
include eps S hS η u x w z hx hz hw hxw
theorem unramifiedProduct_first_defect :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw) hS.half hS.small

theorem unramifiedProduct_first_multipliable :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_first_defect η u P.val (hS.norm_four P.val P.property)
      x w z eps hS.positive hx hz hw hxw
  pm_3892
end

end SevenEighths.ProbeHighRowFamily

end

end OAI
