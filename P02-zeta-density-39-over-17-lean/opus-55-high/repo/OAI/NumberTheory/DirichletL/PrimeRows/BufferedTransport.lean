module
public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma height_slab_integral_wzx (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},f p ∂ heightMeasure)=
      ∫w : ℝ,∫z : ℝ,∫x : ℝ in -H..H,f ((x,z),w) := by
  pm_3483
  pm_6717
  rw [←integral_indicator hE,integral_prod_symm _ hi]
  pm_8497 hi.prod_left_ae integral_prod_symm
  apply Filter.Eventually.of_forall
  intro z
  have heq : (fun x : ℝ=>(E.indicator f) ((x,z),w))=(Icc (-H) H).indicator (fun x=>f ((x,z),w)) := by
    funext x
    pm_94 Set.indicator_apply E Set.mem_ofPred_eq Set.mem_Icc abs_le
  dsimp only
  pm_7999 heq

variable {ι : Type*} [Fintype ι]

end SevenEighths.ProbeHighRowFamily

end

end OAI
