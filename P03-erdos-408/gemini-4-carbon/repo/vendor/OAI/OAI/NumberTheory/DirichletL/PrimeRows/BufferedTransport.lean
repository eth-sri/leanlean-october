module

public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport

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
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},f p ∂heightMeasure)=
      ∫w : ℝ,∫z : ℝ,∫x : ℝ in -H..H,f ((x,z),w) := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator f) heightMeasure := (integrable_indicator_iff hE).mpr hf
  rw [←integral_indicator hE,integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with w hw
  rw [integral_prod_symm _ hw]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have heq : (fun x : ℝ=>(E.indicator f) ((x,z),w))=(Icc (-H) H).indicator (fun x=>f ((x,z),w)) := by
    funext x
    simp only [Set.indicator_apply,E,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
  dsimp only
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith)]

variable {ι : Type*} [Fintype ι]

end SevenEighths.ProbeHighRowFamily

end

end OAI
