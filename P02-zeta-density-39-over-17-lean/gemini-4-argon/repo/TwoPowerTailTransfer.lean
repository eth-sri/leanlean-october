module
public import ActualCriticalTailReduction
public import Mathlib.MeasureTheory.Integral.Layercake

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

theorem shifted_power_tail_integral {v p : ℝ} (hv : 0 < v) (hp : 1 < p) :
    IntegrableOn (fun t : ℝ => (v+t)^(-p)) (Ioi 0) ∧
    (∫ t in Ioi 0,(v+t)^(-p))=v^(1-p)/(p-1) := by
  have hpre : (fun x : ℝ => x+v) ⁻¹' Ioi v=Ioi 0 := by
    ext x
    simp only [mem_preimage,mem_Ioi]
    constructor <;> intro h <;> linarith
  have hmp := measurePreserving_add_right (volume:Measure ℝ) v
  have he := (MeasurableEquiv.addRight v).measurableEmbedding
  have hi := (hmp.integrableOn_comp_preimage he).mpr
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hv)
  have hval := hmp.setIntegral_preimage_emb he (fun x : ℝ => x^(-p)) (Ioi v)
  rw [hpre] at hi hval
  have hex : -p+1=1-p := by ring
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) hv,hex] at hval
  constructor
  · simpa only [Function.comp_def,add_comm] using hi
  · calc
      _ = ∫ t in Ioi 0,(t+v)^(-p) := by congr 1; funext t; rw [add_comm]
      _ = -v^(1-p)/(1-p) := hval
      _ = _ := by rw [show (1:ℝ)-p=-(p-1) by ring,neg_div_neg_eq]

