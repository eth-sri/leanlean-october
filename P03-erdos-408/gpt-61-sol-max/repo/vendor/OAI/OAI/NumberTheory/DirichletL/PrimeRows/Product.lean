module

public import OAI.NumberTheory.DirichletL.PrimeRows.Ramified

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss


def unramifiedFactor (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ)  :=
  if P.val∣Ideal.span {u.val} then 1 else idealUnramifiedCorrection η u P x w z

def unramifiedProduct (S : Finset (Ideal HeckeFamily.O)) (η : Character) (u : FreeRow) (x w z : ℂ)  :=
  ∏' P : {P : PrimeIdeal // P.val∉S},unramifiedFactor η u P.val x w z

section
variable (S : Finset (Ideal HeckeFamily.O)) (hS : CorrectionTail S) (η : Character) (u : FreeRow) (P : PrimeIdeal) (hP : 4≤P.val.absNorm) (x w z : ℂ) (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re)

include hP hx hw hz in
theorem unramifiedFactor_defect      
       
          :
    ‖unramifiedFactor η u P x w z-1‖≤globalPrimeDefectBound P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using globalPrimeDefectBound_nonneg P
  · apply unramifiedClosed_open_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact hx
    · exact hw
    · exact hz

include hS hx hw hz in
theorem unramifiedProduct_multipliable    
         
          :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S} =>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S} => unramifiedFactor η u P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S} => globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

end

end SevenEighths.ProbeHighRowFamily

end

end OAI
