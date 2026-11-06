module
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Detector.RadialIdentity

public import OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTuple
public import OAI.NumberTheory.DirichletL.Detector.PhysicalNorms

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow

local notation "Id" => Ideal ActualEisensteinCubic.O

alias physicalElementNorm_pos := _root_.OAI.SevenEighths.ProbePhysical.elementNorm_pos

section
variable {K : ℕ}
include K

section
variable (p : Fin K→ActualEisensteinCubic.O)
include p

lemma elementNorm_slotProduct     (J : Finset (Fin K)) :
    elementNorm (slotProduct p J)=∏i∈J,elementNorm (p i) := by
  induction J using Finset.induction_on with
  | empty => simp [slotProduct,elementNorm_one]
  | @insert i J hi ih => simpa only [slotProduct,Finset.prod_insert hi,elementNorm_mul] using congrArg (fun x=>elementNorm (p i)*x) ih

section
variable (hp : ∀i,p i≠0) (J : Finset (Fin K))
include hp J

lemma slotProduct_nonzero         :
    slotProduct p J≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

lemma slotProduct_norm_pos         :
    0<elementNorm (slotProduct p J) := physicalElementNorm_pos _ (slotProduct_nonzero p hp J)

end

end

def compensationSubsetCoefficient {K } (η : HeckeFamily.Character)
    (p : Fin K→ActualEisensteinCubic.O) (J : Finset (Fin K))  :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (slotProduct p (Finset.univ\J)))

def compensationSubsetProbe {K } (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→ActualEisensteinCubic.O) (J : Finset (Fin K)) (X Y Z : ℝ)  :=
  compensationSubsetCoefficient η p J*
    markedPhysicalProbe η C (Ideal.span {slotProduct p (Finset.univ\J)}) W0 W1
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))

section
variable (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
include η C W0 W1

lemma compensatedTuple_eq_subsets      
       p   X Y Z  :
    compensatedTuple η C W0 W1 p X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,compensationSubsetProbe η C W0 W1 p J X Y Z := rfl

lemma compensatedPhysicalProbe_eq_subsets      
       slotPrimes 
     W   P   X Y Z  :
    compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : ActualEisensteinCubic.O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            compensationSubsetProbe η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [compensatedTuple_eq_subsets,Finset.mul_sum]
  exact Finset.sum_comm

end

end

end SevenEighths.ProbePhysical
end

end OAI
