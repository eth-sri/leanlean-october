module

public import OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow FourierBridge


def lowSingleSlotWeight (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : ActualEisensteinCubic.O)  :=
  star (HeckeFamily.elementCoeff η a)*W (elementNorm a/P)*logPhase (-t) (Real.log (elementNorm a/P))

lemma lowSelectedWeight_eq_product {K : ℕ}  η  (slots : Fin K→Finset ActualEisensteinCubic.O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)  t 
    (b : LowSelectedTuple slots J) :
    lowSelectedWeight η slots J W P t b=
      ∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val := by
  have he : HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val)=
      ∏i : SelectedSlot J,HeckeFamily.elementCoeff η (b i).val := map_prod (targetMonoid η) _ _
  unfold lowSelectedWeight lowSingleSlotWeight
  rw [he,star_prod]
  simp only [Finset.prod_mul_distrib,mul_assoc]

lemma lowSingleSlotWeight_norm  η   W   P t   a  :
    ‖lowSingleSlotWeight η W P t a‖≤‖W (elementNorm a/P)‖ := by
  rw [lowSingleSlotWeight,norm_mul,norm_mul,norm_star,logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)

end SevenEighths.ProbePhysical
end

end OAI
