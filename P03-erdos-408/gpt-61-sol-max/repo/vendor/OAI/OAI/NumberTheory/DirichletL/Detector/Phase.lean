module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Foundation

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

def G (a : O)  := fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)

def reciprocitySign (a b : O)  :=
  (quadraticRaySign (residue a) (residue b) : ℂ)

section
variable (a b : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (hb : EisensteinEPrimaryPhase.odd (residue b)) (c : O)

include ha hb in
theorem G_mul  
     
      :
    G (a * b) = G a * G b * reciprocitySign a b := by
  change fixedGValue (residue (a * b)) = fixedGValue (residue a) * fixedGValue (residue b) * reciprocitySign a b
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_mul, mul_inv_rev, residue_mul]
  rw [quadraticRayValue_mul _ _ ha hb]
  unfold reciprocitySign
  ring

theorem reciprocitySign_mul_right   :
    reciprocitySign a (b * c) = reciprocitySign a b * reciprocitySign a c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_right, Int.cast_mul]

include ha hb in
theorem reciprocitySign_sq  
     
      :
    reciprocitySign a b ^ 2 = 1 := by
  unfold reciprocitySign
  exact_mod_cast quadraticRaySign_sq (residue a) (residue b) ha hb

include ha hb in
theorem reciprocitySign_cube_right  
     
      :
    reciprocitySign a (b ^ 3) = reciprocitySign a b := by
  rw [show b ^ 3 = b ^ 2 * b by ring, reciprocitySign_mul_right,
    pow_two, reciprocitySign_mul_right]
  grind [reciprocitySign_sq, reciprocitySign]

theorem quadraticRayValue_cube  r 
    (hr : EisensteinEPrimaryPhase.odd r) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul
      (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayValue r := by
  have he : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul
        (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayExponent r := by decide
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul _ _ (odd_mul _ _ hr hr) hr),
    he r hr, ← quadraticRayValue_eq_fourthRoot r hr]

include ha in
theorem G_cube    
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) :
    G (a ^ 3) = quadraticRayValue (residue a) := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  change fixedGValue (residue (a ^ 3)) = quadraticRayValue (residue a)
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_pow, hc, inv_one, one_mul]
  rw [show a ^ 3 = (a * a) * a by ring, residue_mul, residue_mul]
  exact quadraticRayValue_cube (residue a) ha

end

end SevenEighths.ProbePhase
end

end OAI
