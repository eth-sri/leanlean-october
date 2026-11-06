module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.Reciprocal
public import OAI.NumberTheory.DirichletL.Hecke.MellinIdentity

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeOrigin
open HeckeFamily HeckeTheta

def poleRemoved (χ : Character) (s : ℂ)  :=
  (Real.pi : ℂ)^s * (Complex.Gamma (s+1))⁻¹ *
    HeckeMellinIdentity.regularized (pair (coefficients χ)) s / 6

theorem poleRemoved_entire  χ  : Differentiable ℂ (poleRemoved χ) := Differentiable.div_const (Differentiable.mul (Differentiable.mul (Differentiable.const_cpow differentiable_id (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) (Differentiable.comp Complex.differentiable_one_div_Gamma (Differentiable.add_const 1 differentiable_id))) (OAI.SevenEighths.HeckeMellinIdentity.regularized_entire (OAI.SevenEighths.HeckeTheta.pair (OAI.SevenEighths.HeckeFamily.coefficients χ)))) 6

theorem poleRemoved_eq  χ   {s}  (h0 : s ≠ 0) (h1 : s ≠ 1) :
    poleRemoved χ s = (s-1) * LFunction χ s := by
  unfold poleRemoved LFunction continuedLattice latticeL completed
  rw [HeckeMellinIdentity.regularized_eq _ (pair_k _) h0 h1,
    Complex.Gamma_add_one s h0, mul_inv_rev]
  field_simp

theorem poleRemoved_one  χ  :
    poleRemoved χ 1 = HeckeReciprocal.regularizedL χ 1 := by
  rw [HeckeReciprocal.regularizedL_at_one]
  simp [poleRemoved, HeckeMellinIdentity.regularized,
    Complex.Gamma_add_one 1 one_ne_zero,
    show (pair (coefficients χ)).ε = 1 from rfl]

theorem poleRemoved_one_ne_zero  χ  (hχ : χ.residue = 1) :
    poleRemoved χ 1 ≠ 0 := by
  rw [poleRemoved_one]
  exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ

def continued (χ : Character) (s : ℂ)  :=
  if χ.residue = 1 then poleRemoved χ s / (s-1) else LFunction χ s

theorem continued_eq  χ   {s}  (h0 : s ≠ 0) (h1 : s ≠ 1) :
    continued χ s = LFunction χ s := by
  grind [continued, poleRemoved_eq]

theorem continued_differentiableAt  χ   {s} 
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : DifferentiableAt ℂ (continued χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : continued χ = fun z => poleRemoved χ z / (z-1) := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact (poleRemoved_entire χ s).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr (hpole.resolve_right (not_not.mpr hχ)))
  · have heq : continued χ = LFunction χ := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact ((HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6) s

end SevenEighths.HeckeOrigin

end

end OAI
