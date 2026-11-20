/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.AuxiliaryPolynomial.AffineScaledEstimate
public import CCDN.AuxiliaryPolynomial.SmoothBoxAuxiliary
import CCDN.Height.ScaledHypersurfaceHeight

/-! The affine determinant bound. The coefficient-sensitive alternative and the logarithmic
alternative both come from the same projective model. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Any upper bound `A` for the affine height charge yields a box auxiliary, with a constant
independent of the equation and of the box radius. -/
theorem affine_hypersurface_auxiliary {n : ℕ} (f : IntegerPolynomial (n + 2))
    (hprim : PrimitiveIntegerPolynomial f) (hir : AbsolutelyIrreducible f) (hd : 0 < f.totalDegree)
    {B A : ℝ} (hB : 1 ≤ B) (hA : affineAuxiliaryCharge n f.totalDegree B
      (integerCoefficientHeight (homogeneousComponent f.totalDegree f)) (hypersurfaceBadPrimeFactor f) ≤ A) :
    ∃ g, IsBoxAuxiliary f g B ∧ (g.totalDegree : ℝ) ≤ affineHypersurfaceAuxiliaryConstant n *
      (A + 1) * auxDegreeScale n f.totalDegree * affineBoxPower n f.totalDegree B := by
  classical
  let d := f.totalDegree
  have hf := ne_zero_of_irreducible_map hir
  obtain ⟨S⟩ := exists_boxScaling f hprim hd hB
  let X := (integerBox (n+2) B).filter (fun x => eval x f = 0)
  obtain ⟨g,hnd,hz,hg⟩ := S.auxiliary hprim hir hd X
    (fun _ h => mem_integerBox.mp (Finset.mem_filter.mp h).1) (fun _ h => (Finset.mem_filter.mp h).2)
    ∅ 0 ⟨by simp,by simp,by simp,by simp⟩
  have hh : (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d S.p (hypersurfaceBadPrimeFactor f) (integerCoefficientHeight S.equation) := by
    simpa only [hypersurfaceBadPrimeFactor,dite_eq_left hir,Finset.union_empty,Finset.sum_empty,Real.exp_zero,div_one,mul_zero,add_zero] using hg
  let H : ℝ := integerCoefficientHeight S.equation
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast integerCoefficientHeight_pos _ (S.ne_zero hf)
  have hL := leading_height_one_le f hf
  have hc := badHeightCost_nonneg (n+2)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hb : hypersurfaceBadPrimeFactor f ≤ scaleBadCost n * (1 + Real.log H / (d:ℝ)^2) := by
    apply (hypersurfaceBadPrimeFactor_le_height f _ (by exact_mod_cast integerCoefficientHeight_pos f hf) (coefficient_abs_le_integerCoefficientHeight f)).trans
    change badHeightCost (n+2)*(1+_/_) ≤ _
    rw [scaleBadCost,mul_comm _ (badHeightCost (n+2)),mul_assoc (badHeightCost (n+2))]
    apply mul_le_mul_of_nonneg_left _ hc
    have hh := S.height_control hd hf
    push_cast at hh
    have hl := Real.log_nonneg hH
    field_simp
    nlinarith only [hh,hl,mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hl]
  refine ⟨g,⟨fun h => hnd (h ▸ dvd_zero _),hnd,fun x hx hxz => hz x (Finset.mem_filter.mpr ⟨mem_integerBox.mpr hx,hxz⟩)⟩,
    (hh.trans (scaled_auxiliary_estimate hd hB (by exact_mod_cast S.prime.one_le) S.small hL
      (hypersurfaceBadPrimeFactor_nonneg _) S.leading_height hb)).trans ?_⟩
  have := affineHypersurfaceAuxiliaryConstant_pos n
  calc
    _ ≤ affineHypersurfaceAuxiliaryConstant n * auxDegreeScale n f.totalDegree * affineBoxPower n f.totalDegree B * (A + 1) := by gcongr
    _ = _ := by ring

end
end CCDN
