/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.ProjectivePlaneAbsoluteCount
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.SchwartzZippel
import CCDN.Plane.ProjectivePlaneNonabsoluteCount

/-! The elementary linear case completes the uniform plane-equation
bound in every positive degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Uniform CCDN Theorem 2 for rational projective plane equations,
in every positive degree and for every real B >= 1. -/
theorem projective_plane_equation_bound {d : ℕ}
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible f) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  classical
  by_cases hd1 : d = 1
  · subst d
    obtain ⟨g, a, _, ha, he⟩ := exists_primitive_integer_model f hir.ne_zero
    have hgh := rational_scalar_model_homogeneous he hf
    have hg0 : g ≠ 0 := fun h =>
      mul_ne_zero (C_eq_zero.not.mpr ha) hir.ne_zero (by simpa [h] using he.symm)
    have hzero : projectiveZeroLocus (map (Int.castRingHom ℚ) g) = projectiveZeroLocus f := by
      ext x; exact rational_scalar_model_zero_iff ha he x.rep
    have hlin : (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤ 9 * B ^ 2 := by
      rw [← hzero]
      apply projective_zero_count_le_of_family_bound g hgh
      intro t z hz0 hinj _ hz hbox
      let T := (integerBox 3 B).filter (fun x => eval x g = 0)
      let ψ : Fin t → T := fun i => ⟨z i, Finset.mem_filter.mpr ⟨mem_integerBox.mpr (hbox i), hz i⟩⟩
      have hψ : Function.Injective ψ := fun i j heq => by
        have hzi : z i = z j := congrArg Subtype.val heq
        exact hinj ((Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr ⟨1, by simp [hzi]⟩)
      have hc := Fintype.card_le_of_injective ψ hψ
      have hcR : (t : ℝ) ≤ T.card :=
        mod_cast (show t ≤ T.card by simpa only [Fintype.card_fin, Fintype.card_coe] using hc)
      let S := Finset.Icc (-⌊B⌋) ⌊B⌋
      have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr (by linarith)
      have hSpos : (0 : ℝ) < S.card :=
        mod_cast Finset.card_pos.mpr ⟨0, Finset.mem_Icc.mpr ⟨by omega, hfloor⟩⟩
      have hsz : T.card * S.card ≤ g.totalDegree * S.card ^ 3 := by
        simpa only [T, integerBox, S, Fintype.card_fin] using schwartz_zippel_totalDegree_card hg0 S
      have hcard : (T.card : ℝ) ≤ g.totalDegree * (S.card : ℝ) ^ 2 := by
        refine le_of_mul_le_mul_right ?_ hSpos
        rw [mul_assoc, ← pow_succ]; exact_mod_cast hsz
      have hScard : (S.card : ℝ) ≤ 3 * B := by
        dsimp only [S]
        rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        push_cast; linarith [Int.floor_le B]
      have hb := hcard.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hSpos.le hScard 2) (by positivity))
      rw [hgh.totalDegree hg0] at hb
      convert hcR.trans hb using 1
      norm_num; ring
    have hC : 9 ≤ projectivePlaneAbsoluteConstant := by
      unfold projectivePlaneAbsoluteConstant
      have hpos := Real.exp_pos
        (heightDeterminantError projectivePlaneDeterminantConstant + 20)
      have hpos' : 0 ≤
          2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
            Real.exp 14 * Real.exp 2 := by positivity
      linarith
    norm_num only [Nat.cast_one, one_pow, mul_one, div_one, Real.rpow_two]
    exact hlin.trans (mul_le_mul_of_nonneg_right hC (sq_nonneg B))
  · exact projective_plane_rational_count f hf (by omega) hir hB

end
end CCDN
