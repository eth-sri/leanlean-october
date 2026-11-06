/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.HeightDeterminant
import CCDN.Height.CountingHypotheses
import CCDN.Height.PrimitiveIntegerPolynomial
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary
import CCDN.Plane.ScaledModelCoordinates
import CCDN.Plane.ScaledModelPosition

/-! A prime-scaled plane point bound with the arbitrary coefficient
height eliminated. The sharp finite-field count and a suitable scaling prime
remain explicit hypotheses. -/

namespace CCDN
noncomputable section
open MvPolynomial Real

/-- The auxiliary degree bound for a plane equation of degree `d` after translation into a box
of radius `R` and scaling by `p`, with residue constant `C`. The constants `23` and `exp 14` are
explained in `projectivePlaneAbsoluteConstant`. -/
def scaledPlaneAuxiliaryDegreeBound (d : ℕ) (C R p : ℝ) : ℝ :=
  d + Real.log R + 2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 *
    (d : ℝ) ^ 3 * (1 + Real.log p / d) * R ^ (2 / (d : ℝ)) / p ^ (1 / (d : ℝ)) + 2

/-- Count original integer plane points using the translated scaled
model. The determinant estimate is applied to polynomial columns on the
original curve, so its sharp residue-count hypothesis concerns that curve. -/
theorem scaled_plane_finite_count
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (hd : 0 < f.totalDegree) {p : ℕ} (hp : 1 ≤ p)
    (z : Fin t → Fin 2 → ℤ)
    {B C : ℝ} (hzB : IsBoxZeroFamily f B z) (hpB : (p : ℝ) ≤ B) (hC : 0 ≤ C)
    (hcard : ∀ M a g, IsPointAuxiliary
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree (p : ℤ) f))
        g M (fun i j => eval (z i) (scaledModelCoordinates (p : ℤ) a j)) →
      t ≤ f.totalDegree * M)
    (hcount : PlaneResidueCountBound C f.totalDegree f) :
    (t : ℝ) ≤ max
      ((f.totalDegree : ℝ) * scaledPlaneAuxiliaryDegreeBound f.totalDegree C
        (((f.totalDegree : ℝ) + 1) * B) p)
      ((34 + 8 * Real.exp (heightDeterminantError C + 20)) * (f.totalDegree : ℝ) ^ 4) ∧
    ∀ m, f.coeff m ≠ 0 →
      4 * (f.totalDegree : ℝ) * Real.log (((f.totalDegree : ℝ) + 1) * B) ≤
        Real.log |(f.coeff m : ℝ)| →
      (t : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 20)) * (f.totalDegree : ℝ) ^ 4 := by
  obtain ⟨hB, hz, hbox⟩ := hzB
  let d := f.totalDegree
  let R := (d + 1) * B
  have hdR : (0 : ℝ) < d := mod_cast hd
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by linarith) hB
  have hp1 : (1 : ℤ) ≤ p := mod_cast hp
  have hpR : (1 : ℝ) ≤ p := mod_cast hp
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by grind)
  obtain ⟨a, H, ha, hH, hpH, hc, hlo, hhi⟩ := exists_scaled_model_position f hf0 hd hp1
  let model := homogeneousTranslation ℤ a (scaledHomogenize d p f)
  have hmhom : model.IsHomogeneous d :=
    homogeneousTranslation_homogeneous a (scaledHomogenize_homogeneous _ _ le_rfl)
  have hm0 : model ≠ 0 := by
    have he := (homogeneousTranslation ℤ a).injective.ne (scaledHomogenize_ne_zero d
      (show (p : ℤ) ≠ 0 by omega) hf0)
    grind
  let τ := scaledModelCoordinates (p : ℤ) a
  have hmodel : ∀ i, eval (fun j => eval (z i) (τ j)) model = 0 := by
    intro i
    rw [scaledModelCoordinates_model_eval, hz i, mul_zero]
  have himagebox : ∀ i j, |(eval (z i) (τ j) : ℝ)| ≤ R := by
    intro i j
    exact scaledModelCoordinates_box hB (by positivity) (mod_cast hpB) a (z i) ha
      (hbox i) j
  have hbig (hlarge : 4 * d * Real.log R ≤ Real.log H) :
      (t : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 20)) * (d : ℝ) ^ 4 := by
    obtain ⟨M, hM, g, hg⟩ := auxiliary_large_height_degree
      MonomialOrder.lex model hm0 hd hH hR _ (fun M hdM hrel => polynomial_map_no_auxiliary_height_comparison
        MonomialOrder.lex model hmhom hm0 hd hdM ⟨rfl, hir, hH, hc⟩ τ z hz ⟨hR, hmodel, himagebox⟩ hC
        hrel hcount) 14 (by norm_num) hlarge hhi
    have htR : (t : ℝ) ≤ d * (M : ℝ) := mod_cast hcard M a g hg
    apply (htR.trans (mul_le_mul_of_nonneg_left hM hdR.le)).trans
    grind
  refine ⟨?_, fun m hm hheight => hbig (hheight.trans
    (Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hm)) (hc m)))⟩
  by_cases hsmall : Real.log H ≤ 4 * d * Real.log R
  · obtain ⟨M, hM, g, hg⟩ := auxiliary_small_height_degree
      MonomialOrder.lex model hm0 hd hH hR _ (fun M hdM hrel => polynomial_map_no_auxiliary_height_comparison
        MonomialOrder.lex model hmhom hm0 hd hdM ⟨rfl, hir, hH, hc⟩ τ z hz ⟨hR, hmodel, himagebox⟩ hC
        hrel hcount) (hlo.trans hsmall)
    have htR : (t : ℝ) ≤ d * (M : ℝ) := mod_cast hcard M a g hg
    have hL : 0 < |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| := by simp_all
    have hratio := scaled_positioned_height_ratio_le hd hpR (mod_cast hpH) hL hhi
    have hterm : 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * R ^ (2 / (d : ℝ)) /
          |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) ≤
        2 * Real.exp (heightDeterminantError C + 23) * Real.exp 14 * (d : ℝ) ^ 3 *
          (1 + Real.log p / d) * R ^ (2 / (d : ℝ)) / (p : ℝ) ^ (1 / (d : ℝ)) := by
      let A := 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 * R ^ (2 / (d : ℝ))
      have hA : 0 ≤ A := by positivity
      convert mul_le_mul_of_nonneg_left hratio hA using 1 <;> dsimp [A] <;> ring
    exact (htR.trans (mul_le_mul_of_nonneg_left (by
      unfold scaledPlaneAuxiliaryDegreeBound
      linarith) hdR.le)).trans (le_max_left _ _)
  · exact (hbig (lt_of_not_ge hsmall).le).trans (le_max_right _ _)
