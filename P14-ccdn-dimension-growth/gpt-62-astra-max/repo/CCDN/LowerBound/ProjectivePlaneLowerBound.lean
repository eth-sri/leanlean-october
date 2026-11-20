/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.LowerBound.GridCurveConstruction
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Height.ProjectiveIntegerHeight

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

private lemma grid_numeric (k : ℕ) (hk : 1 ≤ k) :
    (((k+1:ℕ):ℝ)^2 / 5) * ((k+1:ℕ):ℝ)^((2:ℝ) / (k+1:ℕ)) ≤ (k+1:ℕ)* (k:ℝ) := by
  have h (d : ℕ) (hd : 2 ≤ d) : (d:ℝ)^2 ≤ (5/2:ℝ)^d := by
    induction d,hd using Nat.le_induction with
    | base => norm_num
    | succ d hd ih =>
      have : (2:ℝ) ≤ d := by exact_mod_cast hd
      rw [pow_succ (5/2:ℝ)]; push_cast
      nlinarith [sq_nonneg ((d:ℝ)-2)]
  let d := k+1
  have hpow := Real.rpow_le_rpow (sq_nonneg (d:ℝ)) (h d (by dsimp [d]; omega)) (show 0 ≤ (d:ℝ)⁻¹ by positivity)
  rw [Real.pow_rpow_inv_natCast (by norm_num) (by dsimp [d]; omega), ← Real.rpow_natCast_mul (by positivity)] at hpow
  change (d:ℝ)^2 / 5 * (d:ℝ)^((2:ℝ) / d) ≤ d*k
  rw [div_eq_mul_inv (2:ℝ)]; push_cast at hpow
  have := mul_le_mul_of_nonneg_left hpow (sq_nonneg (d:ℝ))
  dsimp [d] at *; push_cast at *
  nlinarith [show (1:ℝ) ≤ k by exact_mod_cast hk,sq_nonneg ((k:ℝ)-1)]

theorem projective_plane_lower_bound (d : ℕ) (hd : 0 < d) :
    ∃ F : CoordinatePolynomial 3, ∃ B : ℕ, 1 ≤ B ∧
      F.IsHomogeneous d ∧ F.totalDegree = d ∧ AbsolutelyIrreducibleRat F ∧
        ((d:ℝ)^2 / 5) * (B:ℝ)^(2 / (d:ℝ)) ≤ (projectiveCount (projectiveZeroLocus F) B : ℝ) := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let F := gridEquation ℚ k
  have hom := gridEquation_hom ℚ k
  refine ⟨F, k+1, by omega, hom, hom.totalDegree (gridEquation_irred ℚ k).ne_zero, ?_, ?_⟩
  · change Irreducible (map _ (gridEquation ℚ k))
    rw [gridEquation_map]; apply gridEquation_irred
  let S := projectivePoints (projectiveZeroLocus F) (k+1)
  let pt (z : IntPoint 3) (hz : z ≠ 0) (hb : InBox z (k+1)) (he : eval (rationalPoint z) F = 0) : S :=
    ⟨Projectivization.mk ℚ _ (rationalPoint_ne_zero hz), mem_projectivePoints.mpr
      ⟨projective_integer_height_le z hz hb,(mem_projectiveZeroLocus_mk hom _ _).mpr he⟩⟩
  by_cases hk : k = 0
  · subst k
    let z : IntPoint 3 := ![0,1,0]
    have u := pt z (by intro h; have := congrFun h 1; simp [z] at this)
      (by intro i; fin_cases i <;> norm_num [z]) (by simp [F,gridEquation,gridRows,rationalPoint,z])
    have h := Fintype.card_pos_iff.mpr ⟨u⟩
    simp only [Fintype.card_coe,S,Nat.cast_zero,zero_add] at h
    change _ ≤ (projectiveCount _ _ : ℝ)
    norm_num
    have : (1:ℝ) ≤ projectiveCount (projectiveZeroLocus F) 1 := by exact_mod_cast h
    linarith
  let z (ij : Fin (k+1) × Fin k) : IntPoint 3 := ![ij.1.val,ij.2.val,1]
  let g (ij : Fin (k+1) × Fin k) : S := pt (z ij)
    (by intro h; have := congrFun h 2; simp [z] at this)
    (by intro i; fin_cases i <;> simp [z] <;> norm_cast <;> omega)
    (by
      simp only [F,gridEquation,gridRows,map_add,map_mul,map_prod,map_sub,eval_X,eval_C]
      rw [prod_eq_zero (mem_range.mpr ij.1.isLt) (by simp [rationalPoint,z]),
        prod_eq_zero (mem_range.mpr ij.2.isLt) (by simp [rationalPoint,z]),mul_zero,add_zero])
  have hinj : Function.Injective g := by
    intro a b h
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mp (congrArg Subtype.val h)
    have h1 := congrFun hc 2
    simp [rationalPoint,z] at h1
    subst c
    simp only [one_smul] at hc
    have he := rationalPoint_injective _ hc.symm
    exact Prod.ext (Fin.ext (by simpa [z] using congrFun he 0)) (Fin.ext (by simpa [z] using congrFun he 1))
  have hc := Fintype.card_le_of_injective g hinj
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,S] at hc
  apply (grid_numeric k (by omega)).trans
  simpa [projectiveCount] using (Nat.cast_le.mpr hc : ((_ : ℕ):ℝ) ≤ _)

end
end CCDN
