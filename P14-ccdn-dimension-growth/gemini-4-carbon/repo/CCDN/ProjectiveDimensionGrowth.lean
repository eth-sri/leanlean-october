/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
import CCDN.Algebra.GridPointInterpolation
import CCDN.Algebra.IntegerLinearForms
import CCDN.Algebra.ProjectiveFiniteFibers
import Mathlib.LinearAlgebra.Matrix.ToLin
import CCDN.Hilbert.ProperHilbertDimension
import CCDN.Hypersurface.ProjectiveHypersurfaceDimensionGrowth
import CCDN.Plane.ProjectivePlaneLinearCount
import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.BoundedIntegerNormalization
import CCDN.Projection.ProjectiveLinearCountTransfer

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem empty_of_hilbert_dim_zero {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hdim : (filteredHilbertPolynomial I).natDegree = 0) :
    projectiveIdealZeroLocus I = ∅ := by
  classical
  obtain ⟨N₀, hN₀⟩ := filteredHilbertPolynomial_spec I
  have hP := Polynomial.eq_C_of_natDegree_eq_zero hdim
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  refine projective_linear_image_ne_zero_of_finite_zero_fiber I
    (0 : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin 0 → ℚ))
    (Module.finrank ℚ (filteredCoordinateSpace I N₀)) (fun s hs _ => ?_) x hx rfl
  let S : Finset ℚ := s.biUnion fun y => Finset.univ.image y
  let N := max N₀ ((n + 1) * (S.card - 1))
  have hdimN : Module.finrank ℚ (filteredCoordinateSpace I N) =
      Module.finrank ℚ (filteredCoordinateSpace I N₀) := by
    have h1 := hN₀ N (le_max_left _ _); have h2 := hN₀ N₀ le_rfl
    rw [hP, Polynomial.eval_C] at h1 h2; exact_mod_cast h1.symm.trans h2
  have hh := grid_points_filtered_lower I S (fun y : s => y.val) Subtype.val_injective
    (fun y j => Finset.mem_biUnion.mpr ⟨y.val, y.2, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    (fun y f hf => hs y.val y.2 f hf) (show Fintype.card (Fin (n + 1)) * (S.card - 1) ≤ N by simp [N])
  exact (by simpa only [Fintype.card_coe] using hh : s.card ≤ _).trans_eq hdimN

private theorem zero_dim_count_le {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = 1)
    (hdeg : (filteredHilbertPolynomial I).leadingCoeff = d) (B : ℝ) :
    projectiveCount (projectiveIdealZeroLocus I) B ≤ d ^ (n + 1) := by
  classical
  have hgen (N : ℕ) (hN : 0 + 1 ≤ N) (J : Ideal (MvPolynomial (Fin N) ℚ)) [J.IsPrime]
      (hj : HasProjectiveDimensionDegree J 0 d) :
      ∃ a : Fin 1 → Fin N → ℤ,
        (projectionCoordinateMap J (fun i => integerLinearForm (a i))).IsIntegral ∧
        Function.Injective (projectionCoordinateMap J (fun i => integerLinearForm (a i))) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    obtain ⟨a, _, hint, hi⟩ := exists_bounded_integer_normalization 0 k J d hj
    exact ⟨a, hint, hi⟩
  have hdd : HasProjectiveDimensionDegree I 0 d := ⟨hdim, by simpa using hdeg⟩
  obtain ⟨a, hint, hi⟩ := hgen (n + 1) (by omega) I hdd
  let L := (Matrix.of fun i j => (a i j : ℚ)).mulVecLin
  have hfin (z : Fin 1 → ℚ) (s : Finset (Fin (n + 1) → ℚ))
      (hs : ∀ x ∈ s, x ∈ idealZeroLocus I) (hz : ∀ x ∈ s, L x = z) : s.card ≤ d ^ (n + 1) :=
    (linear_normalization_fiber_card_le I (fun i => integerLinearForm (a i))
      (fun _ => linearForm_totalDegree_le _) hi hint d hdd z s hs fun x hx i => by
        simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
          eval_linearForm] using congrFun (hz x hx) i).trans (Nat.le_self_pow (Nat.succ_ne_zero n) d)
  let s := projectivePoints (projectiveIdealZeroLocus I) B
  have hs (x) (hx : x ∈ s) : x ∈ projectiveIdealZeroLocus I := (mem_projectivePoints.mp hx).2
  have hnon (x) (hx : x ∈ s) : L x.rep ≠ 0 :=
    projective_linear_image_ne_zero_of_finite_zero_fiber I L (d ^ (n + 1)) (hfin 0) x (hs x hx)
  let y : ProjectivePoint 0 := Projectivization.mk ℚ (fun _ : Fin 1 => 1) fun h =>
    one_ne_zero (congrFun h 0)
  refine projective_linear_fiber_card_le I L s hs hnon y (fun x hx => ?_) (d ^ (n + 1)) (hfin y.rep)
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨L x.rep 0, funext fun i => by rw [show i = 0 from Fin.ext (by omega)]; simp⟩

private theorem birational_transfer {r n d : ℕ} (hrn : r + 1 ≤ n + 1)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (hI : IsHomogeneousIdeal I)
    (hd : 5 ≤ d) (hdd : HasProjectiveDimensionDegree I r d) {B : ℝ} (hB : 1 ≤ B) :
    ∃ f : MvPolynomial (Fin (r + 2)) ℚ, Irreducible f ∧ f.IsHomogeneous d ∧ f.totalDegree = d ∧
      1 ≤ ((n + 1 : ℝ) * birationalProjectionHeightConstant (n + 1)) * (d : ℝ) ^ (2 * (n + 1)) * B ∧
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        (d : ℝ) ^ (n + 1) * projectiveCount (projectiveZeroLocus f)
          (((n + 1 : ℝ) * birationalProjectionHeightConstant (n + 1)) *
            (d : ℝ) ^ (2 * (n + 1)) * B) := by
  obtain ⟨b, f, hb, hN, hP, hfhom, hfdeg⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le r (n + 1) hrn I hI d hdd
  let H : ℝ := birationalProjectionHeightConstant (n + 1) * (d : ℝ) ^ (2 * (n + 1))
  have hd1 : (1 : ℝ) ≤ d := mod_cast (show 1 ≤ d by omega)
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le
    (mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos (n + 1))) (one_le_pow₀ hd1)
  have hbH (i j) : |(b i j : ℝ)| ≤ H :=
    (show |(b i j : ℝ)| ≤ integerBirationalProjectionHeight (n + 1) d from mod_cast hb i j).trans
      (by dsimp only [H]; exact_mod_cast integerBirationalProjectionHeight_le (n + 1) d (by omega))
  have hfib (z : Fin (r + 2) → ℚ) (s : Finset (Fin (n + 1) → ℚ))
      (hz0 : ∀ x ∈ s, x ∈ idealZeroLocus I)
      (hpr : ∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) : s.card ≤ d ^ (n + 1) :=
    (linear_normalization_fiber_card_le I (fun i : Fin (r + 1) => integerLinearForm (b i.succ))
      (fun _ => linearForm_totalDegree_le _) hN.injective hN.integral d hdd
      (fun i => z i.succ) s hz0 fun x hx i => hpr x hx i.succ).trans
      (Nat.le_self_pow (Nat.succ_ne_zero n) d)
  have htr := projective_integer_linear_count_transfer I b f (hfdeg ▸ hfhom) hP.aeval_mem
    (d ^ (n + 1)) hfib H B (by linarith) hbH
  have hrad : ((n + 1 : ℝ) * birationalProjectionHeightConstant (n + 1)) * (d : ℝ) ^ (2 * (n + 1)) * B =
      (n + 1 : ℝ) * H * B := by dsimp [H]; ring
  refine ⟨f, hP.irreducible, hfhom, hfdeg, ?_, ?_⟩
  · rw [hrad]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hH) hB
  · rw [hrad]; exact_mod_cast htr

/-- CCDN Theorem 1 with the degree exponent `2n² + 5n - 5` in every ambient projective
dimension `n`. -/
theorem projective_dimension_growth (n : ℕ) :
    ProjectiveGrowth n (2 * n ^ 2 + 5 * n - 5) := by
  classical
  have hempty (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
      (h : (filteredHilbertPolynomial I).natDegree = 0) (B : ℝ) :
      projectiveCount (projectiveIdealZeroLocus I) B = 0 := by
    rw [empty_of_hilbert_dim_zero I h]; simp [projectiveCount, projectivePoints]
  have hlt (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) (hI : I.IsPrime) (d : ℕ) (hd : 5 ≤ d)
      (hdeg : (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
      (filteredHilbertPolynomial I).natDegree < n + 1 := by
    simpa only [Fintype.card_fin] using
      hilbert_dimension_lt_ambient_of_degree_gt_one I hI.ne_top d (by omega) hdeg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_pos, fun I hprime _ d hd hdeg B _ => ?_⟩
    rw [hempty I (by have := hlt I hprime d hd hdeg; omega), Nat.cast_zero]; positivity
  let T : ℝ := (n + 1 : ℝ) * birationalProjectionHeightConstant (n + 1)
  have hT0 : 0 < T := mul_pos (by positivity) (mod_cast birationalProjectionHeightConstant_pos (n + 1))
  choose Ch hCh hh_ideal using fun m => (projective_hypersurface_dimension_growth m).ideal
  choose Cp hCp hp_poly using projective_hypersurface_dimension_growth
  let S_sup : ℝ := ∑ k ∈ Finset.range (n + 1), Cp k * T ^ (k + 1)
  have hS_nonneg : 0 ≤ S_sup := Finset.sum_nonneg fun k _ =>
    mul_nonneg (hCp k).le (pow_nonneg hT0.le _)
  let K : ℝ := S_sup + projectivePlaneAbsoluteConstant * T + Ch (n - 2) + 1
  have hKpos : 0 < K := by
    dsimp [K]; linarith [projectivePlaneAbsoluteConstant_pos, mul_pos projectivePlaneAbsoluteConstant_pos hT0, hCh (n - 2)]
  refine ⟨K, hKpos, fun I hprime hI d hd hdeg B hB => ?_⟩
  have : I.IsPrime := hprime
  set E := 2 * n ^ 2 + 5 * n - 5
  suffices h : ∃ C₀ ≤ K, ∃ e ≤ E,
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C₀ * (d : ℝ) ^ e * B ^ ((filteredHilbertPolynomial I).natDegree - 1) by
    obtain ⟨C₀, hCK, e, heE, h⟩ := h
    have hd1 : (1 : ℝ) ≤ d := mod_cast (show 1 ≤ d by omega)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (mul_le_mul_of_nonneg_right hCK (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd1 heE) hKpos.le)
  have hdim := hlt I hprime d hd hdeg
  obtain h0 | h1 | h2 | h3 : (filteredHilbertPolynomial I).natDegree = 0 ∨
      (filteredHilbertPolynomial I).natDegree = 1 ∨
      (filteredHilbertPolynomial I).natDegree = 2 ∨
      3 ≤ (filteredHilbertPolynomial I).natDegree := by omega
  · refine ⟨0, hKpos.le, 0, Nat.zero_le _, ?_⟩
    rw [hempty I h0, Nat.cast_zero, zero_mul, zero_mul]
  · refine ⟨1, by dsimp [K]; linarith [mul_pos projectivePlaneAbsoluteConstant_pos hT0, hCh (n - 2)],
      n + 1, by have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn; dsimp [E]; omega, ?_⟩
    rw [h1, Nat.sub_self, pow_zero, mul_one, one_mul]
    exact_mod_cast zero_dim_count_le I d h1
      (by simpa only [h1, Nat.factorial_one, Nat.cast_one, div_one] using hdeg) B
  · have hn2 : 2 ≤ n := by omega
    have hsq : 2 * n ≤ n ^ 2 := by nlinarith
    refine ⟨projectivePlaneAbsoluteConstant * T, by dsimp [K]; linarith [hCh (n - 2)],
      3 * (n + 1) + 4, by dsimp [E]; omega, ?_⟩
    rw [h2, show 2 - 1 = 1 from rfl, pow_one]
    obtain ⟨f, hfir, hfhom, _, hTB, htr⟩ := birational_transfer (r := 1) (by omega) I hI hd
      ⟨h2, by simpa only [h2] using hdeg⟩ hB
    have hpl := (projective_plane_equation_bound f hfhom (by omega) hfir hTB).trans
      (mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hTB
        ((div_le_one (by positivity)).mpr (mod_cast (show 2 ≤ d by omega)))).trans_eq (Real.rpow_one _))
        (mul_nonneg projectivePlaneAbsoluteConstant_pos.le (by positivity)))
    refine htr.trans ((mul_le_mul_of_nonneg_left hpl (by positivity)).trans_eq ?_)
    rw [show 3 * (n + 1) + 4 = (n + 1) + 4 + 2 * (n + 1) by omega]
    simp only [T, pow_add]; ring
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' h3
    rcases eq_or_ne (m + 3) n with rfl | hhyp
    · have hsq : 3 * (m + 3) ≤ (m + 3) ^ 2 := by nlinarith
      refine ⟨Ch (m + 1), ?_, 18 + 3 * (m + 1), by dsimp [E]; omega, ?_⟩
      · show Ch (m + 1) ≤ S_sup + projectivePlaneAbsoluteConstant * T + Ch (m + 3 - 2) + 1
        rw [show m + 3 - 2 = m + 1 by omega]
        linarith [mul_pos projectivePlaneAbsoluteConstant_pos hT0]
      · rw [hm, show m + 3 - 1 = m + 1 + 1 by omega]
        exact hh_ideal (m + 1) I hprime hI d hd ⟨hm, by simpa only [hm] using hdeg⟩ B hB
    · have hn4 : 4 ≤ n := by omega
      have hmn : m + 4 ≤ n := by omega
      have hm_mem : m + 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hCm : Cp (m + 1) * T ^ ((m + 1) + 1) ≤ S_sup :=
        Finset.single_le_sum (f := fun k => Cp k * T ^ (k + 1))
          (fun k _ => mul_nonneg (hCp k).le (pow_nonneg hT0.le _)) hm_mem
      refine ⟨Cp (m + 1) * T ^ ((m + 1) + 1), by
        dsimp [K]; linarith [mul_pos projectivePlaneAbsoluteConstant_pos hT0, hCh (n - 2)],
        (n + 1) + (18 + 3 * (m + 1)) + 2 * (n + 1) * (m + 2), ?_, ?_⟩
      · have : (n + 1) + (18 + 3 * (m + 1)) + 2 * (n + 1) * (m + 2) ≤ 2 * n ^ 2 + 2 * n + 6 := by
          nlinarith
        have : 11 ≤ 3 * n := by omega
        dsimp [E]; omega
      · rw [hm, show m + 3 - 1 = m + 2 by omega]
        obtain ⟨f, hfir, hfhom, hfdeg, hTB, htr⟩ := birational_transfer (r := m + 2) (by omega)
          I hI hd ⟨hm, by simpa only [hm] using hdeg⟩ hB
        have hpt := hp_poly (m + 1) f (hfdeg ▸ hfhom) hfir (hfdeg ▸ hd) _ hTB
        rw [hfdeg] at hpt
        refine htr.trans ((mul_le_mul_of_nonneg_left hpt (by positivity)).trans_eq ?_)
        simp only [T, pow_add, pow_mul, mul_pow, show (m + 1) + 1 = m + 2 from rfl]
        ring

end
end CCDN
