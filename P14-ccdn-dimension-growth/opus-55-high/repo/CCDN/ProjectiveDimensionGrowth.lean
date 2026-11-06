/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Projection.ProjectiveProjectionGrowth
import CCDN.Statements
import CCDN.Curve.ProjectiveHilbertCurveGrowth
import CCDN.Hilbert.EmptyProjectiveHilbertDimension
import CCDN.Hilbert.ProperHilbertDimension
import CCDN.Hypersurface.ProjectiveHypersurfaceDimensionGrowth
import CCDN.Hypersurface.ProjectiveVarietyDimensionGrowth
import CCDN.Projection.ZeroDimensionalProjectiveCount

/-! CCDN Theorem 1 in the homogeneous-coordinate-ideal formulation: uniform projective
dimension growth for every rational prime projective variety of degree at least five.
The Hilbert polynomial determines the degree and dimension. Zero-dimensional and empty
loci are included.

The bound is assembled once, in `projectiveGrowth_of_le`, for any degree exponent which
dominates the exponents of the zero-dimensional count, the curve bound, the hypersurface
bound and the projection bound. The degree exponent `2n² + 5n - 5` follows, and from it the
exponent `2n³`. -/

namespace CCDN
section
open MvPolynomial

/-- Theorem 1 holds with any degree exponent `E` which dominates, in `ℙⁿ`, the exponent
`n + 1` of the zero-dimensional count, the exponent `3(n+1) + 4` of the curve bound, the
exponent `18 + 3(n-2)` of the hypersurface bound, and the exponent of the projection bound
for every dimension `m + 1 ≥ 2` and codimension `k ≥ 2`. -/
theorem projectiveGrowth_of_le {n E : ℕ} (hpoint : 1 ≤ n → n + 1 ≤ E)
    (hcurve : 2 ≤ n → 3 * (n + 1) + 4 ≤ E)
    (hhyper : 3 ≤ n → 18 + 3 * (n - 2) ≤ E)
    (hproj : ∀ m k, m + k + 1 = n → 1 ≤ m → 2 ≤ k →
      projectionDegreeExponent m k ≤ E) :
    ProjectiveGrowth n E := by
  have hlt (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) (hI : I.IsPrime) (d : ℕ) (hd : 5 ≤ d)
      (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
        (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
      (filteredHilbertPolynomial I).natDegree < n + 1 := by
    simpa using
      hilbert_dimension_lt_ambient_of_degree_gt_one I hI.ne_top d (by omega) hdegree
  have hempty (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
      (h : (filteredHilbertPolynomial I).natDegree = 0) (B : ℝ) :
      projectiveCount (projectiveIdealZeroLocus I) B = 0 := by
    rw [(show projectiveIdealZeroLocus I = ∅ by
        obtain ⟨M, hM⟩ := finite_point_bound_of_hilbert_dimension_zero I h
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hh := projective_linear_image_ne_zero_of_finite_zero_fiber I
          (0 : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin 0 → ℚ)) M
          (fun s hs _ => hM s hs) x hx
        exact hh rfl)]
    simp [projectiveCount, projectivePoints]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_pos, fun I hprime _ d hd hdegree B _ => ?_⟩
    rw [hempty I (by grind), Nat.cast_zero]
    positivity
  choose Cp _ hp using projective_variety_dimension_growth
  obtain ⟨T, hT⟩ := (((Set.finite_Iic n).prod (Set.finite_Iic n)).image
    fun p => Cp p.1 p.2).bddAbove
  obtain ⟨Cc, hCc, hc⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d → HasProjectiveDimensionDegree I 1 d →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * d ^ (3 * (n + 1) + 4) * B := by
    let T : ℝ := (n + 1) * birationalProjectionHeightConstant (n + 1)
    have hT : 0 < T :=
      mul_pos (by positivity)
        (mod_cast birationalProjectionHeightConstant_pos (n + 1))
    refine ⟨projectivePlaneAbsoluteConstant * T,
      mul_pos projectivePlaneAbsoluteConstant_pos hT, ?_⟩
    intro I hprime hI d hd hdimdeg B hB
    have : I.IsPrime := hprime
    obtain ⟨b, f, hb, hN, hP, hfhom, hfdeg⟩ :=
      exists_bounded_birational_hypersurface_projection_of_le 1 (n + 1)
        (by omega) I hI d hdimdeg
    have hf := hP.irreducible
    have hrel := (hP.aeval_mem_iff _).mpr dvd_rfl
    have hfiber (z : Fin 3 → ℚ) (s : Finset (Fin (n + 1) → ℚ))
        (hzero : ∀ x ∈ s, x ∈ idealZeroLocus I)
        (hproj : ∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) :
        s.card ≤ d ^ (n + 1) := by
      exact (linear_normalization_fiber_card_le I
        (fun i => integerLinearForm (b i.succ))
        (fun i => linearForm_totalDegree_le _) hN.injective hN.integral d hdimdeg
        (fun i => z i.succ) s hzero (fun x hx i => hproj x hx i.succ)).trans
        (Nat.le_self_pow (Nat.succ_ne_zero n) d)
    let H : ℝ := birationalProjectionHeightConstant (n + 1) * (d : ℝ) ^ (2 * (n + 1))
    have hd1 : (1 : ℝ) ≤ d := mod_cast (show 1 ≤ d by omega)
    have hH : 1 ≤ H := by
      exact one_le_mul_of_one_le_of_one_le (by
        exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos (n + 1))) (one_le_pow₀ hd1)
    have hbH (i j) : |(b i j : ℝ)| ≤ H := by
      have hh : |(b i j : ℝ)| ≤ integerBirationalProjectionHeight (n + 1) d := by
        exact_mod_cast hb i j
      apply hh.trans
      dsimp [H]
      exact_mod_cast integerBirationalProjectionHeight_le (n + 1) d (by omega)
    have hbound := projective_integer_linear_count_transfer
      I b f (by grind) hrel (d ^ (n + 1)) hfiber H B (by linarith) hbH
    have hheight : 1 ≤ (n + 1 : ℝ) * H * B :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by grind) hH) hB
    have hC := projectivePlaneAbsoluteConstant_pos
    have htarget := projective_plane_equation_bound f hfhom (by omega) hf hheight
    have hpow : ((n + 1 : ℝ) * H * B) ^ (2 / (d : ℝ)) ≤ (n + 1) * H * B := by
      calc
        _ ≤ ((n + 1 : ℝ) * H * B) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hheight
            ((div_le_one (by positivity)).mpr (mod_cast (show 2 ≤ d by omega)))
        _ = _ := Real.rpow_one _
    have hh : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        (d : ℝ) ^ (n + 1) *
          (projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * ((n + 1) * H * B)) := by
      apply (show (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        (d : ℝ) ^ (n + 1) * projectiveCount (projectiveZeroLocus f) ((n + 1) * H * B) by
        exact_mod_cast hbound).trans
      exact mul_le_mul_of_nonneg_left
        (htarget.trans (mul_le_mul_of_nonneg_left hpow (by positivity))) (by positivity)
    convert hh using 1
    dsimp [H, T]
    rw [show 3 * (n + 1) + 4 = (n + 1) + 4 + 2 * (n + 1) by omega]
    simp [pow_add]
    ring
  choose Ch hCh hh using fun n => (projective_hypersurface_dimension_growth n).ideal
  let K : ℝ := max T 0 + Cc + Ch (n - 2) + 1
  have hCK : Cc ≤ K := by grind
  have hhK : Ch (n - 2) ≤ K := by grind
  refine ⟨K, by linarith, ?_⟩
  intro I hprime hI d hd hdegree B hB
  have : I.IsPrime := hprime
  -- Each dimension gives a bound with a constant at most `K` and an exponent at most `E`.
  suffices h : ∃ C : ℝ, C ≤ K ∧ ∃ e ≤ E,
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * d ^ e * B ^ ((filteredHilbertPolynomial I).natDegree - 1) by
    obtain ⟨C, hC, e, he, h⟩ := h
    have hd1 : (1 : ℝ) ≤ d := mod_cast (show 1 ≤ d by omega)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (mul_le_mul_of_nonneg_right hC (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hd1 he) (by linarith))
  have hdim := hlt I hprime d hd hdegree
  obtain h0 | h1 | h2 | h3 : (filteredHilbertPolynomial I).natDegree = 0 ∨
      (filteredHilbertPolynomial I).natDegree = 1 ∨
      (filteredHilbertPolynomial I).natDegree = 2 ∨
      3 ≤ (filteredHilbertPolynomial I).natDegree := by omega
  · refine ⟨0, by linarith, 0, Nat.zero_le _, ?_⟩
    simp_all
  · refine ⟨1, (by grind), n + 1, hpoint hn, ?_⟩
    have hbound : projectiveCount (projectiveIdealZeroLocus I) B ≤ d ^ (n + 1) := by
      obtain ⟨a, hint, hi⟩ := exists_integer_linear_normalization_of_le 0 (n + 1)
        (by omega) I d ⟨h1, by simp_all⟩
      let L := (Matrix.map a (Int.castRingHom ℚ)).mulVecLin
      have hLapply (x : Fin (n + 1) → ℚ) (i : Fin 1) :
          L x i = eval x (integerLinearForm (a i)) := by
        simp
        rfl
      have hfinite (z : Fin 1 → ℚ) (s : Finset (Fin (n + 1) → ℚ))
          (hs : ∀ x ∈ s, x ∈ idealZeroLocus I) (hz : ∀ x ∈ s, L x = z) :
          s.card ≤ d ^ (n + 1) := by
        refine (linear_normalization_fiber_card_le I (fun i => integerLinearForm (a i))
          (fun i => linearForm_totalDegree_le _) hi hint d ⟨h1, by simp_all⟩ z s hs
          ?_).trans (Nat.le_self_pow (Nat.succ_ne_zero n) d)
        intro x hx i
        rw [← hLapply, hz x hx]
      let s := projectivePoints (projectiveIdealZeroLocus I) B
      have hs (x) (hx : x ∈ s) : x ∈ projectiveIdealZeroLocus I :=
        (mem_projectivePoints.mp hx).2
      have hnon (x) (hx : x ∈ s) : L x.rep ≠ 0 :=
        projective_linear_image_ne_zero_of_finite_zero_fiber I L (d ^ (n + 1))
          (hfinite 0) x (hs x hx)
      let y : ProjectivePoint 0 :=
        Projectivization.mk ℚ (fun _ => 1) (by tauto)
      apply projective_linear_fiber_card_le I L s hs hnon y _ (d ^ (n + 1)) (hfinite y.rep)
      intro x hx
      change Projectivization.mk ℚ (L x.rep) (hnon x hx) =
        Projectivization.mk ℚ (fun _ => 1) _
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨L x.rep 0, ?_⟩
      funext i
      have hi0 : i = 0 := by grind
      simp [hi0]
    rw [h1, Nat.sub_self, pow_zero, mul_one, one_mul]
    exact_mod_cast hbound
  · refine ⟨Cc, hCK, 3 * (n + 1) + 4, hcurve (by omega), ?_⟩
    rw [h2, show 2 - 1 = 1 from rfl, pow_one]
    exact hc I hprime hI d hd ⟨h2, by grind⟩ B hB
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' h3
  obtain ⟨k, rfl⟩ : ∃ k, n = m + 1 + k + 1 := ⟨n - m - 2, by omega⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- A hypersurface.
    obtain rfl : k = 1 := by omega
    refine ⟨Ch (m + 1), by grind, _, hhyper (by omega), ?_⟩
    rw [hm, show m + 1 + 1 + 1 - 2 = m + 1 by omega]
    exact hh (m + 1) I hprime hI d hd ⟨hm, by grind⟩ B hB
  · -- Codimension at least two: the projection bound.
    have hmk := hT (Set.mem_image_of_mem (fun p => Cp p.1 p.2)
      (show (m + 1, k) ∈ Set.Iic _ ×ˢ Set.Iic _ from
        ⟨Set.mem_Iic.mpr (by omega), Set.mem_Iic.mpr (by omega)⟩))
    refine ⟨Cp (m + 1) k, hmk.trans (by grind), _,
      hproj (m + 1) k rfl (by omega) hk, ?_⟩
    rw [hm]
    exact hp (m + 1) k I hprime hI d hd ⟨hm, by grind⟩ B hB

variable (n : ℕ)

/-- The degree exponent `2n² + 5n - 5` of Theorem 1 in `ℙⁿ`. Its values `2` and `13` for
`n = 1, 2` are the exponents of the zero-dimensional count and of the curve bound. For
`n ≥ 4` it exceeds the projection exponent `2n² + 2n + 6` by `3n - 11`. -/
def projectiveGrowthExponent : ℕ := 2 * n ^ 2 + 5 * n - 5

/-- CCDN Theorem 1 with the degree exponent `2n² + 5n - 5` in every ambient projective
dimension `n`. -/
theorem projective_dimension_growth :
    ProjectiveGrowth n (projectiveGrowthExponent n) := by
  unfold projectiveGrowthExponent
  refine projectiveGrowth_of_le (fun hn => ?_) (fun hn => ?_) (fun hn => ?_)
    fun m k h hm hk => ?_
  · have : 1 ≤ n ^ 2 := by nlinarith
    omega
  · have : 4 ≤ n ^ 2 := by nlinarith
    omega
  · have : 9 ≤ n ^ 2 := by nlinarith
    omega
  · have : projectionDegreeExponent m k ≤ 2 * n ^ 2 + 2 * n + 6 := by subst h; unfold projectionDegreeExponent; nlinarith
    omega

